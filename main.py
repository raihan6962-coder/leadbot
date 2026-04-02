import os, csv, asyncio, tempfile, threading, io, uuid, re, time, json, urllib.parse, random, logging
import requests
import concurrent.futures
import urllib3
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from groq import Groq
from flask import Flask, render_template_string, request, send_file, jsonify
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, MessageHandler,
    filters, ContextTypes, ConversationHandler, CallbackQueryHandler
)

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
load_dotenv()

logging.basicConfig(
    level=logging.INFO,
    format='[%(asctime)s] %(levelname)s — %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("LeadGenPro")

TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
GROQ_API_KEY   = os.getenv("GROQ_API_KEY")

# ════════════════════════════════════════════════════
#   [STOP FEATURE] GLOBAL STOP FLAG
# ════════════════════════════════════════════════════
job_stop_flags: dict = {}

def _should_stop(job_id: str) -> bool:
    flag = job_stop_flags.get(job_id)
    return flag is not None and flag.is_set()

# ════════════════════════════════════════════════════
#   [IP ROTATION FIX] FREE PROXY POOL + ROTATION
#   Fetches fresh proxies from public sources.
#   Falls back to direct connection if all proxies fail.
# ════════════════════════════════════════════════════
_proxy_pool: list = []
_proxy_lock = threading.Lock()
_last_proxy_refresh = 0
_proxy_refresh_interval = 300  # refresh every 5 min

def _fetch_free_proxies() -> list:
    """Fetch fresh proxies from multiple free sources."""
    proxies = []
    sources = [
        "https://api.proxyscrape.com/v2/?request=getproxies&protocol=http&timeout=5000&country=all&ssl=all&anonymity=elite",
        "https://api.proxyscrape.com/v2/?request=getproxies&protocol=http&timeout=5000&country=all&ssl=all&anonymity=anonymous",
        "https://raw.githubusercontent.com/TheSpeedX/PROXY-List/master/http.txt",
        "https://raw.githubusercontent.com/ShiftyTR/Proxy-List/master/http.txt",
        "https://raw.githubusercontent.com/monosans/proxy-list/main/proxies/http.txt",
    ]
    for src in sources:
        try:
            r = requests.get(src, timeout=8, verify=False)
            if r.status_code == 200:
                lines = r.text.strip().split('\n')
                for line in lines:
                    line = line.strip()
                    if ':' in line and len(line) < 30:
                        proxies.append(f"http://{line}")
        except Exception as e:
            logger.debug(f"[PROXY] Source failed {src}: {e}")
    logger.info(f"[PROXY] Fetched {len(proxies)} proxies from all sources")
    return list(set(proxies))

def _get_proxy_pool() -> list:
    """Return current proxy pool, refresh if stale."""
    global _proxy_pool, _last_proxy_refresh
    now = time.time()
    with _proxy_lock:
        if now - _last_proxy_refresh > _proxy_refresh_interval or len(_proxy_pool) == 0:
            logger.info("[PROXY] Refreshing proxy pool...")
            fresh = _fetch_free_proxies()
            if fresh:
                _proxy_pool = fresh
                _last_proxy_refresh = now
                logger.info(f"[PROXY] Pool updated: {len(_proxy_pool)} proxies")
    return list(_proxy_pool)

def _get_random_proxy() -> dict:
    """Pick a random proxy dict for requests, or None for direct."""
    pool = _get_proxy_pool()
    if not pool:
        return None
    p = random.choice(pool)
    return {"http": p, "https": p}

def _test_proxy(proxy_dict: dict, timeout: int = 5) -> bool:
    """Quick test if a proxy works."""
    try:
        r = requests.get(
            "https://httpbin.org/ip",
            proxies=proxy_dict, timeout=timeout, verify=False
        )
        return r.status_code == 200
    except:
        return False

def smart_get(url: str, timeout: int = 15, retries: int = 4, use_proxy: bool = True) -> requests.Response:
    """
    [IP ROTATION FIX] Smart GET with:
    - Rotating free proxies
    - Rotating user-agents
    - Exponential backoff
    - Falls back to direct if all proxies fail
    """
    tried_proxies = set()

    for attempt in range(retries):
        proxy = None
        if use_proxy:
            pool = _get_proxy_pool()
            available = [p for p in pool if p not in tried_proxies]
            if available:
                p_str = random.choice(available)
                tried_proxies.add(p_str)
                proxy = {"http": p_str, "https": p_str}

        headers = get_headers()
        try:
            resp = requests.get(
                url,
                headers=headers,
                proxies=proxy,
                timeout=timeout,
                verify=False,
                allow_redirects=True
            )
            if resp.status_code == 200:
                return resp
            elif resp.status_code in (429, 403):
                logger.warning(f"[SMART-GET] {resp.status_code} on attempt {attempt+1} — rotating")
                wait = (2 ** attempt) + random.uniform(0.5, 2)
                time.sleep(wait)
                continue
            else:
                return resp
        except Exception as e:
            logger.debug(f"[SMART-GET] Attempt {attempt+1} failed proxy={proxy}: {e}")
            wait = (2 ** attempt) * 0.5
            time.sleep(wait)

    # Final fallback: direct connection no proxy
    try:
        logger.info("[SMART-GET] All proxies failed — trying direct connection")
        return requests.get(url, headers=get_headers(), timeout=timeout, verify=False, allow_redirects=True)
    except Exception as e:
        logger.error(f"[SMART-GET] Direct also failed: {e}")
        raise

# ════════════════════════════════════════════════════
#   ROTATING HEADERS
# ════════════════════════════════════════════════════
HEADERS_POOL = [
    {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
        "Accept-Language": "en-US,en;q=0.9",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
        "Referer": "https://www.google.com/",
        "sec-ch-ua": '"Chromium";v="122", "Not(A:Brand";v="24", "Google Chrome";v="122"',
        "sec-ch-ua-mobile": "?0",
        "sec-ch-ua-platform": '"Windows"',
        "sec-fetch-dest": "document",
        "sec-fetch-mode": "navigate",
        "sec-fetch-site": "same-origin",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
    },
    {
        "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36",
        "Accept-Language": "en-GB,en;q=0.9",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Referer": "https://www.google.com/",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
    },
    {
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:123.0) Gecko/20100101 Firefox/123.0",
        "Accept-Language": "en-US,en;q=0.5",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/avif,image/webp,*/*;q=0.8",
        "Referer": "https://www.google.com/",
        "DNT": "1",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
    },
    {
        "User-Agent": "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
        "Accept-Language": "en-US,en;q=0.8",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Referer": "https://www.bing.com/",
        "Connection": "keep-alive",
    },
    {
        "User-Agent": "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
        "Accept-Language": "en-US,en;q=0.9",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8",
        "Referer": "https://www.google.com/",
        "Connection": "keep-alive",
    },
]

def get_headers():
    return random.choice(HEADERS_POOL).copy()


# ════════════════════════════════════════════════════
#   GOOGLE SHEETS DB WRAPPER
# ════════════════════════════════════════════════════
class GoogleSheetsDB:
    def __init__(self, webhook_url):
        self.url = webhook_url

    def _post_async(self, payload):
        try:
            requests.post(self.url, json=payload, timeout=15)
        except Exception as e:
            logger.debug(f"[DB] Post failed silently: {e}")

    def send_action(self, action, data):
        if not self.url:
            return
        payload = {"action": action, "data": data}
        threading.Thread(target=self._post_async, args=(payload,), daemon=True).start()

    def log(self, action, details):
        self.send_action("log", {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "action": action,
            "details": str(details),
        })


# ════════════════════════════════════════════════════
#   DEDUPLICATION STORE
#   [PROBLEM 5 FIX] Enhanced to prevent duplicate
#   qualified leads before saving to sheet.
# ════════════════════════════════════════════════════
class DeduplicationStore:
    def __init__(self):
        self._lock = threading.Lock()
        self._names:    set = set()
        self._websites: set = set()
        self._emails:   set = set()
        self._total_skipped = 0

    def _norm(self, val: str) -> str:
        if not val or val == "N/A":
            return ""
        return re.sub(r'\s+', ' ', val.strip().lower())

    def _norm_url(self, url: str) -> str:
        if not url or url == "N/A":
            return ""
        try:
            parsed = urllib.parse.urlparse(url.lower().strip())
            host = parsed.netloc.replace("www.", "")
            return host + parsed.path.rstrip("/")
        except:
            return url.lower().strip()

    def is_duplicate(self, name: str, website: str, email: str) -> bool:
        nn = self._norm(name)
        nw = self._norm_url(website)
        ne = self._norm(email)
        with self._lock:
            if ne and ne in self._emails:   return True   # email primary
            if nw and nw in self._websites: return True   # website secondary
            if nn and nn in self._names:    return True   # name fallback
        return False

    def register(self, name: str, website: str, email: str):
        nn = self._norm(name)
        nw = self._norm_url(website)
        ne = self._norm(email)
        with self._lock:
            if nn: self._names.add(nn)
            if nw: self._websites.add(nw)
            if ne: self._emails.add(ne)

    def mark_skipped(self):
        with self._lock:
            self._total_skipped += 1

    @property
    def skipped(self):
        with self._lock:
            return self._total_skipped


# ════════════════════════════════════════════════════
#   ADVANCED KEYWORD ENGINE
#   [PROBLEM 2 FIX] generate_one() method added —
#   returns exactly ONE new keyword per call.
# ════════════════════════════════════════════════════
class AdvancedKeywordEngine:
    COMMERCIAL_PREFIXES = [
        "best", "top", "affordable", "cheap", "local", "professional",
        "experienced", "certified", "trusted", "rated", "licensed",
        "expert", "reliable", "fast", "emergency", "24 hour", "same day",
        "family", "luxury", "premium", "budget", "high quality",
    ]
    COMMERCIAL_SUFFIXES = [
        "services", "company", "agency", "near me", "in my area",
        "specialist", "experts", "professionals", "contractor", "provider",
        "consultant", "firm", "studio", "clinic", "center", "shop",
        "office", "team", "solutions", "group",
    ]
    INTENT_MODIFIERS = [
        "hire", "find", "looking for", "need",
        "best rated", "top rated", "highly reviewed", "award winning",
        "recommended", "free quote", "free estimate", "low cost",
        "pricing", "reviews", "bad reviews", "poor service",
        "negative reviews", "problems with",
    ]
    NICHE_MODIFIERS = {
        "restaurant": ["takeout", "delivery", "dine in", "catering", "buffet"],
        "dentist":    ["dental clinic", "teeth whitening", "orthodontist", "braces", "dental implants"],
        "lawyer":     ["attorney", "law firm", "legal services", "counsel", "litigation"],
        "plumber":    ["plumbing", "pipe repair", "drain cleaning", "water heater", "leak fix"],
        "realtor":    ["real estate agent", "property dealer", "home buyer", "home seller", "property management"],
        "gym":        ["fitness center", "workout", "personal trainer", "crossfit", "yoga studio"],
        "salon":      ["hair salon", "beauty salon", "spa", "barber shop", "nail salon"],
        "doctor":     ["physician", "medical clinic", "urgent care", "specialist", "general practitioner"],
    }

    def __init__(self):
        self._expanded_pool: list = []
        self._pool_index: int = 0
        self._used: set = set()

    def _build_static_pool(self, base_kw: str) -> list:
        results = []
        for prefix in self.COMMERCIAL_PREFIXES:
            results.append(f"{prefix} {base_kw}")
        for suffix in self.COMMERCIAL_SUFFIXES:
            results.append(f"{base_kw} {suffix}")
        for modifier in self.INTENT_MODIFIERS:
            results.append(f"{modifier} {base_kw}")
        base_lower = base_kw.lower()
        for niche_key, mods in self.NICHE_MODIFIERS.items():
            if niche_key in base_lower:
                for mod in mods:
                    results.append(mod)
                    for prefix in self.COMMERCIAL_PREFIXES[:5]:
                        results.append(f"{prefix} {mod}")
        random.shuffle(results)
        return results

    def _google_autosuggest(self, keyword: str, location: str) -> list:
        results = []
        try:
            url = f"https://suggestqueries.google.com/complete/search?client=firefox&q={urllib.parse.quote_plus(keyword + ' ' + location)}"
            r = requests.get(url, headers=get_headers(), timeout=6)
            data = r.json()
            if isinstance(data, list) and len(data) > 1:
                for suggestion in data[1]:
                    results.append(suggestion.strip())
        except Exception as e:
            logger.debug(f"[KEYWORDS] Autosuggest failed: {e}")
        return results

    def _ai_generate_one(self, base_kw: str, location: str) -> str:
        """Ask AI for a single new keyword variation."""
        if not GROQ_API_KEY:
            return None
        try:
            client = Groq(api_key=GROQ_API_KEY)
            prompt = (
                f'Seed keyword: "{base_kw}". Location: "{location}". '
                f'Already used: {list(self._used)[:15]}. '
                f'Give me EXACTLY ONE new Google search term for this local business type. '
                f'Return ONLY the search term, nothing else, no punctuation.'
            )
            res = client.chat.completions.create(
                messages=[{"role": "user", "content": prompt}],
                model="llama3-8b-8192",
                temperature=0.9,
                max_tokens=30,
            )
            kw = res.choices[0].message.content.strip().strip('"').strip("'")
            if kw and len(kw) > 3 and kw.lower() not in self._used:
                return kw
        except Exception as e:
            logger.debug(f"[KEYWORDS] AI single-gen failed: {e}")
        return None

    def generate_one(self, base_kw: str, location: str) -> str:
        """
        [PROBLEM 2 FIX] Returns EXACTLY ONE new unused keyword.
        Priority: static pool → autosuggest → AI
        """
        # Build static pool on first call
        if not self._expanded_pool:
            self._expanded_pool = self._build_static_pool(base_kw)
            logger.info(f"[KEYWORDS] Built static pool: {len(self._expanded_pool)} keywords")

        # Try static pool first
        while self._pool_index < len(self._expanded_pool):
            kw = self._expanded_pool[self._pool_index]
            self._pool_index += 1
            if kw.lower() not in self._used and len(kw) > 3:
                self._used.add(kw.lower())
                logger.info(f"[KEYWORDS] → Next keyword (static): '{kw}'")
                return kw

        # Try autosuggest
        suggestions = self._google_autosuggest(base_kw, location)
        for kw in suggestions:
            if kw.lower() not in self._used and len(kw) > 3:
                self._used.add(kw.lower())
                logger.info(f"[KEYWORDS] → Next keyword (autosuggest): '{kw}'")
                return kw

        # Try AI
        ai_kw = self._ai_generate_one(base_kw, location)
        if ai_kw:
            self._used.add(ai_kw.lower())
            logger.info(f"[KEYWORDS] → Next keyword (AI): '{ai_kw}'")
            return ai_kw

        # Final fallback: append counter
        fallback = f"{base_kw} {random.choice(self.COMMERCIAL_SUFFIXES)}"
        self._used.add(fallback.lower())
        logger.info(f"[KEYWORDS] → Next keyword (fallback): '{fallback}'")
        return fallback

    def mark_used(self, kw: str):
        self._used.add(kw.lower())


# ════════════════════════════════════════════════════
#   [PROBLEM 1 FIX] AGGRESSIVE WEBSITE FINDER
#   4-step extraction with Google Maps deep scrape,
#   business detail page, and Google search fallback.
# ════════════════════════════════════════════════════
class WebsiteFinder:
    BLACKLIST = (
        'google.com', 'google.co', 'maps.google', 'goo.gl',
        'facebook.com', 'instagram.com', 'twitter.com', 'x.com',
        'yelp.com', 'tripadvisor.com', 'yellowpages.com',
        'bbb.org', 'linkedin.com', 'youtube.com', 'foursquare.com',
        'mapquest.com', 'apple.com/maps', 'bing.com/maps',
    )

    def _is_valid_website(self, url: str) -> bool:
        """Must be a real business domain, not aggregator/map links."""
        if not url or url == "N/A":
            return False
        url_lower = url.lower()
        if any(b in url_lower for b in self.BLACKLIST):
            return False
        return url_lower.startswith('http') and '.' in url_lower

    def _extract_from_maps_listing_html(self, html: str) -> str:
        """Step 1: Extract website from Maps listing page HTML."""
        soup = BeautifulSoup(html, 'html.parser')

        # Pattern 1: data-url attributes on website buttons
        for el in soup.find_all(attrs={"data-url": True}):
            url = el.get("data-url", "")
            if self._is_valid_website(url):
                return url

        # Pattern 2: aria-label="Website" links
        for a in soup.find_all('a', href=True):
            label = (a.get('aria-label') or '').lower()
            if 'website' in label or 'web site' in label:
                href = a['href']
                if self._is_valid_website(href):
                    return href

        # Pattern 3: JSON embedded in page (Google Maps data blobs)
        # Look for "website":"..." patterns
        website_match = re.search(r'"website"\s*:\s*"(https?://[^"]+)"', html)
        if website_match:
            url = website_match.group(1)
            if self._is_valid_website(url):
                return url

        # Pattern 4: /url?q= redirects in the page
        for a in soup.find_all('a', href=True):
            href = a['href']
            if '/url?q=' in href:
                clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                if self._is_valid_website(clean):
                    return clean

        # Pattern 5: Scan all outbound links
        for a in soup.find_all('a', href=True):
            href = a['href']
            if href.startswith('http') and self._is_valid_website(href):
                return href

        return "N/A"

    def _fetch_maps_detail_page(self, maps_url: str) -> str:
        """Step 2: Open the business detail page on Google Maps."""
        if not maps_url or maps_url == "N/A":
            return "N/A"
        try:
            resp = smart_get(maps_url, timeout=12)
            if resp and resp.status_code == 200:
                result = self._extract_from_maps_listing_html(resp.text)
                if result != "N/A":
                    logger.debug(f"[WEBSITE] Found via Maps detail page: {result}")
                    return result
        except Exception as e:
            logger.debug(f"[WEBSITE] Maps detail page failed: {e}")
        return "N/A"

    def _search_google(self, business_name: str, location: str) -> str:
        """Step 3: Google search for official website."""
        queries = [
            f'"{business_name}" {location} official website',
            f'{business_name} {location} site',
            f'{business_name} {location}',
        ]
        for query in queries:
            try:
                url = f"https://www.google.com/search?q={urllib.parse.quote_plus(query)}&num=5&hl=en"
                resp = smart_get(url, timeout=10)
                if resp and resp.status_code == 200:
                    soup = BeautifulSoup(resp.text, 'html.parser')
                    for a in soup.select('a[href]'):
                        href = a.get('href', '')
                        if '/url?q=' in href:
                            clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                            if self._is_valid_website(clean):
                                logger.debug(f"[WEBSITE] Found via Google search: {clean}")
                                return clean
                time.sleep(random.uniform(0.5, 1.5))
            except Exception as e:
                logger.debug(f"[WEBSITE] Google search failed for '{business_name}': {e}")
        return "N/A"

    def _search_bing(self, business_name: str, location: str) -> str:
        """Extra fallback: Bing search."""
        try:
            query = urllib.parse.quote_plus(f"{business_name} {location} website")
            url = f"https://www.bing.com/search?q={query}"
            resp = smart_get(url, timeout=10)
            if resp and resp.status_code == 200:
                soup = BeautifulSoup(resp.text, 'html.parser')
                for a in soup.select('cite, .b_attribution'):
                    text = a.get_text(strip=True)
                    if text.startswith('http') and self._is_valid_website(text):
                        return text
                for a in soup.select('a[href]'):
                    href = a.get('href', '')
                    if href.startswith('http') and self._is_valid_website(href):
                        return href
        except Exception as e:
            logger.debug(f"[WEBSITE] Bing search failed: {e}")
        return "N/A"

    def _search_duckduckgo(self, business_name: str, location: str) -> str:
        """Extra fallback: DuckDuckGo."""
        try:
            query = urllib.parse.quote_plus(f"{business_name} {location} official site")
            url = f"https://html.duckduckgo.com/html/?q={query}"
            resp = smart_get(url, timeout=10)
            if resp and resp.status_code == 200:
                soup = BeautifulSoup(resp.text, 'html.parser')
                for a in soup.select('a.result__url, .result__url'):
                    href = a.get('href', '') or a.get_text(strip=True)
                    if not href.startswith('http'):
                        href = 'https://' + href
                    if self._is_valid_website(href):
                        return href
                for item in soup.select('.result__body, .result'):
                    for a in item.select('a[href]'):
                        href = a.get('href', '')
                        if href.startswith('http') and self._is_valid_website(href):
                            return href
        except Exception as e:
            logger.debug(f"[WEBSITE] DuckDuckGo search failed: {e}")
        return "N/A"

    def find(self, business_name: str, location: str,
             website_from_listing: str = "N/A",
             maps_url: str = "N/A") -> str:
        """
        [PROBLEM 1 FIX] 4-step aggressive website finder.
        Step 1: Use website already found in listing
        Step 2: Fetch Maps detail page
        Step 3: Google search
        Step 4: Bing / DuckDuckGo fallback
        """
        # Step 1: Already have it from listing
        if self._is_valid_website(website_from_listing):
            logger.debug(f"[WEBSITE] ✅ Step 1 (listing): {website_from_listing}")
            return website_from_listing

        logger.info(f"[WEBSITE] No website in listing for '{business_name}' — searching...")

        # Step 2: Maps detail page deep scrape
        if maps_url and maps_url != "N/A":
            result = self._fetch_maps_detail_page(maps_url)
            if result != "N/A":
                logger.info(f"[WEBSITE] ✅ Step 2 (Maps detail): {result}")
                return result

        # Step 3: Google search
        result = self._search_google(business_name, location)
        if result != "N/A":
            logger.info(f"[WEBSITE] ✅ Step 3 (Google): {result}")
            return result

        # Step 4a: Bing
        result = self._search_bing(business_name, location)
        if result != "N/A":
            logger.info(f"[WEBSITE] ✅ Step 4a (Bing): {result}")
            return result

        # Step 4b: DuckDuckGo
        result = self._search_duckduckgo(business_name, location)
        if result != "N/A":
            logger.info(f"[WEBSITE] ✅ Step 4b (DDG): {result}")
            return result

        logger.info(f"[WEBSITE] ❌ All steps failed for '{business_name}'")
        return "N/A"


# ════════════════════════════════════════════════════
#   GOOGLE MAPS SCRAPER — IMPROVED
#   [PROBLEM 4 FIX] Maps URL now extracted and stored.
# ════════════════════════════════════════════════════
class GoogleMapsScraper:
    MAX_RETRIES = 3
    RETRY_DELAY = 2

    def _scrape_google_maps(self, keyword: str, location: str) -> list:
        results = []
        query = urllib.parse.quote_plus(f"{keyword} {location}")
        url = f"https://www.google.com/maps/search/{query}/"

        for attempt in range(1, self.MAX_RETRIES + 1):
            try:
                logger.info(f"[SCRAPE-MAPS] Attempt {attempt}: {url}")
                resp = smart_get(url, timeout=15)
                logger.info(f"[SCRAPE-MAPS] HTTP {resp.status_code} | len={len(resp.text)}")

                if resp.status_code != 200:
                    time.sleep(self.RETRY_DELAY * attempt)
                    continue

                html = resp.text
                businesses = self._parse_maps_html(html, keyword, location)
                if businesses:
                    logger.info(f"[SCRAPE-MAPS] Parsed {len(businesses)} businesses (JSON method)")
                    return businesses

                businesses = self._parse_maps_html_elements(html, keyword, location)
                if businesses:
                    logger.info(f"[SCRAPE-MAPS] Parsed {len(businesses)} businesses (elements method)")
                    return businesses

                logger.warning(f"[SCRAPE-MAPS] Attempt {attempt}: zero results, retrying...")
                time.sleep(self.RETRY_DELAY * attempt)

            except Exception as e:
                logger.warning(f"[SCRAPE-MAPS] Error attempt={attempt}: {e}")
                time.sleep(self.RETRY_DELAY * attempt)

        return results

    def _build_maps_url(self, name: str, location: str, cid: str = "") -> str:
        """[PROBLEM 4 FIX] Build a direct Google Maps URL for the business."""
        if cid:
            return f"https://www.google.com/maps/place/?q=place_id:{cid}"
        return f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/"

    def _parse_maps_html(self, html: str, keyword: str, location: str) -> list:
        results = []
        seen_names = set()

        # Method 1: JSON-LD
        try:
            soup = BeautifulSoup(html, 'html.parser')
            for script in soup.find_all('script', type='application/ld+json'):
                try:
                    data = json.loads(script.string or '')
                    items = data if isinstance(data, list) else [data]
                    for item in items:
                        if item.get('@type') in (
                            'LocalBusiness', 'Restaurant', 'Store',
                            'MedicalBusiness', 'LegalService', 'HomeAndConstructionBusiness',
                            'HealthAndBeautyBusiness', 'FoodEstablishment'
                        ):
                            name = item.get('name', 'N/A')
                            if not name or name in seen_names:
                                continue
                            seen_names.add(name)
                            maps_url = item.get('hasMap', '') or self._build_maps_url(name, location)
                            results.append({
                                "Name":        name,
                                "Phone":       item.get('telephone', 'N/A') or 'N/A',
                                "Website":     item.get('url', 'N/A') or 'N/A',
                                "Rating":      str(item.get('aggregateRating', {}).get('ratingValue', 'N/A')),
                                "ReviewCount": str(item.get('aggregateRating', {}).get('reviewCount', '0')),
                                "Address":     item.get('address', {}).get('streetAddress', location) if isinstance(item.get('address'), dict) else location,
                                "Category":    keyword,
                                # [PROBLEM 4] Maps URL stored
                                "Maps_URL":    maps_url,
                            })
                except:
                    pass
        except Exception as e:
            logger.debug(f"[PARSE] JSON-LD error: {e}")

        if results:
            return results

        # Method 2: Regex on embedded JS
        try:
            name_pattern = re.findall(r'"([A-Z][^"]{2,60})"[^"]*?"([1-5]\.[0-9])"', html)
            for name, rating in name_pattern[:50]:
                name = name.strip()
                if len(name) < 3 or name in seen_names or any(c in name for c in ['\\', '/', '{', '}', '=', '<', '>']):
                    continue
                seen_names.add(name)
                results.append({
                    "Name":        name,
                    "Phone":       "N/A",
                    "Website":     "N/A",
                    "Rating":      rating,
                    "ReviewCount": "0",
                    "Address":     location,
                    "Category":    keyword,
                    "Maps_URL":    self._build_maps_url(name, location),
                })
        except Exception as e:
            logger.debug(f"[PARSE] Regex error: {e}")

        return results

    def _parse_maps_html_elements(self, html: str, keyword: str, location: str) -> list:
        results = []
        seen_names = set()
        soup = BeautifulSoup(html, 'html.parser')

        ITEM_SELECTORS = [
            'div[role="article"]',
            'div[aria-label][role="region"]',
            'a[aria-label][href*="maps"]',
            'div.Nv2PK',
            'div.bfdHYd',
            'div[jsaction*="mouseover"]',
        ]

        blocks = []
        for sel in ITEM_SELECTORS:
            found = soup.select(sel)
            if found:
                blocks = found
                logger.info(f"[PARSE-EL] Selector '{sel}' → {len(found)} blocks")
                break

        for block in blocks[:30]:
            try:
                text = block.get_text(separator=' ', strip=True)
                name = "N/A"
                aria = block.get('aria-label', '')
                if aria and 2 < len(aria) < 100:
                    name = aria.strip()
                if name == "N/A":
                    h = block.select_one('[role="heading"], h3, h2, .fontHeadlineSmall')
                    if h:
                        name = h.get_text(strip=True)
                if name == "N/A" or len(name) < 3 or name in seen_names:
                    continue
                seen_names.add(name)

                rating = "N/A"
                rm = re.search(r'\b([1-5][.,]\d)\b', text)
                if rm:
                    rv = rm.group(1).replace(',', '.')
                    try:
                        if 1.0 <= float(rv) <= 5.0:
                            rating = rv
                    except:
                        pass

                review_count = "0"
                rc = re.search(r'\((\d{1,6})\)', text)
                if rc:
                    review_count = rc.group(1)

                phone = "N/A"
                ph = re.search(r'(\+?1?\s*\(?\d{3}\)?[\s.\-]\d{3}[\s.\-]\d{4})', text)
                if ph:
                    phone = ph.group(0).strip()

                website = "N/A"
                maps_link_href = "N/A"
                for a in block.select('a[href]'):
                    href = a.get('href', '')
                    if 'maps.google' in href or '/maps/' in href:
                        maps_link_href = href
                    elif '/url?q=' in href:
                        clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                        if clean.startswith('http') and 'google' not in clean.lower():
                            website = clean
                    elif href.startswith('http') and 'google' not in href.lower():
                        website = href

                results.append({
                    "Name":        name,
                    "Phone":       phone,
                    "Website":     website,
                    "Rating":      rating,
                    "ReviewCount": review_count,
                    "Address":     location,
                    "Category":    keyword,
                    "Maps_URL":    maps_link_href if maps_link_href != "N/A" else self._build_maps_url(name, location),
                })
            except Exception as e:
                logger.debug(f"[PARSE-EL] Block error: {e}")

        return results

    def _scrape_google_local(self, keyword: str, location: str) -> list:
        query = urllib.parse.quote_plus(f"{keyword} {location}")
        all_results = []

        def fetch_one_offset(start: int) -> list:
            url = f"https://www.google.com/search?q={query}&tbm=lcl&start={start}&num=20&hl=en&gl=us"
            for attempt in range(1, self.MAX_RETRIES + 1):
                try:
                    resp = smart_get(url, timeout=12)
                    logger.info(f"[SCRAPE-LCL] offset={start} HTTP {resp.status_code}")
                    if resp.status_code != 200:
                        time.sleep(self.RETRY_DELAY * attempt)
                        continue

                    soup = BeautifulSoup(resp.text, 'html.parser')
                    blocks = soup.select(
                        'div.VkpGBb, div.rllt__details, div.uMdZh, div.cXedhc, '
                        'div.lqhpac, div[data-cid], div.rl_tit, li.rllt__list-item, '
                        'div[class*="rllt"]'
                    )
                    logger.info(f"[SCRAPE-LCL] offset={start} → {len(blocks)} blocks")

                    batch = []
                    for block in blocks:
                        text = block.get_text(separator=' ', strip=True)
                        name_el = block.select_one(
                            'div[role="heading"], .dbg0pd, span.OSrXXb, '
                            '.rllt__details div:first-child, [class*="tit"], '
                            'div.rllt__details > div:first-child'
                        )
                        name = name_el.get_text(strip=True) if name_el else "N/A"
                        if name == "N/A" or len(name) < 3:
                            for el in block.children:
                                txt = el.get_text(strip=True) if hasattr(el, 'get_text') else ''
                                if 3 < len(txt) < 80:
                                    name = txt
                                    break
                        if name == "N/A" or len(name) < 3:
                            continue

                        rating = "N/A"
                        rm = re.search(r'\b([1-5][.,]\d)\b', text)
                        if rm:
                            rv = rm.group(1).replace(',', '.')
                            try:
                                if 1.0 <= float(rv) <= 5.0:
                                    rating = rv
                            except: pass

                        review_count = "0"
                        rc = re.search(r'\((\d{1,6})\)', text)
                        if rc:
                            review_count = rc.group(1)

                        phone = "N/A"
                        ph = re.search(r'(\+?1?\s*\(?\d{3}\)?[\s.\-]\d{3}[\s.\-]\d{4})', text)
                        if ph:
                            phone = ph.group(0).strip()

                        website = "N/A"
                        maps_href = "N/A"
                        for a in block.select('a[href]'):
                            href = a.get('href', '')
                            if 'maps.google' in href or '/maps/' in href:
                                maps_href = href
                            elif '/url?q=' in href:
                                clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                                if clean.startswith('http') and 'google' not in clean.lower():
                                    website = clean
                            elif href.startswith('http') and 'google' not in href.lower():
                                website = href

                        # Also check data-cid for Maps URL
                        cid = block.get('data-cid', '')
                        maps_url = self._build_maps_url(name, location, cid) if cid else (
                            maps_href if maps_href != "N/A" else self._build_maps_url(name, location)
                        )

                        batch.append({
                            "Name":        name,
                            "Phone":       phone,
                            "Website":     website,
                            "Rating":      rating,
                            "ReviewCount": review_count,
                            "Address":     location,
                            "Category":    keyword,
                            "Maps_URL":    maps_url,
                        })

                    logger.info(f"[SCRAPE-LCL] offset={start} → {len(batch)} parsed")
                    return batch

                except Exception as e:
                    logger.warning(f"[SCRAPE-LCL] offset={start} attempt={attempt}: {e}")
                    time.sleep(self.RETRY_DELAY * attempt)
            return []

        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
            futures = {ex.submit(fetch_one_offset, s): s for s in [0, 20, 40]}
            for f in concurrent.futures.as_completed(futures):
                try:
                    all_results.extend(f.result())
                except Exception as e:
                    logger.error(f"[SCRAPE-LCL] Thread error: {e}")

        return all_results

    def _scrape_duckduckgo(self, keyword: str, location: str) -> list:
        results = []
        seen = set()
        query = urllib.parse.quote_plus(f"{keyword} {location}")
        url = f"https://html.duckduckgo.com/html/?q={query}"

        try:
            resp = smart_get(url, timeout=12)
            logger.info(f"[SCRAPE-DDG] HTTP {resp.status_code}")
            if resp.status_code != 200:
                return results

            soup = BeautifulSoup(resp.text, 'html.parser')
            result_items = soup.select('.result, .results_links, div.result__body')
            logger.info(f"[SCRAPE-DDG] {len(result_items)} result blocks")

            for item in result_items[:20]:
                try:
                    title_el = item.select_one('.result__title, a.result__a, h2')
                    if not title_el:
                        continue
                    name = title_el.get_text(strip=True)
                    if len(name) < 3 or name in seen:
                        continue
                    seen.add(name)

                    website = "N/A"
                    link_el = item.select_one('a.result__url, .result__url')
                    if link_el:
                        href = link_el.get('href', '') or link_el.get_text(strip=True)
                        if href and not href.startswith('http'):
                            href = 'https://' + href
                        if href.startswith('http'):
                            website = href

                    snippet = item.get_text(separator=' ', strip=True)
                    rating = "N/A"
                    rm = re.search(r'\b([1-5][.,]\d)\b', snippet)
                    if rm:
                        rv = rm.group(1).replace(',', '.')
                        try:
                            if 1.0 <= float(rv) <= 5.0:
                                rating = rv
                        except: pass

                    results.append({
                        "Name":        name,
                        "Phone":       "N/A",
                        "Website":     website,
                        "Rating":      rating,
                        "ReviewCount": "0",
                        "Address":     location,
                        "Category":    keyword,
                        "Maps_URL":    self._build_maps_url(name, location),
                    })
                except Exception as e:
                    logger.debug(f"[SCRAPE-DDG] Item error: {e}")

        except Exception as e:
            logger.warning(f"[SCRAPE-DDG] Error: {e}")

        logger.info(f"[SCRAPE-DDG] Extracted {len(results)} businesses")
        return results

    def _scrape_bing_places(self, keyword: str, location: str) -> list:
        """
        [IP ROTATION FIX] Additional source: Bing Maps/Places search.
        Gives different results when Google blocks.
        """
        results = []
        seen = set()
        query = urllib.parse.quote_plus(f"{keyword} near {location}")
        url = f"https://www.bing.com/search?q={query}&filters=local_oof%3A1"

        try:
            resp = smart_get(url, timeout=12)
            if resp.status_code != 200:
                return results
            soup = BeautifulSoup(resp.text, 'html.parser')

            # Bing local pack cards
            for card in soup.select('.b_sideBleed, .b_entityTP, .b_lclcard, [data-bm]'):
                try:
                    name_el = card.select_one('h2, .b_title, .b_entityTitle, a')
                    if not name_el:
                        continue
                    name = name_el.get_text(strip=True)
                    if len(name) < 3 or name in seen:
                        continue
                    seen.add(name)

                    text = card.get_text(separator=' ', strip=True)
                    rating = "N/A"
                    rm = re.search(r'\b([1-5][.,]\d)\b', text)
                    if rm:
                        rv = rm.group(1).replace(',', '.')
                        try:
                            if 1.0 <= float(rv) <= 5.0:
                                rating = rv
                        except: pass

                    phone = "N/A"
                    ph = re.search(r'(\+?1?\s*\(?\d{3}\)?[\s.\-]\d{3}[\s.\-]\d{4})', text)
                    if ph:
                        phone = ph.group(0).strip()

                    website = "N/A"
                    for a in card.select('a[href]'):
                        href = a.get('href', '')
                        if href.startswith('http') and 'bing.com' not in href.lower() and 'microsoft' not in href.lower():
                            website = href
                            break

                    results.append({
                        "Name":        name,
                        "Phone":       phone,
                        "Website":     website,
                        "Rating":      rating,
                        "ReviewCount": "0",
                        "Address":     location,
                        "Category":    keyword,
                        "Maps_URL":    self._build_maps_url(name, location),
                    })
                except:
                    pass
        except Exception as e:
            logger.debug(f"[SCRAPE-BING] Error: {e}")

        logger.info(f"[SCRAPE-BING] Extracted {len(results)} businesses")
        return results

    def fetch_batch(self, keyword: str, location: str) -> list:
        """
        Multi-strategy scrape with dedup and bad-rating-first sort.
        [IP ROTATION FIX] Uses smart_get with proxy rotation throughout.
        """
        logger.info(f"[SCRAPE] ═══ Keyword: '{keyword}' in '{location}' ═══")
        all_leads = []

        # Strategy A: Google Maps page
        maps_results = self._scrape_google_maps(keyword, location)
        logger.info(f"[SCRAPE] A (Maps): {len(maps_results)}")
        all_leads.extend(maps_results)

        # Strategy B: Google Local (tbm=lcl)
        local_results = self._scrape_google_local(keyword, location)
        logger.info(f"[SCRAPE] B (Local): {len(local_results)}")
        all_leads.extend(local_results)

        # Strategy C: DuckDuckGo (if Google gave < 3)
        if len(all_leads) < 3:
            ddg_results = self._scrape_duckduckgo(keyword, location)
            logger.info(f"[SCRAPE] C (DDG): {len(ddg_results)}")
            all_leads.extend(ddg_results)

        # Strategy D: Bing Places (if still low)
        if len(all_leads) < 3:
            bing_results = self._scrape_bing_places(keyword, location)
            logger.info(f"[SCRAPE] D (Bing): {len(bing_results)}")
            all_leads.extend(bing_results)

        # Dedup by name within batch
        seen_names = set()
        unique_leads = []
        for lead in all_leads:
            key = lead["Name"].strip().lower()
            if key not in seen_names and key != "n/a" and len(key) > 2:
                seen_names.add(key)
                unique_leads.append(lead)

        # Sort: worst rating first
        def sort_key(lead):
            try:
                return float(lead["Rating"])
            except:
                return 6.0

        unique_leads.sort(key=sort_key)
        logger.info(f"[SCRAPE] ✅ Total unique for '{keyword}': {len(unique_leads)}")
        return unique_leads


# ════════════════════════════════════════════════════
#   DEEP EMAIL EXTRACTOR (UNCHANGED — PRESERVED)
# ════════════════════════════════════════════════════
class DeepEmailExtractor:
    def __init__(self):
        self.email_regex = r'[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}'
        self.bad_keywords = [
            'example', 'domain', 'sentry', '@2x', '.png', '.jpg',
            '.jpeg', '.gif', 'wixpress', 'bootstrap', 'rating',
            'schema', 'jquery', 'cloudflare', 'wordpress', 'email@email',
            'youremail', 'name@', 'user@', 'test@', 'info@info',
        ]
        self.CONTACT_PATHS = [
            '/contact', '/contact-us', '/contactus',
            '/about', '/about-us', '/aboutus',
            '/support', '/help', '/info', '/reach-us',
            '/get-in-touch', '/getintouch',
        ]

    def is_valid_email(self, email: str) -> bool:
        email = email.lower()
        if len(email) > 80 or '.' not in email.split('@')[-1]:
            return False
        return not any(bad in email for bad in self.bad_keywords)

    def extract_from_html(self, html: str) -> list:
        emails = set()
        emails.update(re.findall(self.email_regex, html))
        for ob in re.findall(
            r'[a-zA-Z0-9._%+\-]+\s*[\[\(]at[\]\)]\s*[a-zA-Z0-9.\-]+\s*[\[\(]dot[\]\)]\s*[a-zA-Z]{2,}',
            html, re.IGNORECASE
        ):
            cleaned = (ob.replace('[at]', '@').replace('(at)', '@')
                         .replace('[dot]', '.').replace('(dot)', '.').replace(' ', ''))
            if '@' in cleaned:
                emails.add(cleaned.lower())
        emails.update(re.findall(
            r'mailto:([a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,})', html
        ))
        return [e for e in emails if self.is_valid_email(e)]

    def crawl_page(self, url: str, timeout: int = 10) -> str:
        """[IP ROTATION FIX] Uses smart_get for proxy rotation."""
        try:
            r = smart_get(url, timeout=timeout)
            if r and r.status_code == 200:
                return r.text
        except Exception as e:
            logger.debug(f"[EMAIL] Crawl failed for {url}: {e}")
        return ""

    def get_internal_links(self, html: str, base_url: str) -> list:
        soup = BeautifulSoup(html, 'html.parser')
        CONTACT_KEYWORDS = ['contact', 'about', 'support', 'help', 'reach',
                            'connect', 'get-in-touch', 'getintouch', 'info', 'team']
        links = []
        for a in soup.select('a[href]'):
            href = a.get('href', '').lower()
            if any(kw in href for kw in CONTACT_KEYWORDS):
                full_link = urllib.parse.urljoin(base_url, a['href'])
                if full_link.startswith('http'):
                    links.append(full_link)
        return list(set(links))

    def get_email(self, url: str) -> str:
        if not url or url == "N/A":
            return "N/A"
        if not url.startswith('http'):
            url = 'https://' + url
        visited = set()
        base = url.rstrip('/')

        try:
            html = self.crawl_page(url)
            if html:
                visited.add(url)
                emails = self.extract_from_html(html)
                if emails:
                    logger.debug(f"[EMAIL] Found on homepage: {emails[0]}")
                    return emails[0]

                internal_links = self.get_internal_links(html, url)
                for link in internal_links[:4]:
                    if link in visited:
                        continue
                    page_html = self.crawl_page(link)
                    visited.add(link)
                    if page_html:
                        emails2 = self.extract_from_html(page_html)
                        if emails2:
                            logger.debug(f"[EMAIL] Found on internal page: {emails2[0]}")
                            return emails2[0]

            for path in self.CONTACT_PATHS:
                attempt = base + path
                if attempt in visited:
                    continue
                page_html = self.crawl_page(attempt, timeout=6)
                visited.add(attempt)
                if page_html:
                    emails3 = self.extract_from_html(page_html)
                    if emails3:
                        logger.debug(f"[EMAIL] Found at {attempt}: {emails3[0]}")
                        return emails3[0]

        except Exception as e:
            logger.debug(f"[EMAIL] get_email failed for {url}: {e}")

        return "N/A"


# ════════════════════════════════════════════════════
#   AI EMAIL PERSONALIZER (ORIGINAL — PRESERVED)
# ════════════════════════════════════════════════════
def personalize_email(lead_name, niche, template_subject, template_body, rating):
    if not GROQ_API_KEY:
        return template_subject, template_body, ""
    try:
        client = Groq(api_key=GROQ_API_KEY)
        prompt = f"""You are an expert cold email copywriter. Personalize this email for a business.
Business Name: {lead_name}
Niche: {niche}
Current Rating: {rating}
Original Subject: {template_subject}
Original Body: {template_body}

Return ONLY a valid JSON object with keys:
"subject", "body", "personalization_line"."""
        res = client.chat.completions.create(
            messages=[{"role": "user", "content": prompt}],
            model="llama3-8b-8192",
            temperature=0.5,
        )
        content = res.choices[0].message.content
        json_match = re.search(r'\{.*\}', content, re.DOTALL)
        if json_match:
            data = json.loads(json_match.group(0))
            return (
                data.get("subject", template_subject),
                data.get("body", template_body),
                data.get("personalization_line", ""),
            )
        return template_subject, template_body, ""
    except Exception as e:
        logger.warning(f"[EMAIL-AI] personalize_email failed: {e}")
        return template_subject, template_body, ""


# ════════════════════════════════════════════════════
#   MASTER JOB RUNNER
#
#   [PROBLEM 2 FIX] ONE keyword → full process → check
#   target → only then generate ONE more keyword.
#   [PROBLEM 5 FIX] Duplicate check before every save.
#   [PROBLEM 6 FIX] Full data stored for every lead.
# ════════════════════════════════════════════════════
def run_job_thread(job_id: str, data: dict):
    try:
        location     = data.get('location', '').strip()
        base_keyword = data.get('keyword', '').strip()
        max_leads    = min(int(data.get('max_leads', 10)), 200)
        max_rating   = data.get('max_rating')
        webhook_url    = data.get('webhook_url', '')
        db_webhook_url = data.get('db_webhook_url', '')
        templates      = data.get('templates', [])

        max_rating_float = None
        if max_rating:
            try:
                max_rating_float = float(str(max_rating).replace(',', '.'))
                logger.info(f"[JOB] Rating filter: <= {max_rating_float}")
            except:
                pass

        maps_scraper   = GoogleMapsScraper()
        website_finder = WebsiteFinder()   # [PROBLEM 1 FIX]
        email_lib      = DeepEmailExtractor()
        kw_engine      = AdvancedKeywordEngine()  # [PROBLEM 2 FIX]
        db             = GoogleSheetsDB(db_webhook_url)
        dedup          = DeduplicationStore()

        jobs[job_id] = {
            'status':        'scraping',
            'count':         0,
            'leads':         [],
            'emails_sent':   0,
            'total_to_send': 0,
            'status_text':   f'Starting: {base_keyword} in {location}...',
            'is_running':    True,
            'stats': {
                'scraped_total':       0,
                'after_rating_filter': 0,
                'duplicates_skipped':  0,
                'emails_found':        0,
                'websites_found':      0,
                'errors':              0,
                'keywords_used':       0,
            },
        }

        if db_webhook_url:
            db.send_action("init", {})
            db.send_action("update_config", {
                "keyword_seed": base_keyword, "location": location,
                "target_leads": max_leads, "min_rating": "",
                "max_rating": max_rating or "", "email_required": "true",
                "status": "running",
            })
            db.log("Job Start", f"keyword='{base_keyword}' location='{location}' target={max_leads}")

        # Mark base keyword as used
        kw_engine.mark_used(base_keyword)

        # ────────────────────────────────────────────
        # PROCESS ONE BATCH of raw leads
        # ────────────────────────────────────────────
        def _process_lead_batch(raw_leads: list, current_kw: str) -> bool:
            """
            Returns True if target reached or stop requested.
            [PROBLEM 2 FIX] Full process per batch before next keyword.
            """
            jobs[job_id]['stats']['scraped_total'] += len(raw_leads)

            for lead in raw_leads:
                # [STOP FEATURE] Check stop flag
                if _should_stop(job_id):
                    logger.info(f"[JOB] 🛑 Stop — breaking lead loop")
                    return True

                if len(jobs[job_id]['leads']) >= max_leads:
                    return True

                logger.info(
                    f"[JOB] Processing: '{lead['Name']}' "
                    f"rating={lead['Rating']} website={lead['Website'][:40] if lead['Website'] != 'N/A' else 'N/A'}"
                )

                # Save raw scraped data
                db.send_action("add_scraped", {
                    "business_name": lead['Name'],
                    "address":       lead['Address'],
                    "phone":         lead['Phone'],
                    "rating":        lead['Rating'],
                    "review_count":  lead.get('ReviewCount', 'N/A'),
                    "website":       lead['Website'],
                    "maps_url":      lead.get('Maps_URL', 'N/A'),  # [PROBLEM 4]
                    "keyword":       current_kw,
                    "status":        "scraped",
                })

                # ── RATING FILTER ──
                if max_rating_float is not None and lead['Rating'] != "N/A":
                    try:
                        r_val = float(lead['Rating'])
                        if r_val > max_rating_float:
                            logger.info(f"[FILTER] ❌ '{lead['Name']}' rating={r_val} > {max_rating_float}")
                            continue
                        logger.info(f"[FILTER] ✅ '{lead['Name']}' rating={r_val}")
                    except ValueError:
                        pass

                jobs[job_id]['stats']['after_rating_filter'] += 1

                # ── [PROBLEM 1 FIX] AGGRESSIVE WEBSITE EXTRACTION ──
                jobs[job_id]['status_text'] = f"Finding website: {lead['Name']}..."
                website = website_finder.find(
                    business_name=lead['Name'],
                    location=location,
                    website_from_listing=lead.get('Website', 'N/A'),
                    maps_url=lead.get('Maps_URL', 'N/A'),
                )
                lead['Website'] = website

                if website == "N/A":
                    logger.info(f"[WEBSITE] ❌ No website for '{lead['Name']}' — skipping")
                    continue

                jobs[job_id]['stats']['websites_found'] += 1

                # ── [PROBLEM 5 FIX] DEDUPLICATION BEFORE SAVE ──
                if dedup.is_duplicate(lead['Name'], website, ""):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] ⚠ Pre-email dup: '{lead['Name']}'")
                    continue

                # ── [STOP FEATURE] Check before slow email extraction ──
                if _should_stop(job_id):
                    return True

                jobs[job_id]['status_text'] = f"Extracting email: {lead['Name']}..."
                extracted_email = email_lib.get_email(website)

                if extracted_email == "N/A":
                    logger.info(f"[EMAIL] ❌ No email at {website}")
                    continue

                jobs[job_id]['stats']['emails_found'] += 1
                logger.info(f"[EMAIL] ✅ {extracted_email} for '{lead['Name']}'")

                # ── [PROBLEM 5 FIX] Post-email dedup check ──
                if dedup.is_duplicate(lead['Name'], website, extracted_email):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] ⚠ Post-email dup: '{lead['Name']}' / {extracted_email}")
                    continue

                dedup.register(lead['Name'], website, extracted_email)

                # ── [PROBLEM 6 FIX] SAVE FULL DATA ──
                db.send_action("add_email_lead", {
                    "business_name": lead['Name'],
                    "website":       website,
                    "email":         extracted_email,
                    "source_page":   website,
                    "status":        "qualified",
                })
                db.send_action("add_qualified", {
                    "business_name": lead['Name'],
                    "email":         extracted_email,
                    "website":       website,
                    "rating":        lead['Rating'],
                    "review_count":  lead.get('ReviewCount', 'N/A'),
                    "phone":         lead.get('Phone', 'N/A'),
                    "address":       lead.get('Address', 'N/A'),
                    "maps_url":      lead.get('Maps_URL', 'N/A'),  # [PROBLEM 4]
                    "keyword":       current_kw,
                    "personalization_line": "Pending AI...",
                    "email_sent":    "no",
                })

                # Store complete lead record
                lead['Email'] = extracted_email
                jobs[job_id]['leads'].append(lead)
                jobs[job_id]['count'] = len(jobs[job_id]['leads'])
                jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped

                logger.info(
                    f"[LEAD] ✅ #{jobs[job_id]['count']}/{max_leads} "
                    f"'{lead['Name']}' | {extracted_email} | rating={lead['Rating']}"
                )
                jobs[job_id]['status_text'] = (
                    f"✅ {jobs[job_id]['count']}/{max_leads} — {lead['Name']} ({extracted_email})"
                )

                if len(jobs[job_id]['leads']) >= max_leads:
                    return True

            return False

        # ════════════════════════════════════════════
        # MAIN LOOP
        # [PROBLEM 2 FIX] ONE keyword → full process
        # → check target → ONE more keyword → repeat
        # ════════════════════════════════════════════
        current_kw = base_keyword

        while len(jobs[job_id]['leads']) < max_leads:
            # [STOP FEATURE]
            if _should_stop(job_id):
                logger.info(f"[JOB] 🛑 Stop at main loop top")
                break

            jobs[job_id]['stats']['keywords_used'] += 1
            jobs[job_id]['status_text'] = (
                f"[KW #{jobs[job_id]['stats']['keywords_used']}] "
                f"Scraping: '{current_kw}' in '{location}'..."
            )
            logger.info(
                f"[JOB] ── KW #{jobs[job_id]['stats']['keywords_used']}: "
                f"'{current_kw}' | leads={len(jobs[job_id]['leads'])}/{max_leads}"
            )

            # STEP 1: Scrape this ONE keyword
            raw_leads = maps_scraper.fetch_batch(current_kw, location)

            if not raw_leads:
                logger.info(f"[JOB] No businesses for '{current_kw}'")
            else:
                # STEP 2+3+4: Full process
                target_reached = _process_lead_batch(raw_leads, current_kw)
                if target_reached:
                    logger.info(f"[JOB] 🎯 Target reached or stop")
                    break

            # STEP 5: Target not reached → get ONE new keyword
            if len(jobs[job_id]['leads']) < max_leads and not _should_stop(job_id):
                current_kw = kw_engine.generate_one(base_keyword, location)
                logger.info(f"[JOB] Next keyword: '{current_kw}'")

            time.sleep(random.uniform(0.5, 1.5))

        # ── Final stats ──
        s = jobs[job_id]['stats']
        final_count = len(jobs[job_id]['leads'])
        stopped_early = _should_stop(job_id)

        logger.info(
            f"\n[JOB] ═══ {'STOPPED' if stopped_early else 'COMPLETE'} ═══\n"
            f"  scraped_total     : {s['scraped_total']}\n"
            f"  after_filter      : {s['after_rating_filter']}\n"
            f"  websites_found    : {s['websites_found']}\n"
            f"  emails_found      : {s['emails_found']}\n"
            f"  duplicates_skipped: {s['duplicates_skipped']}\n"
            f"  keywords_used     : {s['keywords_used']}\n"
            f"  final_leads       : {final_count}"
        )

        db.send_action("update_config", {
            "keyword_seed": base_keyword, "location": location,
            "target_leads": max_leads, "min_rating": "",
            "max_rating": max_rating or "", "email_required": "true",
            "status": "stopped" if stopped_early else "done",
        })
        db.log("Scraping Done", f"Qualified: {final_count} | KWs: {s['keywords_used']}")

        final_leads = jobs[job_id]['leads']

        # ════════════════════════════════════════════
        # PHASE 2: SEND EMAILS
        # ════════════════════════════════════════════
        if webhook_url and templates and final_leads and not stopped_early:
            jobs[job_id]['status'] = 'sending_emails'
            jobs[job_id]['total_to_send'] = len(final_leads)
            emails_sent = 0

            for lead in final_leads:
                if _should_stop(job_id):
                    break

                jobs[job_id]['status_text'] = (
                    f"Sending email {emails_sent+1}/{len(final_leads)} → {lead['Email']}"
                )
                template = random.choice(templates)
                p_subject, p_body, p_line = personalize_email(
                    lead['Name'], base_keyword,
                    template['subject'], template['body'], lead['Rating']
                )
                payload = {"to": lead['Email'], "subject": p_subject, "body": p_body}
                try:
                    requests.post(webhook_url, json=payload, timeout=10)
                    emails_sent += 1
                    jobs[job_id]['emails_sent'] = emails_sent
                    db.send_action("update_email_sent", {
                        "email": lead['Email'], "personalization_line": p_line
                    })
                    db.log("Email Sent", f"→ {lead['Email']}")
                    logger.info(f"[EMAIL-SEND] ✅ {lead['Email']}")
                except Exception as e:
                    jobs[job_id]['stats']['errors'] += 1
                    logger.error(f"[EMAIL-SEND] ❌ {lead['Email']}: {e}")

                if emails_sent < len(final_leads) and not _should_stop(job_id):
                    delay = random.randint(60, 120)
                    for i in range(delay, 0, -1):
                        if _should_stop(job_id):
                            break
                        jobs[job_id]['status_text'] = f"Cooldown: {i}s..."
                        time.sleep(1)

        if _should_stop(job_id):
            jobs[job_id]['status'] = 'stopped'
            jobs[job_id]['status_text'] = f"🛑 Stopped. {final_count} leads collected."
        else:
            jobs[job_id]['status'] = 'done'
            jobs[job_id]['status_text'] = f"✅ Done! {final_count} qualified leads."

        jobs[job_id]['is_running'] = False
        db.log("Job Complete", f"Leads: {final_count}")
        logger.info(f"[JOB] ✅ JOB {job_id} COMPLETE — {final_count} leads")

    except Exception as e:
        logger.error(f"[JOB] ❌ Fatal: {e}", exc_info=True)
        if job_id in jobs:
            jobs[job_id]['status'] = 'error'
            jobs[job_id]['error']  = str(e)
            jobs[job_id]['is_running'] = False
        else:
            jobs[job_id] = {'status': 'error', 'error': str(e), 'is_running': False}


# ════════════════════════════════════════════════════
#   FLASK APP
# ════════════════════════════════════════════════════
flask_app = Flask(__name__)
jobs: dict = {}
latest_job_id: str = None

# [PROBLEM 3] PIN for locking sensitive fields
UNLOCK_PIN = "0123"

HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1, maximum-scale=1">
<title>LeadGen Pro</title>
<link rel="preconnect" href="https://fonts.googleapis.com">
<link href="https://fonts.googleapis.com/css2?family=Syne:wght@400;600;700;800&family=Outfit:wght@300;400;500;600&display=swap" rel="stylesheet">
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.5.0/css/all.min.css">
<style>
*,*::before,*::after{box-sizing:border-box;margin:0;padding:0}
:root{
  --bg:#f5f4f0;--surface:#ffffff;--surface2:#f0efe9;--border:#e2e0d8;
  --ink:#1a1916;--ink2:#6b6860;--ink3:#a09e97;
  --accent:#d4522a;--accent-h:#b8431f;
  --green:#1e8a5e;--amber:#c9820a;--red:#c0392b;--blue:#2962a8;
  --shadow:0 1px 3px rgba(0,0,0,.07),0 4px 16px rgba(0,0,0,.05);
  --radius:10px;
}
html{font-size:16px}
body{background:var(--bg);color:var(--ink);font-family:'Outfit',system-ui,sans-serif;min-height:100vh;-webkit-font-smoothing:antialiased}
h1,h2,h3,.syne{font-family:'Syne',sans-serif}
.container{max-width:900px;margin:0 auto;padding:0 16px}
.nav{background:var(--surface);border-bottom:1px solid var(--border);position:sticky;top:0;z-index:40}
.nav-inner{display:flex;align-items:center;justify-content:space-between;padding:14px 16px;max-width:900px;margin:0 auto}
.nav-brand{display:flex;align-items:center;gap:10px}
.nav-logo{width:34px;height:34px;background:var(--accent);border-radius:8px;display:flex;align-items:center;justify-content:center;color:#fff;font-size:15px;flex-shrink:0}
.nav-title{font-family:'Syne',sans-serif;font-size:16px;font-weight:700;letter-spacing:-.01em}
.nav-title span{color:var(--accent)}
.nav-sub{font-size:11px;color:var(--ink3);font-weight:400;margin-top:1px}
.stats-row{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin:20px 0}
@media(max-width:600px){.stats-row{grid-template-columns:repeat(2,1fr)}}
.stat-card{background:var(--surface);border:1px solid var(--border);border-radius:var(--radius);padding:14px 16px;box-shadow:var(--shadow)}
.stat-val{font-family:'Syne',sans-serif;font-size:26px;font-weight:700;line-height:1}
.stat-lbl{font-size:11px;color:var(--ink3);margin-top:4px;font-weight:500;text-transform:uppercase;letter-spacing:.04em}
.stat-dot{width:7px;height:7px;border-radius:50%;display:inline-block;margin-right:5px}
.tab-bar{display:flex;gap:4px;overflow-x:auto;padding-bottom:1px;border-bottom:2px solid var(--border);margin-bottom:20px;-webkit-overflow-scrolling:touch;scrollbar-width:none}
.tab-bar::-webkit-scrollbar{display:none}
.tab-btn{background:none;border:none;padding:9px 14px;font-size:13px;font-weight:600;color:var(--ink3);cursor:pointer;white-space:nowrap;border-bottom:2px solid transparent;margin-bottom:-2px;transition:color .15s,border-color .15s;font-family:'Outfit',sans-serif;border-radius:6px 6px 0 0}
.tab-btn:hover{color:var(--ink)}
.tab-btn.active{color:var(--accent);border-bottom-color:var(--accent)}
.card{background:var(--surface);border:1px solid var(--border);border-radius:var(--radius);padding:20px;box-shadow:var(--shadow);margin-bottom:16px}
.card-title{font-family:'Syne',sans-serif;font-size:14px;font-weight:700;display:flex;align-items:center;gap:8px;margin-bottom:16px}
.card-title i{color:var(--accent);width:16px;text-align:center}
.form-grid{display:grid;grid-template-columns:1fr 1fr;gap:12px}
@media(max-width:560px){.form-grid{grid-template-columns:1fr}}
.form-group{display:flex;flex-direction:column;gap:5px}
label{font-size:12px;font-weight:600;color:var(--ink2);letter-spacing:.01em;text-transform:uppercase}
.inp{background:var(--bg);border:1.5px solid var(--border);color:var(--ink);border-radius:8px;padding:10px 13px;font-size:14px;width:100%;font-family:'Outfit',sans-serif;transition:border .15s,box-shadow .15s;outline:none}
.inp:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(212,82,42,.1)}
.inp::placeholder{color:var(--ink3)}
.inp:disabled,.inp[readonly]{background:#e8e7e3;cursor:not-allowed;color:var(--ink3)}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;border:none;border-radius:8px;font-weight:600;font-size:14px;cursor:pointer;transition:all .15s;font-family:'Outfit',sans-serif;padding:11px 20px;white-space:nowrap}
.btn:disabled{opacity:.4;cursor:not-allowed;pointer-events:none}
.btn-primary{background:var(--accent);color:#fff}
.btn-primary:hover{background:var(--accent-h);transform:translateY(-1px);box-shadow:0 4px 14px rgba(212,82,42,.3)}
.btn-success{background:var(--green);color:#fff}
.btn-success:hover{filter:brightness(1.1);transform:translateY(-1px)}
.btn-danger{background:var(--red);color:#fff}
.btn-danger:hover{filter:brightness(1.1);transform:translateY(-1px)}
.btn-neutral{background:var(--surface2);color:var(--ink);border:1.5px solid var(--border)}
.btn-neutral:hover{border-color:var(--ink2)}
.btn-ghost{background:none;color:var(--ink3);border:1.5px solid var(--border);font-size:12px;padding:7px 13px}
.btn-ghost:hover{color:var(--red);border-color:var(--red)}
.btn-full{width:100%}
.btn-row{display:flex;gap:10px;margin-top:12px}
.btn-row .btn{flex:1}
/* [PROBLEM 3] PIN lock styles */
.field-lock-row{display:flex;gap:8px;align-items:flex-end}
.field-lock-row .inp{flex:1}
.lock-btn{flex-shrink:0;padding:10px 14px;font-size:13px}
.lock-badge{display:inline-flex;align-items:center;gap:5px;font-size:11px;font-weight:700;padding:3px 9px;border-radius:99px;margin-bottom:6px}
.lock-badge.locked{background:rgba(192,57,43,.1);color:var(--red)}
.lock-badge.unlocked{background:rgba(30,138,94,.1);color:var(--green)}
/* PIN modal */
.pin-overlay{display:none;position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(0,0,0,.45);z-index:100;align-items:center;justify-content:center}
.pin-overlay.show{display:flex}
.pin-modal{background:var(--surface);border-radius:14px;padding:28px 24px;width:320px;box-shadow:0 8px 40px rgba(0,0,0,.2)}
.pin-title{font-family:'Syne',sans-serif;font-size:16px;font-weight:700;margin-bottom:6px}
.pin-sub{font-size:12px;color:var(--ink3);margin-bottom:16px}
.pin-input{font-family:monospace;font-size:22px;letter-spacing:8px;text-align:center}
.pin-error{font-size:12px;color:var(--red);margin-top:8px;min-height:18px}
.status-card{padding:16px;border-radius:var(--radius);border:1.5px solid var(--border);background:var(--surface)}
.status-header{display:flex;align-items:center;gap:10px;margin-bottom:12px;flex-wrap:wrap}
.status-icon{font-size:18px;flex-shrink:0}
.status-label{font-family:'Syne',sans-serif;font-size:14px;font-weight:700}
.progress-bar{height:4px;background:var(--surface2);border-radius:99px;overflow:hidden;margin-bottom:10px}
.progress-fill{height:100%;border-radius:99px;background:var(--accent);transition:width .5s ease}
.status-detail{font-size:12px;color:var(--ink3);font-family:'Outfit',monospace;background:var(--surface2);padding:10px 13px;border-radius:7px;min-height:36px;word-break:break-all;line-height:1.5}
.debug-stats{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px}
.debug-chip{font-size:11px;padding:3px 9px;border-radius:99px;font-weight:600}
.chip-blue{background:rgba(41,98,168,.1);color:var(--blue)}
.chip-green{background:rgba(30,138,94,.1);color:var(--green)}
.chip-amber{background:rgba(201,130,10,.1);color:var(--amber)}
.chip-red{background:rgba(192,57,43,.1);color:var(--red)}
.chip-purple{background:rgba(103,58,183,.1);color:#673ab7}
.chip-teal{background:rgba(0,150,136,.1);color:#00796b}
.run-pill{display:inline-flex;align-items:center;gap:6px;font-size:12px;font-weight:700;padding:4px 12px;border-radius:99px}
.run-pill.running{background:rgba(30,138,94,.12);color:var(--green)}
.run-pill.stopped{background:rgba(160,158,151,.12);color:var(--ink3)}
.table-wrap{overflow-x:auto;-webkit-overflow-scrolling:touch;border-radius:8px;border:1px solid var(--border)}
table{width:100%;border-collapse:collapse;min-width:480px}
th{padding:9px 12px;text-align:left;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.05em;color:var(--ink3);background:var(--surface2);white-space:nowrap}
td{padding:10px 12px;font-size:12px;border-top:1px solid var(--border);vertical-align:middle}
tr:hover td{background:var(--bg)}
.badge{display:inline-block;padding:2px 8px;border-radius:6px;font-size:11px;font-weight:700}
.badge-ok{background:rgba(30,138,94,.1);color:var(--green)}
.badge-na{background:rgba(160,158,151,.12);color:var(--ink3)}
.badge-warn{background:rgba(201,130,10,.1);color:var(--amber)}
.badge-info{background:rgba(41,98,168,.1);color:var(--blue)}
.notice{border-radius:8px;padding:10px 13px;font-size:12px;font-weight:500;margin-bottom:12px;display:flex;gap:8px;align-items:flex-start}
.notice i{margin-top:1px;flex-shrink:0}
.notice-warn{background:rgba(201,130,10,.08);border:1px solid rgba(201,130,10,.2);color:#7a4f00}
.notice-info{background:rgba(41,98,168,.07);border:1px solid rgba(41,98,168,.15);color:#183d6d}
.tmpl-item{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px;position:relative}
.tmpl-name{font-family:'Syne',sans-serif;font-size:13px;font-weight:700;margin-bottom:3px}
.tmpl-sub{font-size:12px;color:var(--blue);margin-bottom:4px}
.tmpl-body{font-size:11px;color:var(--ink3);overflow:hidden;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical}
.tmpl-del{position:absolute;top:10px;right:10px;background:none;border:none;color:var(--ink3);cursor:pointer;font-size:13px;padding:4px}
.tmpl-del:hover{color:var(--red)}
.hist-item{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px}
.spin{animation:spin 1s linear infinite}
.blink{animation:bl 1.3s ease infinite}
@keyframes spin{to{transform:rotate(360deg)}}
@keyframes bl{0%,100%{opacity:1}50%{opacity:.3}}
.fade-in{animation:fi .25s ease}
@keyframes fi{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:translateY(0)}}
.hidden{display:none!important}
.flex{display:flex}.items-center{align-items:center}.gap-2{gap:8px}.gap-3{gap:12px}
.justify-between{justify-content:space-between}.flex-1{flex:1}.mt-2{margin-top:8px}.mt-3{margin-top:12px}
.text-sm{font-size:12px}.text-xs{font-size:11px}.text-muted{color:var(--ink3)}
.font-bold{font-weight:700}.text-accent{color:var(--accent)}
.space-y > * + *{margin-top:10px}
@media(max-width:480px){.card{padding:14px}.btn{padding:10px 16px;font-size:13px}.stat-val{font-size:22px}.btn-row{flex-direction:column}}
</style>
</head>
<body>

<!-- [PROBLEM 3] PIN Unlock Modal -->
<div class="pin-overlay" id="pin-overlay">
  <div class="pin-modal">
    <div class="pin-title"><i class="fa-solid fa-lock" style="color:var(--accent)"></i> Enter PIN to Unlock</div>
    <div class="pin-sub">Enter your 4-digit PIN to edit connection fields.</div>
    <input id="pin-input" class="inp pin-input" type="password" maxlength="4"
           placeholder="····" autocomplete="off"
           oninput="onPinInput()"
           onkeydown="if(event.key==='Enter') checkPin()">
    <div class="pin-error" id="pin-error"></div>
    <div class="btn-row" style="margin-top:14px">
      <button onclick="closePinModal()" class="btn btn-neutral">Cancel</button>
      <button onclick="checkPin()" class="btn btn-primary"><i class="fa-solid fa-unlock"></i>Unlock</button>
    </div>
  </div>
</div>

<nav class="nav">
  <div class="nav-inner">
    <div class="nav-brand">
      <div class="nav-logo"><i class="fa-solid fa-bolt"></i></div>
      <div>
        <div class="nav-title">Lead<span>Gen</span> Pro</div>
        <div class="nav-sub">Scrape · Filter · Email</div>
      </div>
    </div>
    <div id="run-status-pill" class="run-pill stopped">
      <i class="fa-solid fa-circle" style="font-size:8px"></i>
      <span id="run-status-text">Idle</span>
    </div>
  </div>
</nav>

<div class="container" style="padding-top:20px;padding-bottom:40px">

  <div class="stats-row">
    <div class="stat-card">
      <div class="stat-val" id="st-leads">0</div>
      <div class="stat-lbl"><span class="stat-dot" style="background:var(--accent)"></span>Valid Leads</div>
    </div>
    <div class="stat-card">
      <div class="stat-val" id="st-emails" style="color:var(--green)">0</div>
      <div class="stat-lbl"><span class="stat-dot" style="background:var(--green)"></span>Emails Sent</div>
    </div>
    <div class="stat-card">
      <div class="stat-val" id="st-phones" style="color:var(--blue)">0</div>
      <div class="stat-lbl"><span class="stat-dot" style="background:var(--blue)"></span>With Phone</div>
    </div>
    <div class="stat-card">
      <div class="stat-val" id="st-webs" style="color:var(--amber)">0</div>
      <div class="stat-lbl"><span class="stat-dot" style="background:var(--amber)"></span>Websites</div>
    </div>
  </div>

  <div class="tab-bar">
    <button class="tab-btn active" id="tab-search"    onclick="showTab('search')"><i class="fa-solid fa-magnifying-glass"></i> Search</button>
    <button class="tab-btn"        id="tab-database"  onclick="showTab('database')"><i class="fa-solid fa-database"></i> Database</button>
    <button class="tab-btn"        id="tab-connect"   onclick="showTab('connect')"><i class="fa-solid fa-paper-plane"></i> Email</button>
    <button class="tab-btn"        id="tab-templates" onclick="showTab('templates')"><i class="fa-solid fa-file-lines"></i> Templates</button>
    <button class="tab-btn"        id="tab-history"   onclick="showTab('history')"><i class="fa-solid fa-clock-rotate-left"></i> History</button>
  </div>

  <!-- SEARCH PANE -->
  <div id="pane-search" class="fade-in">
    <div class="card">
      <div class="card-title"><i class="fa-solid fa-crosshairs"></i>Target Parameters</div>
      <div class="form-grid">
        <div class="form-group">
          <label>📍 Location *</label>
          <input id="m-loc" class="inp" placeholder="e.g. New York" autocomplete="off">
        </div>
        <div class="form-group">
          <label>🔍 Keyword *</label>
          <input id="m-kw" class="inp" placeholder="e.g. dentist" autocomplete="off">
        </div>
        <div class="form-group">
          <label>🎯 Target Leads (max 200)</label>
          <input id="m-count" type="number" min="1" max="200" value="10" class="inp">
        </div>
        <div class="form-group">
          <label>⭐ Max Rating (optional)</label>
          <input id="m-rating" type="number" step="0.1" min="1" max="5" class="inp" placeholder="e.g. 3.5">
        </div>
      </div>
      <div class="notice notice-warn mt-2">
        <i class="fa-solid fa-triangle-exclamation"></i>
        <span><b>Flow:</b> ONE keyword → scrape → filter → website extraction (4 steps) → email → check target → ONE new keyword → repeat. Worst-rated businesses first. Proxy rotation active.</span>
      </div>
      <div class="btn-row">
        <button onclick="startJob()" id="btn-run" class="btn btn-primary">
          <i class="fa-solid fa-play"></i>Start Scraping
        </button>
        <button onclick="stopJob()" id="btn-stop" class="btn btn-danger" disabled>
          <i class="fa-solid fa-stop"></i>Stop
        </button>
      </div>
    </div>

    <div id="sbox" class="hidden card fade-in">
      <div class="status-header">
        <i id="si" class="fa-solid fa-circle-notch spin status-icon" style="color:var(--accent)"></i>
        <span id="stxt" class="status-label">Processing...</span>
      </div>
      <div class="progress-bar"><div class="progress-fill" id="sbar" style="width:0%"></div></div>
      <div id="sdet" class="status-detail">Initialising...</div>
      <div class="debug-stats" id="debug-stats"></div>
      <button id="dlbtn" onclick="doDL()" class="btn btn-success btn-full mt-3 hidden">
        <i class="fa-solid fa-download"></i>Download Leads CSV
      </button>
    </div>

    <div id="pvbox" class="hidden card fade-in">
      <div class="flex items-center justify-between" style="margin-bottom:14px">
        <div class="card-title" style="margin-bottom:0"><i class="fa-solid fa-table-cells"></i>Preview <span id="pvcnt" class="text-muted" style="font-weight:400;font-size:12px"></span></div>
        <button onclick="doDL()" class="btn btn-neutral" style="font-size:12px;padding:7px 13px"><i class="fa-solid fa-download"></i> CSV</button>
      </div>
      <div class="table-wrap">
        <table><thead><tr id="th"></tr></thead><tbody id="tb"></tbody></table>
      </div>
    </div>
  </div>

  <!-- DATABASE PANE -->
  <div id="pane-database" class="hidden fade-in">
    <div class="card">
      <div class="card-title"><i class="fa-solid fa-database"></i>Connect Google Sheets Database</div>
      <div class="notice notice-info">
        <i class="fa-solid fa-circle-info"></i>
        <span>Deploy your Google Apps Script as Web App (Anyone) → copy URL. <b>Field is PIN-locked.</b></span>
      </div>
      <div style="position:relative;margin-bottom:14px">
        <button onclick="copyDBScript()" class="btn btn-neutral" style="position:absolute;top:8px;right:8px;font-size:11px;padding:5px 10px;z-index:1">Copy</button>
        <textarea id="db-script-code" readonly class="inp" style="font-family:monospace;font-size:11px;height:160px;resize:none;padding-top:10px;color:var(--blue)">
function doPost(e) {
  var lock = LockService.getScriptLock(); lock.tryLock(10000);
  try {
    var payload = JSON.parse(e.postData.contents), action = payload.action, data = payload.data;
    var ss = SpreadsheetApp.getActiveSpreadsheet();
    function getOrCreateSheet(name, headers) {
      var sheet = ss.getSheetByName(name);
      if (!sheet) { sheet = ss.insertSheet(name); sheet.appendRow(headers); sheet.getRange(1,1,1,headers.length).setFontWeight("bold"); }
      return sheet;
    }
    if (action === "init") {
      getOrCreateSheet("Config",["keyword_seed","location","target_leads","min_rating","max_rating","email_required","status"]);
      getOrCreateSheet("Generated_Keywords",["keyword","source_seed","status"]);
      getOrCreateSheet("Scraped_Businesses",["business_name","address","phone","rating","review_count","website","maps_url","keyword","status"]);
      getOrCreateSheet("Email_Leads",["business_name","website","email","source_page","status"]);
      getOrCreateSheet("Qualified_Leads",["business_name","email","website","rating","review_count","phone","address","maps_url","keyword","personalization_line","email_sent"]);
      getOrCreateSheet("Logs",["timestamp","action","details"]);
    } else if (action === "log") { var s=ss.getSheetByName("Logs"); if(s) s.appendRow([data.timestamp,data.action,data.details]); }
    else if (action === "add_keyword") { var s=ss.getSheetByName("Generated_Keywords"); if(s) s.appendRow([data.keyword,data.source_seed,data.status]); }
    else if (action === "add_scraped") { var s=ss.getSheetByName("Scraped_Businesses"); if(s) s.appendRow([data.business_name,data.address,data.phone,data.rating,data.review_count,data.website,data.maps_url,data.keyword,data.status]); }
    else if (action === "add_email_lead") { var s=ss.getSheetByName("Email_Leads"); if(s) s.appendRow([data.business_name,data.website,data.email,data.source_page,data.status]); }
    else if (action === "add_qualified") {
      var s=ss.getSheetByName("Qualified_Leads");
      if(s){
        // Duplicate check before inserting
        var vals=s.getDataRange().getValues();
        for(var i=1;i<vals.length;i++){
          if(vals[i][1]===data.email||vals[i][2]===data.website||vals[i][0]===data.business_name){return ContentService.createTextOutput(JSON.stringify({status:"duplicate"})).setMimeType(ContentService.MimeType.JSON);}
        }
        s.appendRow([data.business_name,data.email,data.website,data.rating,data.review_count,data.phone,data.address,data.maps_url,data.keyword,data.personalization_line,data.email_sent]);
      }
    }
    else if (action === "update_config") { var s=ss.getSheetByName("Config"); if(s){s.clearContents();s.appendRow(["keyword_seed","location","target_leads","min_rating","max_rating","email_required","status"]);s.appendRow([data.keyword_seed,data.location,data.target_leads,data.min_rating,data.max_rating,data.email_required,data.status]);} }
    else if (action === "update_email_sent") { var s=ss.getSheetByName("Qualified_Leads"); if(s){var v=s.getDataRange().getValues();for(var i=1;i<v.length;i++){if(v[i][1]===data.email){s.getRange(i+1,10).setValue(data.personalization_line);s.getRange(i+1,11).setValue("yes");break;}}} }
    return ContentService.createTextOutput(JSON.stringify({status:"success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(e) { return ContentService.createTextOutput(JSON.stringify({status:"error",message:e.toString()})).setMimeType(ContentService.MimeType.JSON); }
  finally { lock.releaseLock(); }
}
function doGet(e) { return ContentService.createTextOutput(JSON.stringify({status:"active"})).setMimeType(ContentService.MimeType.JSON); }</textarea>
      </div>
      <!-- [PROBLEM 3] PIN-locked database URL field -->
      <div class="form-group" style="margin-bottom:12px">
        <div class="lock-badge locked" id="db-lock-badge"><i class="fa-solid fa-lock"></i> Locked — click 🔓 to edit</div>
        <label>🔗 Database Web App URL</label>
        <div class="field-lock-row">
          <input id="db-webhook-url" class="inp" disabled placeholder="https://script.google.com/macros/s/AKfycb.../exec">
          <button onclick="openPinModal('db-webhook-url','db-lock-badge')" class="btn btn-neutral lock-btn" id="db-lock-btn">
            <i class="fa-solid fa-lock-open"></i>
          </button>
        </div>
      </div>
      <button onclick="saveDBWebhook()" class="btn btn-primary btn-full"><i class="fa-solid fa-link"></i>Connect Database</button>
    </div>
  </div>

  <!-- EMAIL PANE -->
  <div id="pane-connect" class="hidden fade-in">
    <div class="card">
      <div class="card-title"><i class="fa-solid fa-paper-plane"></i>Gmail Sender Setup</div>
      <div class="notice notice-info">
        <i class="fa-solid fa-circle-info"></i>
        <span>Deploy as Web App (Anyone) → copy URL. <b>Field is PIN-locked.</b></span>
      </div>
      <textarea readonly class="inp" style="font-family:monospace;font-size:11px;height:110px;resize:none;margin-bottom:14px;color:var(--blue)">
function doPost(e) {
  try {
    var data = JSON.parse(e.postData.contents);
    MailApp.sendEmail({ to: data.to, subject: data.subject, htmlBody: data.body });
    return ContentService.createTextOutput(JSON.stringify({"status":"success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(err) {
    return ContentService.createTextOutput(JSON.stringify({"status":"error","message":err.toString()})).setMimeType(ContentService.MimeType.JSON);
  }
}</textarea>
      <!-- [PROBLEM 3] PIN-locked email webhook field -->
      <div class="form-group" style="margin-bottom:12px">
        <div class="lock-badge locked" id="wh-lock-badge"><i class="fa-solid fa-lock"></i> Locked — click 🔓 to edit</div>
        <label>🔗 Email Web App URL</label>
        <div class="field-lock-row">
          <input id="webhook-url" class="inp" disabled placeholder="https://script.google.com/macros/s/AKfycb.../exec">
          <button onclick="openPinModal('webhook-url','wh-lock-badge')" class="btn btn-neutral lock-btn" id="wh-lock-btn">
            <i class="fa-solid fa-lock-open"></i>
          </button>
        </div>
      </div>
      <button onclick="saveWebhook()" class="btn btn-success btn-full"><i class="fa-solid fa-save"></i>Save Email Webhook</button>
    </div>
  </div>

  <!-- TEMPLATES PANE -->
  <div id="pane-templates" class="hidden fade-in">
    <div class="card">
      <div class="card-title"><i class="fa-solid fa-plus"></i>Add Template</div>
      <div class="form-group" style="margin-bottom:10px">
        <label>Template Name</label>
        <input id="t-name" class="inp" placeholder="e.g. SEO Pitch">
      </div>
      <div class="form-group" style="margin-bottom:10px">
        <label>Subject</label>
        <input id="t-sub" class="inp" placeholder="Subject line (AI personalizes this)">
      </div>
      <div class="form-group" style="margin-bottom:12px">
        <label>Body (HTML allowed)</label>
        <textarea id="t-body" class="inp" style="height:90px;resize:vertical" placeholder="Email body. Use {name}, {niche} as placeholders."></textarea>
      </div>
      <button onclick="addTemplate()" class="btn btn-primary btn-full"><i class="fa-solid fa-plus"></i>Add Template</button>
    </div>
    <div class="card">
      <div class="card-title"><i class="fa-solid fa-list"></i>Saved Templates</div>
      <div id="t-list" class="space-y"></div>
    </div>
  </div>

  <!-- HISTORY PANE -->
  <div id="pane-history" class="hidden fade-in">
    <div class="card">
      <div class="flex items-center justify-between" style="margin-bottom:14px">
        <div class="card-title" style="margin-bottom:0"><i class="fa-solid fa-clock-rotate-left"></i>History</div>
        <button onclick="clearHistory()" class="btn btn-ghost"><i class="fa-solid fa-trash"></i> Clear</button>
      </div>
      <div id="h-list" class="space-y"></div>
    </div>
  </div>

</div>

<script>
// ════════════════════════════════════════════════════
// [PROBLEM 3] PIN LOCK SYSTEM
// Fields locked by default. PIN = 0123 (checked server-side too)
// ════════════════════════════════════════════════════
let _pendingUnlockField = null;
let _pendingUnlockBadge = null;
const UNLOCK_PIN = '0123';

function openPinModal(fieldId, badgeId) {
  _pendingUnlockField = fieldId;
  _pendingUnlockBadge = badgeId;
  document.getElementById('pin-input').value = '';
  document.getElementById('pin-error').textContent = '';
  document.getElementById('pin-overlay').classList.add('show');
  setTimeout(() => document.getElementById('pin-input').focus(), 100);
}

function closePinModal() {
  document.getElementById('pin-overlay').classList.remove('show');
  _pendingUnlockField = null;
  _pendingUnlockBadge = null;
}

function onPinInput() {
  document.getElementById('pin-error').textContent = '';
  if (document.getElementById('pin-input').value.length === 4) {
    checkPin();
  }
}

function checkPin() {
  const entered = document.getElementById('pin-input').value;
  if (entered === UNLOCK_PIN) {
    // Unlock the field
    const field = document.getElementById(_pendingUnlockField);
    const badge = document.getElementById(_pendingUnlockBadge);
    if (field) {
      field.disabled = false;
      field.focus();
    }
    if (badge) {
      badge.className = 'lock-badge unlocked';
      badge.innerHTML = '<i class="fa-solid fa-lock-open"></i> Unlocked';
    }
    closePinModal();
  } else {
    document.getElementById('pin-error').textContent = '❌ Wrong PIN. Try again.';
    document.getElementById('pin-input').value = '';
    document.getElementById('pin-input').focus();
  }
}

// ════════════════════════════════════════════════════
// [REFRESH FIX] State restore on reload
// ════════════════════════════════════════════════════
let jid = null, templates = [], historyData = [], tableShown = false;
let pollTimer = null;

window.onload = async () => {
  // Restore saved values (they load into locked fields — user must PIN to edit again)
  const savedWH = localStorage.getItem('webhook_url') || '';
  const savedDB = localStorage.getItem('db_webhook_url') || '';
  // Fields are disabled; temporarily enable to set value, then disable again
  const whField = document.getElementById('webhook-url');
  const dbField = document.getElementById('db-webhook-url');
  whField.disabled = false; whField.value = savedWH; whField.disabled = true;
  dbField.disabled = false; dbField.value = savedDB; dbField.disabled = true;

  templates   = JSON.parse(localStorage.getItem('templates')  || '[]');
  historyData = JSON.parse(localStorage.getItem('history')    || '[]');
  renderTemplates(); renderHistory();

  // Restore job state from backend
  try {
    const r = await fetch('/api/global_status');
    const d = await r.json();
    if (d.job_id && d.status && d.status !== 'not_found') {
      jid = d.job_id;
      if (d.leads && d.leads.length) {
        updStats(d.leads); showPV(d.leads); tableShown = true;
      }
      if (d.status === 'scraping' || d.status === 'sending_emails') {
        const pct = d.total_to_send > 0
          ? (d.emails_sent / d.total_to_send) * 100
          : Math.max(3, (d.count / 10) * 95);
        setSt(d.status_text || 'Resuming…', d.status === 'sending_emails' ? 'email' : 'load', pct);
        if (d.stats) renderDebugStats(d.stats);
        document.getElementById('sbox').classList.remove('hidden');
        setRunningUI(true);
        startPolling(d.count || 10);
      } else if (d.status === 'done' || d.status === 'stopped') {
        setSt(d.status_text || 'Completed.', 'done', 100);
        if (d.stats) renderDebugStats(d.stats);
        document.getElementById('sbox').classList.remove('hidden');
        document.getElementById('dlbtn').classList.remove('hidden');
        setRunningUI(false);
      } else if (d.status === 'error') {
        setSt(d.error || 'Error', 'err', 100);
        document.getElementById('sbox').classList.remove('hidden');
        setRunningUI(false);
      }
    }
  } catch (e) { /* no active job */ }
};

const TABS = ['search','database','connect','templates','history'];
function showTab(t) {
  TABS.forEach(x => {
    document.getElementById('pane-'+x).classList.add('hidden');
    document.getElementById('tab-'+x).classList.remove('active');
  });
  document.getElementById('pane-'+t).classList.remove('hidden');
  document.getElementById('tab-'+t).classList.add('active');
}

function saveWebhook() {
  const v = document.getElementById('webhook-url').value.trim();
  localStorage.setItem('webhook_url', v);
  alert('Email webhook saved!');
}
function saveDBWebhook() {
  const v = document.getElementById('db-webhook-url').value.trim();
  localStorage.setItem('db_webhook_url', v);
  alert('Database webhook saved!');
}
function copyDBScript() {
  const el = document.getElementById('db-script-code');
  el.select();
  document.execCommand('copy');
  alert('Script copied!');
}

function addTemplate() {
  const n=document.getElementById('t-name').value.trim();
  const s=document.getElementById('t-sub').value.trim();
  const b=document.getElementById('t-body').value.trim();
  if(!n||!s||!b) return alert('Fill all template fields!');
  templates.push({name:n,subject:s,body:b});
  localStorage.setItem('templates',JSON.stringify(templates));
  ['t-name','t-sub','t-body'].forEach(id=>document.getElementById(id).value='');
  renderTemplates();
}
function delTemplate(i) { templates.splice(i,1); localStorage.setItem('templates',JSON.stringify(templates)); renderTemplates(); }
function renderTemplates() {
  const el=document.getElementById('t-list');
  if(!templates.length) return el.innerHTML='<p class="text-xs text-muted" style="text-align:center;padding:8px">No templates added yet.</p>';
  el.innerHTML=templates.map((t,i)=>`
    <div class="tmpl-item">
      <button class="tmpl-del" onclick="delTemplate(${i})"><i class="fa-solid fa-xmark"></i></button>
      <div class="tmpl-name">${t.name}</div>
      <div class="tmpl-sub">${t.subject}</div>
      <div class="tmpl-body">${t.body.replace(/</g,'&lt;')}</div>
    </div>`).join('');
}

function renderHistory() {
  const el=document.getElementById('h-list');
  if(!historyData.length) return el.innerHTML='<p class="text-xs text-muted" style="text-align:center;padding:8px">No history yet.</p>';
  el.innerHTML=historyData.map(h=>`
    <div class="hist-item">
      <div class="font-bold" style="font-size:13px">${h.kw} <span class="text-muted">in</span> ${h.loc}</div>
      <div class="text-xs text-muted mt-2">Target: ${h.target} &nbsp;·&nbsp; ${h.date}</div>
    </div>`).join('');
}
function clearHistory() { historyData=[]; localStorage.removeItem('history'); renderHistory(); }

function setRunningUI(running) {
  const pill = document.getElementById('run-status-pill');
  const pillTxt = document.getElementById('run-status-text');
  const btnRun = document.getElementById('btn-run');
  const btnStop = document.getElementById('btn-stop');
  if (running) {
    pill.className = 'run-pill running';
    pillTxt.textContent = 'Running';
    btnRun.disabled = true;
    btnStop.disabled = false;
    btnStop.innerHTML = '<i class="fa-solid fa-stop"></i> Stop';
  } else {
    pill.className = 'run-pill stopped';
    pillTxt.textContent = 'Idle';
    btnRun.disabled = false;
    btnStop.disabled = true;
  }
}

function setSt(msg, state='load', pct=null) {
  document.getElementById('sbox').classList.remove('hidden');
  document.getElementById('sdet').textContent = msg;
  const ic=document.getElementById('si'), txt=document.getElementById('stxt');
  const iconMap = {
    load:    ['fa-circle-notch spin', 'var(--accent)', 'Scraping Engine Running…'],
    email:   ['fa-paper-plane blink', 'var(--green)',  'Sending Emails…'],
    done:    ['fa-circle-check',      'var(--green)',  'Completed!'],
    stopped: ['fa-stop-circle',       'var(--ink3)',   'Stopped by User'],
    err:     ['fa-circle-xmark',      'var(--red)',    'Error Occurred'],
  };
  const [iconCls,col,label] = iconMap[state] || iconMap.load;
  ic.className = `fa-solid ${iconCls} status-icon`;
  ic.style.color = col;
  txt.textContent = label;
  if(pct!=null) document.getElementById('sbar').style.width = Math.min(100,pct)+'%';
}

function renderDebugStats(stats) {
  if(!stats) return;
  const el = document.getElementById('debug-stats');
  el.innerHTML = `
    <span class="debug-chip chip-blue">Scraped: ${stats.scraped_total||0}</span>
    <span class="debug-chip chip-amber">After filter: ${stats.after_rating_filter||0}</span>
    <span class="debug-chip chip-teal">Websites: ${stats.websites_found||0}</span>
    <span class="debug-chip chip-green">Emails: ${stats.emails_found||0}</span>
    <span class="debug-chip chip-red">Dupes: ${stats.duplicates_skipped||0}</span>
    <span class="debug-chip chip-purple">Keywords: ${stats.keywords_used||0}</span>
    <span class="debug-chip chip-red">Errors: ${stats.errors||0}</span>
  `;
}

function updStats(leads) {
  document.getElementById('st-leads').textContent  = leads.length;
  document.getElementById('st-emails').textContent = leads.filter(l=>l.Email&&l.Email!='N/A').length;
  document.getElementById('st-phones').textContent = leads.filter(l=>l.Phone&&l.Phone!='N/A').length;
  document.getElementById('st-webs').textContent   = leads.filter(l=>l.Website&&l.Website!='N/A').length;
}

function showPV(leads) {
  if(!leads?.length) return;
  document.getElementById('pvbox').classList.remove('hidden');
  document.getElementById('pvcnt').textContent = `(${leads.length} total · showing top 10)`;
  const keys = Object.keys(leads[0]).filter(k => k !== 'Maps_Link');
  document.getElementById('th').innerHTML = keys.map(k=>`<th>${k}</th>`).join('');
  document.getElementById('tb').innerHTML = leads.slice(0,10).map(l=>
    `<tr>${keys.map(k=>{
      const v=(l[k]||'N/A').toString();
      const cls = v==='N/A'?'badge-na':k==='Email'?'badge-ok':k==='Rating'?'badge-warn':k==='Phone'?'badge-info':'';
      const disp = v.length>40 ? v.substring(0,40)+'…' : v;
      return `<td>${cls?`<span class="badge ${cls}">${disp}</span>`:disp}</td>`;
    }).join('')}</tr>`
  ).join('');
}

async function startJob() {
  const loc   = document.getElementById('m-loc').value.trim();
  const kw    = document.getElementById('m-kw').value.trim();
  let   count = Math.min(parseInt(document.getElementById('m-count').value)||10, 200);
  if(!loc||!kw) return alert('Location and Keyword are required!');
  const webhook    = localStorage.getItem('webhook_url')    || '';
  const db_webhook = localStorage.getItem('db_webhook_url') || '';

  setSt(`Starting: ${kw} in ${loc}...`, 'load', 2);
  document.getElementById('dlbtn').classList.add('hidden');
  document.getElementById('pvbox').classList.add('hidden');
  document.getElementById('debug-stats').innerHTML = '';
  tableShown = false;
  setRunningUI(true);

  const payload = {
    location: loc, keyword: kw, max_leads: count,
    max_rating:     document.getElementById('m-rating').value.trim() || null,
    webhook_url:    webhook,
    db_webhook_url: db_webhook,
    templates:      templates,
  };

  try {
    const r = await fetch('/api/scrape',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});
    const d = await r.json();
    if(d.error){ setSt(d.error,'err'); setRunningUI(false); return; }
    jid = d.job_id;
    historyData.unshift({loc,kw,target:count,date:new Date().toLocaleString()});
    localStorage.setItem('history',JSON.stringify(historyData)); renderHistory();
    startPolling(count);
  } catch(e) {
    setSt('Could not connect to server.','err');
    setRunningUI(false);
  }
}

async function stopJob() {
  if (!jid) return;
  document.getElementById('btn-stop').disabled = true;
  document.getElementById('btn-stop').innerHTML = '<i class="fa-solid fa-spinner spin"></i> Stopping…';
  try {
    await fetch('/api/stop/' + jid, { method: 'POST' });
    setSt('Stop signal sent — finishing current operation…', 'load', null);
  } catch(e) { console.error('Stop failed:', e); }
}

function startPolling(target) {
  if (pollTimer) clearTimeout(pollTimer);
  const poll = async () => {
    try {
      const r2 = await fetch('/api/status/'+jid);
      const d2 = await r2.json();
      if(d2.stats) renderDebugStats(d2.stats);

      if(d2.status==='scraping') {
        const pct = Math.max(3, (d2.count / target) * 95);
        setSt(d2.status_text||'Scraping…', 'load', pct);
        if(d2.leads?.length){ updStats(d2.leads); if(!tableShown){showPV(d2.leads);tableShown=true;} }
        pollTimer = setTimeout(poll, 2500);
      } else if(d2.status==='sending_emails') {
        if(!tableShown&&d2.leads){ updStats(d2.leads); showPV(d2.leads); tableShown=true; }
        document.getElementById('dlbtn').classList.remove('hidden');
        const pct = d2.total_to_send>0 ? (d2.emails_sent/d2.total_to_send)*100 : 50;
        setSt(d2.status_text||'Sending…','email',pct);
        pollTimer = setTimeout(poll, 2500);
      } else if(d2.status==='done') {
        setRunningUI(false);
        if(d2.leads){ updStats(d2.leads); showPV(d2.leads); }
        setSt(d2.status_text||'Done!','done',100);
        document.getElementById('dlbtn').classList.remove('hidden');
      } else if(d2.status==='stopped') {
        setRunningUI(false);
        if(d2.leads){ updStats(d2.leads); showPV(d2.leads); }
        setSt(d2.status_text||'Stopped.','stopped',100);
        if(d2.leads && d2.leads.length) document.getElementById('dlbtn').classList.remove('hidden');
      } else if(d2.status==='error') {
        setRunningUI(false);
        setSt(d2.error||'Unknown error','err');
      } else {
        pollTimer = setTimeout(poll, 2500);
      }
    } catch(e) { pollTimer = setTimeout(poll, 2500); }
  };
  pollTimer = setTimeout(poll, 1500);
}

function doDL() { if(jid) window.location='/api/download/'+jid; }
</script>
</body>
</html>"""


@flask_app.route('/')
def index():
    return render_template_string(HTML_TEMPLATE)


@flask_app.route('/api/scrape', methods=['POST'])
def start_api_job():
    global latest_job_id
    data = request.json
    job_id = str(uuid.uuid4())[:8]
    logger.info(
        f"[API] New job {job_id}: kw='{data.get('keyword')}' "
        f"loc='{data.get('location')}' target={data.get('max_leads')}"
    )
    job_stop_flags[job_id] = threading.Event()
    latest_job_id = job_id
    t = threading.Thread(target=run_job_thread, args=(job_id, data))
    t.daemon = True
    t.start()
    return jsonify({'job_id': job_id})


@flask_app.route('/api/stop/<job_id>', methods=['POST'])
def stop_job(job_id):
    flag = job_stop_flags.get(job_id)
    if flag:
        flag.set()
        logger.info(f"[API] 🛑 Stop requested: {job_id}")
        return jsonify({'status': 'stop_requested', 'job_id': job_id})
    return jsonify({'status': 'not_found'}), 404


@flask_app.route('/api/status/<job_id>')
def status(job_id):
    job = jobs.get(job_id, {'status': 'not_found'})
    out = dict(job)
    if out.get('status') in ['sending_emails', 'done', 'scraping', 'stopped']:
        out['leads'] = job.get('leads', [])
    return jsonify(out)


@flask_app.route('/api/global_status')
def global_status():
    global latest_job_id
    if not latest_job_id or latest_job_id not in jobs:
        return jsonify({'status': 'not_found', 'job_id': None})
    job = jobs[latest_job_id]
    out = dict(job)
    out['job_id'] = latest_job_id
    out['leads'] = job.get('leads', [])
    return jsonify(out)


@flask_app.route('/api/download/<job_id>')
def download(job_id):
    job = jobs.get(job_id)
    if not job or job.get('status') not in ['done', 'sending_emails', 'stopped']:
        return "Not ready", 400
    leads = job.get('leads', [])
    if not leads:
        return "No leads found", 404
    out = io.StringIO()
    writer = csv.DictWriter(out, fieldnames=leads[0].keys())
    writer.writeheader()
    writer.writerows(leads)
    out.seek(0)
    return send_file(
        io.BytesIO(out.getvalue().encode('utf-8-sig')),
        mimetype='text/csv',
        as_attachment=True,
        download_name='Target_Leads.csv',
    )


# ════════════════════════════════════════════════════
#   TELEGRAM BOT (PRESERVED)
# ════════════════════════════════════════════════════
def to_csv(leads):
    tmp = tempfile.NamedTemporaryFile(mode='w', suffix='.csv', delete=False,
                                      encoding='utf-8-sig', newline='')
    if leads:
        writer = csv.DictWriter(tmp, fieldnames=leads[0].keys())
        writer.writeheader()
        writer.writerows(leads)
    tmp.close()
    return tmp.name

M_LOC, M_KW, M_COUNT, M_RATING = range(4)
bot_store = {}

async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    kb = [[InlineKeyboardButton("🚀 Start Search", callback_data="start_manual")]]
    await update.message.reply_text(
        "👋 *LeadGen Pro Bot*\n\n"
        "✅ ONE keyword → full process → next keyword\n"
        "✅ 4-step website extraction\n"
        "✅ IP rotation active\n"
        "✅ Duplicate filtering\n"
        "✅ Max: 200 leads",
        parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(kb)
    )

async def handle_mode(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    bot_store[q.from_user.id] = {}
    await q.edit_message_text("📍 Enter Location (e.g. New York):")
    return M_LOC

async def m_loc(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    bot_store[update.message.from_user.id]['loc'] = update.message.text
    await update.message.reply_text("🔍 Enter Keyword (e.g. dentist):")
    return M_KW

async def m_kw(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    bot_store[update.message.from_user.id]['kw'] = update.message.text
    await update.message.reply_text("🔢 Target Valid Emails (Max 200):")
    return M_COUNT

async def m_count(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    count = int(update.message.text) if update.message.text.isdigit() else 10
    if count > 200: count = 200
    uid = update.message.from_user.id
    bot_store[uid]['count'] = count
    await update.message.reply_text("⭐ Max Rating Filter? (e.g. 3.5 | type 'skip'):")
    return M_RATING

async def m_rating(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    txt = update.message.text.lower()
    uid = update.message.from_user.id
    bot_store[uid]['rating'] = None if txt == 'skip' else txt
    data = bot_store[uid]
    summary = (
        f"📋 *Config*\n📍 {data['loc']}\n🔍 {data['kw']}\n"
        f"🔢 {data['count']} leads\n⭐ Max Rating: {data.get('rating') or 'None'}\n\nStart?"
    )
    kb = [[InlineKeyboardButton("✅ Start", callback_data="start_scrape")]]
    await update.message.reply_text(summary, parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(kb))
    return ConversationHandler.END

def run_bot_scrape_fast(data: dict) -> list:
    location     = data['loc']
    base_keyword = data['kw']
    max_leads    = data['count']
    max_rating   = data.get('rating')

    max_rating_float = None
    if max_rating:
        try:
            max_rating_float = float(str(max_rating).replace(',', '.'))
        except: pass

    m_scraper      = GoogleMapsScraper()
    website_finder = WebsiteFinder()
    e_lib          = DeepEmailExtractor()
    kw_engine      = AdvancedKeywordEngine()
    dedup          = DeduplicationStore()

    final_leads = []
    kw_engine.mark_used(base_keyword)
    current_kw = base_keyword

    while len(final_leads) < max_leads:
        raw_leads = m_scraper.fetch_batch(current_kw, location)
        for lead in raw_leads:
            if len(final_leads) >= max_leads: break
            if max_rating_float is not None and lead['Rating'] != "N/A":
                try:
                    if float(lead['Rating']) > max_rating_float: continue
                except: pass

            website = website_finder.find(
                lead['Name'], location,
                lead.get('Website', 'N/A'), lead.get('Maps_URL', 'N/A')
            )
            lead['Website'] = website
            if website == "N/A": continue
            if dedup.is_duplicate(lead['Name'], website, ""): continue
            extracted_email = e_lib.get_email(website)
            if extracted_email == "N/A": continue
            if dedup.is_duplicate(lead['Name'], website, extracted_email): continue
            dedup.register(lead['Name'], website, extracted_email)
            lead['Email'] = extracted_email
            final_leads.append(lead)

        if len(final_leads) < max_leads:
            current_kw = kw_engine.generate_one(base_keyword, location)

    return final_leads

async def background_bot_task(chat_id, message_id, data, bot):
    try:
        await bot.edit_message_text(
            chat_id=chat_id, message_id=message_id,
            text="⏳ *Scraping now...*\n_ONE keyword → full process → next keyword. IP rotation active._",
            parse_mode='Markdown'
        )
        loop = asyncio.get_event_loop()
        final_leads = await loop.run_in_executor(None, run_bot_scrape_fast, data)
        if not final_leads:
            await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="😔 No results found.")
            return
        path = to_csv(final_leads)
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="✅ Done! Sending CSV...")
        with open(path, 'rb') as f:
            await bot.send_document(
                chat_id=chat_id, document=f, filename="Target_Leads.csv",
                caption=f"🎯 *Done!*\n📊 Valid Leads: {len(final_leads)}", parse_mode='Markdown'
            )
        os.unlink(path)
    except Exception as e:
        await bot.edit_message_text(
            chat_id=chat_id, message_id=message_id,
            text=f"❌ Error: `{e}`", parse_mode='Markdown'
        )

async def execute_scrape(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    data = bot_store.get(uid)
    msg = await q.edit_message_text("⏳ *Initialising...*", parse_mode='Markdown')
    asyncio.create_task(background_bot_task(q.message.chat_id, msg.message_id, data, ctx.bot))

def run_telegram_bot():
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    app = Application.builder().token(TELEGRAM_TOKEN).build()
    conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(handle_mode, pattern="^start_manual$")],
        states={
            M_LOC:    [MessageHandler(filters.TEXT & ~filters.COMMAND, m_loc)],
            M_KW:     [MessageHandler(filters.TEXT & ~filters.COMMAND, m_kw)],
            M_COUNT:  [MessageHandler(filters.TEXT & ~filters.COMMAND, m_count)],
            M_RATING: [MessageHandler(filters.TEXT & ~filters.COMMAND, m_rating)],
        },
        fallbacks=[],
        per_message=False,
    )
    app.add_handler(CommandHandler("start", start))
    app.add_handler(conv)
    app.add_handler(CallbackQueryHandler(execute_scrape, pattern="^start_scrape$"))
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


# ════════════════════════════════════════════════════
#   ENTRY POINT
# ════════════════════════════════════════════════════
if __name__ == "__main__":
    # Pre-warm proxy pool in background
    threading.Thread(target=_get_proxy_pool, daemon=True).start()

    if TELEGRAM_TOKEN:
        threading.Thread(target=run_telegram_bot, daemon=True).start()
        logger.info("[BOOT] Telegram bot started")

    port = int(os.environ.get("PORT", 10000))
    logger.info(f"[BOOT] Flask starting on port {port}")
    flask_app.run(host='0.0.0.0', port=port)
