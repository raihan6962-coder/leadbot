import os, csv, asyncio, tempfile, threading, io, uuid, re, time, json, urllib.parse, random, logging
import requests
import concurrent.futures
import urllib3
from bs4 import BeautifulSoup
from dotenv import load_dotenv
from groq import Groq
from flask import Flask, render_template_string, request, send_file, jsonify

# Telegram imports preserved
from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup
from telegram.ext import (
    Application, CommandHandler, MessageHandler,
    filters, ContextTypes, ConversationHandler, CallbackQueryHandler
)

urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
load_dotenv()

# ════════════════════════════════════════════════════
#   LOGGING SETUP
# ════════════════════════════════════════════════════
logging.basicConfig(
    level=logging.INFO,
    format='[%(asctime)s] %(levelname)s — %(message)s',
    datefmt='%H:%M:%S'
)
logger = logging.getLogger("LeadGenPro")

TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
GROQ_API_KEY   = os.getenv("GROQ_API_KEY")

# PIN for locking sensitive settings
ACCESS_PIN = "0123"

# ════════════════════════════════════════════════════
#   BACKEND PERSISTENT SETTINGS STORE
#   Replaces localStorage — works across ALL browsers/devices
# ════════════════════════════════════════════════════
_settings: dict = {
    "webhook_url":    "",
    "db_webhook_url": "",
    "templates":      [],
}
_settings_lock = threading.Lock()

def get_settings() -> dict:
    with _settings_lock:
        return dict(_settings)

def save_settings(key: str, value) -> None:
    with _settings_lock:
        _settings[key] = value

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
]

def get_headers():
    return random.choice(HEADERS_POOL).copy()


# ════════════════════════════════════════════════════
#   GOOGLE SHEETS DB WRAPPER  (UNCHANGED)
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
#   DEDUPLICATION STORE  (UNCHANGED)
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
            if nn and nn in self._names:    return True
            if nw and nw in self._websites: return True
            if ne and ne in self._emails:   return True
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
#   ADVANCED KEYWORD ENGINE  (UNCHANGED — PRESERVED)
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
        self.session = requests.Session()

    def google_autosuggest(self, keyword, location):
        results = set()
        base_terms = [keyword, f"{keyword} {location}", f"best {keyword}", f"{keyword} services"]
        for term in base_terms:
            try:
                url = f"https://suggestqueries.google.com/complete/search?client=firefox&q={urllib.parse.quote_plus(term)}"
                r = self.session.get(url, headers=get_headers(), timeout=6)
                data = r.json()
                if isinstance(data, list) and len(data) > 1:
                    for suggestion in data[1]:
                        results.add(suggestion.strip())
            except Exception as e:
                logger.debug(f"[KEYWORDS] Autosuggest failed for '{term}': {e}")
            time.sleep(0.3)
        logger.info(f"[KEYWORDS] Autosuggest → {len(results)} suggestions for '{keyword}'")
        return list(results)

    def expand_with_variations(self, base_kw):
        results = set()
        for prefix in self.COMMERCIAL_PREFIXES:
            results.add(f"{prefix} {base_kw}")
        for suffix in self.COMMERCIAL_SUFFIXES:
            results.add(f"{base_kw} {suffix}")
        for modifier in self.INTENT_MODIFIERS:
            results.add(f"{modifier} {base_kw}")
        base_lower = base_kw.lower()
        for niche_key, mods in self.NICHE_MODIFIERS.items():
            if niche_key in base_lower:
                for mod in mods:
                    results.add(mod)
                    for prefix in self.COMMERCIAL_PREFIXES[:5]:
                        results.add(f"{prefix} {mod}")
        logger.info(f"[KEYWORDS] Expansion → {len(results)} variants for '{base_kw}'")
        return list(results)

    def ai_generate(self, base_kw, location, used_kws):
        fallback = self.expand_with_variations(base_kw)
        if not GROQ_API_KEY:
            return fallback
        try:
            client = Groq(api_key=GROQ_API_KEY)
            prompt = (
                f'You are a local SEO expert. Seed keyword: "{base_kw}". Location: "{location}". '
                f'Already used: {list(used_kws)[:20]}. '
                f'Generate 120 unique search terms a customer would type into Google. '
                f'Include service variations, problem-based terms, niche subcategories, local intent, '
                f'review-seeking terms. Return ONLY a comma-separated list. No numbering, no explanation.'
            )
            res = client.chat.completions.create(
                messages=[{"role": "user", "content": prompt}],
                model="llama3-8b-8192",
                temperature=0.8,
                max_tokens=2000,
            )
            text = res.choices[0].message.content
            ai_kws = [k.strip().strip('"').strip("'") for k in text.split(',')
                      if k.strip() and k.strip().lower() not in used_kws]
            combined = list(set(ai_kws + fallback))
            logger.info(f"[KEYWORDS] AI → {len(combined)} keywords total")
            return combined
        except Exception as e:
            logger.warning(f"[KEYWORDS] AI generation failed: {e} — using fallback")
            return fallback

    def generate_full_pool(self, base_kw, location, used_kws):
        all_kws = set()
        all_kws.update(self.ai_generate(base_kw, location, used_kws))
        all_kws.update(self.google_autosuggest(base_kw, location))
        all_kws.update(self.expand_with_variations(base_kw))
        final = [k for k in all_kws if k.lower() not in used_kws and len(k) > 3]
        if len(final) < 100:
            for p in self.COMMERCIAL_PREFIXES:
                final.append(f"{p} {base_kw}")
        final = list(set(final))
        logger.info(f"[KEYWORDS] Full pool → {len(final)} unique keywords for '{base_kw}'")
        return final


# ════════════════════════════════════════════════════
#   WEBSITE VALIDATOR
#   Ensures we never store Maps/DDG/aggregator URLs
# ════════════════════════════════════════════════════
# Domains that are NEVER valid business websites
_WEBSITE_BLACKLIST = (
    'google.com', 'google.co', 'maps.google', 'goo.gl',
    'duckduckgo.com', 'bing.com', 'yahoo.com',
    'facebook.com', 'fb.com', 'instagram.com', 'twitter.com',
    'linkedin.com', 'youtube.com', 'tiktok.com',
    'yelp.com', 'tripadvisor.com', 'foursquare.com',
    'bbb.org', 'yellowpages.com', 'whitepages.com',
    'angi.com', 'thumbtack.com', 'houzz.com',
    'zillow.com', 'realtor.com', 'trulia.com',
    'amazon.com', 'ebay.com', 'etsy.com',
    'wikipedia.org', 'wikimedia.org',
)

def is_valid_business_website(url: str) -> bool:
    """
    Returns True only if the URL is a real business domain.
    Rejects Maps links, aggregators, social media, search engines.
    """
    if not url or url == "N/A":
        return False
    if not url.startswith('http'):
        return False
    url_lower = url.lower()
    if any(bl in url_lower for bl in _WEBSITE_BLACKLIST):
        return False
    # Must have a valid TLD
    try:
        parsed = urllib.parse.urlparse(url_lower)
        host = parsed.netloc
        if not host or '.' not in host:
            return False
        # reject IP addresses as business websites
        if re.match(r'^\d+\.\d+\.\d+\.\d+', host):
            return False
        return True
    except:
        return False


# ════════════════════════════════════════════════════
#   COMPLETE SCRAPER  — REBUILT FROM SCRATCH
#
#   Strategies (in order of reliability on server IPs):
#   A. Yelp search  — HTML rendered, no JS needed, rich data
#   B. Google search with "site:yelp.com" exclusion
#      using tbm=lcl — works when not blocked
#   C. Bing Maps search — HTML rendered, reliable
#   D. Google organic search for local businesses
#
#   For each business found, a 4-stage website resolver
#   guarantees we get a real domain, not a Maps/DDG link.
# ════════════════════════════════════════════════════
class GoogleMapsScraper:
    MAX_RETRIES = 2
    RETRY_DELAY = 1.5

    # ── STRATEGY A: Yelp search (most reliable HTML source) ─────────
    def _scrape_yelp(self, keyword: str, location: str) -> list:
        """
        Yelp's search page is rendered HTML (no JS required).
        Each result card contains: name, rating, review count, website, phone.
        Supports pagination via &start= parameter.
        """
        results = []
        seen = set()

        for page_start in [0, 10, 20, 30]:   # 4 pages × ~10 results = 40 businesses
            query = urllib.parse.quote_plus(keyword)
            loc   = urllib.parse.quote_plus(location)
            url   = f"https://www.yelp.com/search?find_desc={query}&find_loc={loc}&start={page_start}"

            for attempt in range(1, self.MAX_RETRIES + 1):
                try:
                    resp = requests.get(url, headers=get_headers(), timeout=14, verify=False)
                    logger.info(f"[YELP] page_start={page_start} HTTP {resp.status_code} ({len(resp.text)} chars)")
                    if resp.status_code != 200:
                        time.sleep(self.RETRY_DELAY * attempt)
                        continue

                    soup = BeautifulSoup(resp.text, 'html.parser')

                    # ── Primary selectors for Yelp result cards ──
                    cards = soup.select(
                        'div[class*="businessName"], '
                        'h3[class*="businessName"], '
                        'li[class*="businessListItem"], '
                        'div.arrange-unit__373c0__1piwO, '
                        'div[data-testid*="serp-ia-card"]'
                    )

                    # ── Fallback: any link that goes to /biz/ ──
                    if not cards:
                        biz_links = soup.select('a[href*="/biz/"]')
                        logger.info(f"[YELP] page_start={page_start} — primary cards=0, biz_links={len(biz_links)}")
                        for link in biz_links[:15]:
                            try:
                                name = link.get_text(strip=True)
                                if not name or len(name) < 3 or name in seen:
                                    continue
                                # Skip navigation/category links
                                if any(skip in name.lower() for skip in
                                       ['more', 'see all', 'write a review', 'add photo', 'directions']):
                                    continue
                                seen.add(name)
                                biz_url = 'https://www.yelp.com' + link['href'] if link['href'].startswith('/') else link['href']
                                results.append({
                                    "Name":        name,
                                    "Phone":       "N/A",
                                    "Website":     "N/A",   # resolved later by website_resolver
                                    "Rating":      "N/A",
                                    "ReviewCount": "0",
                                    "Address":     location,
                                    "Category":    keyword,
                                    "Maps_Link":   biz_url,
                                    "_yelp_url":   biz_url,  # internal: used by website_resolver
                                })
                            except:
                                pass
                        break  # don't retry if we got fallback results

                    logger.info(f"[YELP] page_start={page_start} — {len(cards)} cards")

                    for card in cards:
                        try:
                            # Name
                            name_el = card.select_one(
                                'a[class*="businessName"], span[class*="businessName"], '
                                'h3 a, h4 a, [class*="biz-name"]'
                            )
                            name = name_el.get_text(strip=True) if name_el else card.get_text(strip=True)[:80]
                            # Strip leading numbers like "1. Business Name"
                            name = re.sub(r'^\d+\.\s*', '', name).strip()
                            if not name or len(name) < 3 or name in seen:
                                continue
                            seen.add(name)

                            text = card.get_text(separator=' ', strip=True)

                            # Rating
                            rating = "N/A"
                            rm = re.search(r'\b([1-5][.,]\d)\b', text)
                            if rm:
                                rv = rm.group(1).replace(',', '.')
                                try:
                                    if 1.0 <= float(rv) <= 5.0:
                                        rating = rv
                                except:
                                    pass

                            # Review count
                            review_count = "0"
                            rc = re.search(r'(\d+)\s+review', text, re.IGNORECASE)
                            if rc:
                                review_count = rc.group(1)

                            # Phone
                            phone = "N/A"
                            ph = re.search(r'(\(?\d{3}\)?[\s.\-]\d{3}[\s.\-]\d{4})', text)
                            if ph:
                                phone = ph.group(0).strip()

                            # Yelp business URL for detail scraping
                            biz_url = "N/A"
                            biz_link = card.select_one('a[href*="/biz/"]')
                            if biz_link:
                                href = biz_link.get('href', '')
                                biz_url = ('https://www.yelp.com' + href
                                           if href.startswith('/') else href)

                            results.append({
                                "Name":        name,
                                "Phone":       phone,
                                "Website":     "N/A",   # resolved by website_resolver
                                "Rating":      rating,
                                "ReviewCount": review_count,
                                "Address":     location,
                                "Category":    keyword,
                                "Maps_Link":   biz_url,
                                "_yelp_url":   biz_url,
                            })
                        except Exception as e:
                            logger.debug(f"[YELP] Card parse error: {e}")
                    break  # success, no more retries needed

                except requests.exceptions.RequestException as e:
                    logger.warning(f"[YELP] Request error page_start={page_start} attempt={attempt}: {e}")
                    time.sleep(self.RETRY_DELAY * attempt)

            time.sleep(random.uniform(0.8, 1.5))

        logger.info(f"[YELP] Total extracted: {len(results)} businesses")
        return results

    # ── STRATEGY B: Google Local search (tbm=lcl) ────────────────────
    def _scrape_google_local(self, keyword: str, location: str) -> list:
        """
        Google's tbm=lcl local results. Works when not blocked.
        Multiple offsets to get 60+ results.
        """
        query = urllib.parse.quote_plus(f"{keyword} {location}")
        all_results = []

        def fetch_offset(start: int) -> list:
            url = f"https://www.google.com/search?q={query}&tbm=lcl&start={start}&num=20&hl=en&gl=us"
            for attempt in range(1, self.MAX_RETRIES + 1):
                try:
                    resp = requests.get(url, headers=get_headers(), timeout=12, verify=False)
                    logger.info(f"[LCL] offset={start} HTTP {resp.status_code}")
                    if resp.status_code != 200:
                        time.sleep(self.RETRY_DELAY * attempt)
                        continue

                    soup = BeautifulSoup(resp.text, 'html.parser')
                    blocks = soup.select(
                        'div.VkpGBb, div.rllt__details, div.uMdZh, div.cXedhc, '
                        'div.lqhpac, div[data-cid], div.rl_tit, li.rllt__list-item, '
                        'div[class*="rllt"]'
                    )
                    logger.info(f"[LCL] offset={start} blocks={len(blocks)}")

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
                                t = el.get_text(strip=True) if hasattr(el, 'get_text') else ''
                                if 3 < len(t) < 80:
                                    name = t; break
                        if name == "N/A" or len(name) < 3:
                            continue

                        rating = "N/A"
                        rm = re.search(r'\b([1-5][.,]\d)\b', text)
                        if rm:
                            rv = rm.group(1).replace(',', '.')
                            try:
                                if 1.0 <= float(rv) <= 5.0: rating = rv
                            except: pass

                        review_count = "0"
                        rc = re.search(r'\((\d{1,6})\)', text)
                        if rc: review_count = rc.group(1)

                        phone = "N/A"
                        ph = re.search(r'(\+?1?\s*\(?\d{3}\)?[\s.\-]\d{3}[\s.\-]\d{4})', text)
                        if ph: phone = ph.group(0).strip()

                        # Website from listing links (NOT Maps links)
                        website = "N/A"
                        for a in block.select('a[href]'):
                            href = a.get('href', '')
                            if '/url?q=' in href:
                                clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                                if is_valid_business_website(clean):
                                    website = clean; break
                            elif href.startswith('http') and is_valid_business_website(href):
                                website = href; break

                        batch.append({
                            "Name":        name,
                            "Phone":       phone,
                            "Website":     website,
                            "Rating":      rating,
                            "ReviewCount": review_count,
                            "Address":     location,
                            "Category":    keyword,
                            "Maps_Link":   f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/",
                        })
                    logger.info(f"[LCL] offset={start} → {len(batch)} parsed")
                    return batch

                except requests.exceptions.RequestException as e:
                    logger.warning(f"[LCL] Request error offset={start} attempt={attempt}: {e}")
                    time.sleep(self.RETRY_DELAY * attempt)
                except Exception as e:
                    logger.error(f"[LCL] Unexpected error offset={start}: {e}")
                    break
            return []

        with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:
            futures = {ex.submit(fetch_offset, s): s for s in [0, 20, 40, 60, 80]}
            for f in concurrent.futures.as_completed(futures):
                try:
                    all_results.extend(f.result())
                except Exception as e:
                    logger.error(f"[LCL] Thread error: {e}")

        logger.info(f"[LCL] Total: {len(all_results)} businesses")
        return all_results

    # ── STRATEGY C: Bing local search ────────────────────────────────
    def _scrape_bing_local(self, keyword: str, location: str) -> list:
        """
        Bing's HTML local results — reliable on server IPs.
        """
        results = []
        seen = set()
        query = urllib.parse.quote_plus(f"{keyword} near {location}")
        url = f"https://www.bing.com/search?q={query}&first=1&count=30&setlang=en"

        try:
            resp = requests.get(url, headers=get_headers(), timeout=12, verify=False)
            logger.info(f"[BING] HTTP {resp.status_code} ({len(resp.text)} chars)")
            if resp.status_code != 200:
                return results

            soup = BeautifulSoup(resp.text, 'html.parser')

            # Bing local pack
            local_cards = soup.select(
                'div.b_entityTP, div[class*="local-pack"], '
                'li[class*="b_ans"], div.b_lclCard, '
                'div[data-idx], li.b_ans div[class*="lc"]'
            )
            logger.info(f"[BING] {len(local_cards)} local cards")

            for card in local_cards[:30]:
                try:
                    text = card.get_text(separator=' ', strip=True)
                    name_el = card.select_one(
                        'h2, h3, .b_entityTitle, [class*="title"], '
                        'a[class*="tilk"], .b_lclName'
                    )
                    name = name_el.get_text(strip=True) if name_el else "N/A"
                    if not name or len(name) < 3 or name in seen:
                        continue
                    seen.add(name)

                    rating = "N/A"
                    rm = re.search(r'\b([1-5][.,]\d)\b', text)
                    if rm:
                        rv = rm.group(1).replace(',', '.')
                        try:
                            if 1.0 <= float(rv) <= 5.0: rating = rv
                        except: pass

                    review_count = "0"
                    rc = re.search(r'(\d+)\s+(?:review|Rating)', text, re.IGNORECASE)
                    if rc: review_count = rc.group(1)

                    phone = "N/A"
                    ph = re.search(r'(\(?\d{3}\)?[\s.\-]\d{3}[\s.\-]\d{4})', text)
                    if ph: phone = ph.group(0).strip()

                    website = "N/A"
                    for a in card.select('a[href]'):
                        href = a.get('href', '')
                        if is_valid_business_website(href):
                            website = href; break

                    results.append({
                        "Name":        name,
                        "Phone":       phone,
                        "Website":     website,
                        "Rating":      rating,
                        "ReviewCount": review_count,
                        "Address":     location,
                        "Category":    keyword,
                        "Maps_Link":   f"https://www.bing.com/maps?q={urllib.parse.quote_plus(name + ' ' + location)}",
                    })
                except Exception as e:
                    logger.debug(f"[BING] Card error: {e}")

            # ── Also scrape organic Bing results for more businesses ──
            organic = soup.select('li.b_algo')
            logger.info(f"[BING] {len(organic)} organic results")
            for item in organic[:20]:
                try:
                    name_el = item.select_one('h2 a, h3 a')
                    if not name_el: continue
                    name = name_el.get_text(strip=True)
                    if not name or len(name) < 3 or name in seen: continue
                    seen.add(name)

                    href = name_el.get('href', '')
                    website = href if is_valid_business_website(href) else "N/A"
                    text = item.get_text(separator=' ', strip=True)
                    rating = "N/A"
                    rm = re.search(r'\b([1-5][.,]\d)\b', text)
                    if rm:
                        rv = rm.group(1).replace(',', '.')
                        try:
                            if 1.0 <= float(rv) <= 5.0: rating = rv
                        except: pass

                    results.append({
                        "Name":        name,
                        "Phone":       "N/A",
                        "Website":     website,
                        "Rating":      rating,
                        "ReviewCount": "0",
                        "Address":     location,
                        "Category":    keyword,
                        "Maps_Link":   f"https://www.bing.com/maps?q={urllib.parse.quote_plus(name + ' ' + location)}",
                    })
                except: pass

        except Exception as e:
            logger.warning(f"[BING] Error: {e}")

        logger.info(f"[BING] Total: {len(results)} businesses")
        return results

    # ── WEBSITE RESOLVER — 4 stages ──────────────────────────────────
    def resolve_website(self, business_name: str, location: str,
                        existing_url: str = "N/A",
                        yelp_url: str = "N/A") -> str:
        """
        4-stage website resolution. Returns a validated business domain.

        Stage 1: Validate existing URL from scraper (if any)
        Stage 2: Scrape Yelp business page for external website link
        Stage 3: Google search "business name location official website"
        Stage 4: Bing search fallback
        """
        # ── Stage 1: Validate what we already have ──
        if is_valid_business_website(existing_url):
            logger.debug(f"[WEBSITE] Stage1 OK for '{business_name}': {existing_url}")
            return existing_url

        # ── Stage 2: Yelp business detail page ──
        if yelp_url and yelp_url != "N/A" and "yelp.com/biz/" in yelp_url:
            try:
                resp = requests.get(yelp_url, headers=get_headers(), timeout=10, verify=False)
                if resp.status_code == 200:
                    soup = BeautifulSoup(resp.text, 'html.parser')
                    # Yelp shows external website as a link with rel="noopener"
                    for a in soup.select('a[href][target="_blank"]'):
                        href = a.get('href', '')
                        # Yelp wraps external links through biz_redirect
                        if 'biz_redir' in href or 'redirect_url' in href:
                            parsed = urllib.parse.parse_qs(urllib.parse.urlparse(href).query)
                            url_val = parsed.get('url', [None])[0] or parsed.get('redirect_url', [None])[0]
                            if url_val and is_valid_business_website(urllib.parse.unquote(url_val)):
                                logger.info(f"[WEBSITE] Stage2 (Yelp) for '{business_name}': {url_val}")
                                return urllib.parse.unquote(url_val)
                        if is_valid_business_website(href):
                            logger.info(f"[WEBSITE] Stage2 (Yelp direct) for '{business_name}': {href}")
                            return href
                    # Also check structured JSON-LD on yelp page
                    for script in soup.find_all('script', type='application/ld+json'):
                        try:
                            d = json.loads(script.string or '')
                            items = d if isinstance(d, list) else [d]
                            for item in items:
                                u = item.get('url', '')
                                if is_valid_business_website(u) and 'yelp' not in u.lower():
                                    logger.info(f"[WEBSITE] Stage2 (Yelp JSON-LD) for '{business_name}': {u}")
                                    return u
                        except: pass
            except Exception as e:
                logger.debug(f"[WEBSITE] Stage2 Yelp failed for '{business_name}': {e}")

        # ── Stage 3: Google search ──
        for search_query in [
            f'"{business_name}" {location} official website',
            f'{business_name} {location} contact',
        ]:
            try:
                url = f"https://www.google.com/search?q={urllib.parse.quote_plus(search_query)}&num=5&hl=en"
                resp = requests.get(url, headers=get_headers(), timeout=8, verify=False)
                soup = BeautifulSoup(resp.text, 'html.parser')
                for a in soup.select('a[href]'):
                    href = a.get('href', '')
                    if '/url?q=' in href:
                        clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                        if is_valid_business_website(clean):
                            logger.info(f"[WEBSITE] Stage3 (Google) for '{business_name}': {clean}")
                            return clean
                    elif is_valid_business_website(href):
                        logger.info(f"[WEBSITE] Stage3 (Google direct) for '{business_name}': {href}")
                        return href
            except Exception as e:
                logger.debug(f"[WEBSITE] Stage3 Google failed for '{business_name}': {e}")
            time.sleep(0.5)

        # ── Stage 4: Bing search fallback ──
        try:
            bq = urllib.parse.quote_plus(f"{business_name} {location} website")
            url = f"https://www.bing.com/search?q={bq}&count=5"
            resp = requests.get(url, headers=get_headers(), timeout=8, verify=False)
            soup = BeautifulSoup(resp.text, 'html.parser')
            for a in soup.select('li.b_algo h2 a, li.b_algo a.tilk'):
                href = a.get('href', '')
                if is_valid_business_website(href):
                    logger.info(f"[WEBSITE] Stage4 (Bing) for '{business_name}': {href}")
                    return href
        except Exception as e:
            logger.debug(f"[WEBSITE] Stage4 Bing failed for '{business_name}': {e}")

        logger.info(f"[WEBSITE] All stages failed for '{business_name}'")
        return "N/A"

    # ── Master fetch_batch ────────────────────────────────────────────
    def fetch_batch(self, keyword: str, location: str) -> list:
        """
        CORRECT FLOW:
        1. Yelp (primary — HTML, no JS, rich data)
        2. Google Local tbm=lcl (secondary)
        3. Bing (tertiary / gap-filler)
        Merge → deduplicate by name → sort bad-rating-first.
        """
        logger.info(f"[SCRAPE] ═══ Starting: '{keyword}' in '{location}' ═══")
        all_leads = []

        # Strategy A: Yelp
        yelp = self._scrape_yelp(keyword, location)
        logger.info(f"[SCRAPE] Yelp → {len(yelp)}")
        all_leads.extend(yelp)

        # Strategy B: Google Local
        gcl = self._scrape_google_local(keyword, location)
        logger.info(f"[SCRAPE] Google Local → {len(gcl)}")
        all_leads.extend(gcl)

        # Strategy C: Bing (always — fills gaps when Google is blocked)
        bing = self._scrape_bing_local(keyword, location)
        logger.info(f"[SCRAPE] Bing → {len(bing)}")
        all_leads.extend(bing)

        # Deduplicate by name
        seen = set()
        unique = []
        for lead in all_leads:
            key = lead["Name"].strip().lower()
            if key and key != "n/a" and len(key) > 2 and key not in seen:
                seen.add(key)
                unique.append(lead)

        # Sort: lowest rating first (bad businesses first)
        def sort_key(lead):
            try:
                return float(lead["Rating"])
            except:
                return 6.0
        unique.sort(key=sort_key)

        logger.info(f"[SCRAPE] ✅ TOTAL: {len(all_leads)} raw → {len(unique)} unique")
        return unique

    # find_website_via_search preserved as wrapper to resolve_website
    def find_website_via_search(self, business_name: str, location: str) -> str:
        return self.resolve_website(business_name, location, "N/A", "N/A")


# ════════════════════════════════════════════════════
#   DEEP EMAIL EXTRACTOR  (UNCHANGED — PRESERVED)
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

    def crawl_page(self, url: str, timeout: int = 8) -> str:
        try:
            r = requests.get(url, headers=get_headers(), timeout=timeout,
                             verify=False, allow_redirects=True)
            if r.status_code == 200:
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
                            logger.debug(f"[EMAIL] Found on internal page {link}: {emails2[0]}")
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
#   AI KEYWORD GENERATOR  (ORIGINAL — PRESERVED)
# ════════════════════════════════════════════════════
def generate_ai_keywords(base_kw, location, used_kws):
    fallback = [
        f"best {base_kw}", f"top {base_kw}", f"{base_kw} services",
        f"affordable {base_kw}", f"{base_kw} agency", f"{base_kw} near me",
        f"{base_kw} company", f"{base_kw} experts",
    ]
    if not GROQ_API_KEY:
        return fallback
    try:
        client = Groq(api_key=GROQ_API_KEY)
        prompt = (
            f'I am searching for "{base_kw}" in "{location}". '
            f'Used keywords: {list(used_kws)}. '
            f'Generate 100 NEW, highly related search terms/categories. '
            f'Return ONLY a comma-separated list.'
        )
        res = client.chat.completions.create(
            messages=[{"role": "user", "content": prompt}],
            model="llama3-8b-8192",
            temperature=0.7,
        )
        text = res.choices[0].message.content
        new_kws = [
            k.strip() for k in text.split(',')
            if k.strip() and k.strip().lower() not in used_kws
        ]
        return new_kws if new_kws else fallback
    except Exception as e:
        logger.warning(f"[KEYWORDS] generate_ai_keywords failed: {e}")
        return fallback


# ════════════════════════════════════════════════════
#   AI EMAIL PERSONALIZER  (ORIGINAL — PRESERVED)
# ════════════════════════════════════════════════════
def personalize_email(lead_name, niche, template_subject, template_body, rating):
    if not GROQ_API_KEY:
        return template_subject, template_body, ""
    try:
        client = Groq(api_key=GROQ_API_KEY)
        prompt = f"""You are an expert cold email copywriter. Personalize this email for a business.
Business Name: {lead_name}
Niche: {niche}
Current Rating: {rating} (If below 4.0, mention helping them improve it. If high, compliment it).
Original Subject: {template_subject}
Original Body: {template_body}

Return ONLY a valid JSON object with keys:
"subject" (personalized subject),
"body" (personalized HTML body),
"personalization_line" (A single, highly personalized opening sentence based on their business and rating)."""
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
#   MASTER JOB RUNNER  (CORRECT FLOW — PRESERVED)
# ════════════════════════════════════════════════════
def run_job_thread(job_id: str, data: dict):
    try:
        location     = data.get('location', '').strip()
        base_keyword = data.get('keyword', '').strip()
        max_leads    = min(int(data.get('max_leads', 10)), 200)
        max_rating   = data.get('max_rating')
        webhook_url    = data.get('webhook_url', '') or get_settings().get('webhook_url', '')
        db_webhook_url = data.get('db_webhook_url', '') or get_settings().get('db_webhook_url', '')
        templates      = data.get('templates', []) or get_settings().get('templates', [])

        max_rating_float = None
        if max_rating:
            try:
                max_rating_float = float(str(max_rating).replace(',', '.'))
                logger.info(f"[JOB] Rating filter: rating <= {max_rating_float}")
            except:
                logger.warning(f"[JOB] Invalid max_rating '{max_rating}' — filter disabled")

        maps_scraper = GoogleMapsScraper()
        email_lib    = DeepEmailExtractor()
        kw_engine    = AdvancedKeywordEngine()
        db           = GoogleSheetsDB(db_webhook_url)
        dedup        = DeduplicationStore()

        jobs[job_id] = {
            'status':        'scraping',
            'count':         0,
            'leads':         [],
            'emails_sent':   0,
            'total_to_send': 0,
            'status_text':   f'Starting scrape: {base_keyword} in {location}...',
            'stats': {
                'scraped_total':       0,
                'after_rating_filter': 0,
                'duplicates_skipped':  0,
                'emails_found':        0,
                'errors':              0,
                'keywords_used':       0,
                'keywords_generated':  0,
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

        used_keywords = set()

        # ── FIX 2: ONE-keyword-at-a-time keyword pool ─────────────────
        # We start with just the base keyword. After it is fully processed
        # we check whether the target is met. If not, we generate EXACTLY
        # ONE new keyword, process it fully, check again — and so on.
        # We never dump 100+ keywords into the queue at once.
        # _keyword_pool holds the pre-generated list; we pop ONE at a time.
        _keyword_pool: list = []    # pool of future keywords (filled lazily)
        _pool_built    = False      # whether we've built the expansion pool yet

        def _next_keyword() -> str:
            """Return the next keyword to scrape (one at a time). Never empty."""
            nonlocal _pool_built

            # First: try unused items in the pool
            while _keyword_pool:
                kw = _keyword_pool.pop(0)
                if kw.lower() not in used_keywords:
                    return kw

            # Pool exhausted — build/rebuild it (one-shot expansion)
            if not _pool_built:
                logger.info(f"[KW] Building keyword expansion pool for '{base_keyword}'")
                jobs[job_id]['status_text'] = f"Generating next keyword for '{base_keyword}'..."
                # Use full pool builder but store all in _keyword_pool;
                # the caller pops ONE at a time each iteration.
                new_kws = kw_engine.generate_full_pool(base_keyword, location, used_keywords)
                _pool_built = True
            else:
                logger.info(f"[KW] Re-generating keywords for '{base_keyword}'")
                jobs[job_id]['status_text'] = f"Re-generating next keyword..."
                new_kws = generate_ai_keywords(base_keyword, location, used_keywords)

            random.shuffle(new_kws)
            fresh = [k for k in new_kws if k.lower() not in used_keywords]
            _keyword_pool.extend(fresh)
            jobs[job_id]['stats']['keywords_generated'] += len(fresh)

            # Log all generated keywords to DB
            for kw in fresh:
                db.send_action("add_keyword", {
                    "keyword": kw, "source_seed": base_keyword, "status": "pending"
                })

            # Return first unused keyword from rebuilt pool
            while _keyword_pool:
                kw = _keyword_pool.pop(0)
                if kw.lower() not in used_keywords:
                    return kw

            # Absolute fallback: derive a variation on the fly
            fallback_kw = f"top {base_keyword} {location}"
            logger.warning(f"[KW] Pool empty, using fallback: '{fallback_kw}'")
            return fallback_kw

        def _process_lead_batch(raw_leads: list, current_kw: str) -> bool:
            """
            Process one batch of scraped businesses.
            FIX 4: Google Maps URL stored for every business.
            FIX 5: Duplicate check against email/website/name BEFORE saving to Qualified.
            FIX 6: Full business data (name, phone, address, rating, review_count,
                   website, email, maps_url, keyword) stored in every DB action.
            Returns True when the lead target is met.
            """
            jobs[job_id]['stats']['scraped_total'] += len(raw_leads)
            logger.info(f"[JOB] Processing {len(raw_leads)} businesses from '{current_kw}'")

            for lead in raw_leads:
                if len(jobs[job_id]['leads']) >= max_leads:
                    logger.info(f"[JOB] 🎯 TARGET {max_leads} reached — stopping")
                    return True

                # ── FIX 4: Build canonical Google Maps URL for every business ──
                maps_url = lead.get('Maps_Link') or (
                    f"https://www.google.com/maps/search/"
                    f"{urllib.parse.quote_plus(lead['Name'] + ' ' + location)}/"
                )
                lead['Maps_Link'] = maps_url  # ensure it's always set

                logger.info(
                    f"[JOB] Business: '{lead['Name']}' | "
                    f"rating={lead['Rating']} | website={lead['Website']} | maps={maps_url}"
                )

                # ── FIX 6: Save raw to DB with ALL fields including Maps URL ──
                db.send_action("add_scraped", {
                    "business_name": lead['Name'],
                    "address":       lead['Address'],
                    "phone":         lead['Phone'],
                    "rating":        lead['Rating'],
                    "review_count":  lead.get('ReviewCount', 'N/A'),
                    "website":       lead['Website'],
                    "maps_url":      maps_url,          # FIX 4: maps URL in raw record
                    "keyword":       current_kw,
                    "status":        "scraped",
                })

                # Rating filter
                if max_rating_float is not None and lead['Rating'] != "N/A":
                    try:
                        r_val = float(lead['Rating'])
                        if r_val > max_rating_float:
                            logger.info(f"[FILTER] ❌ Skipped '{lead['Name']}' rating={r_val} > {max_rating_float}")
                            continue
                        logger.info(f"[FILTER] ✅ Accepted '{lead['Name']}' rating={r_val}")
                    except ValueError:
                        pass

                jobs[job_id]['stats']['after_rating_filter'] += 1

                # ── FIX 1: Website resolution (4-stage aggressive) ──────────
                # Stage 1 — already in the lead dict (from scraper)
                # Stage 2 — Yelp detail page
                # Stage 3 — Google search
                # Stage 4 — Bing search
                existing_url = lead.get('Website', 'N/A')
                yelp_url     = lead.get('_yelp_url', 'N/A')

                if is_valid_business_website(existing_url):
                    website = existing_url
                    logger.info(f"[WEBSITE] Stage1 OK for '{lead['Name']}': {website}")
                else:
                    jobs[job_id]['status_text'] = f"Resolving website for: {lead['Name']}..."
                    # resolve_website tries Yelp detail → Google → Bing
                    website = maps_scraper.resolve_website(
                        lead['Name'], location, existing_url, yelp_url
                    )
                    lead['Website'] = website

                if not is_valid_business_website(website):
                    logger.info(f"[WEBSITE] ❌ No valid website for '{lead['Name']}' — skipping")
                    continue

                # ── FIX 5: Pre-email duplicate check (name + website + email="") ──
                # Catches same business appearing under different keywords
                if dedup.is_duplicate(lead['Name'], website, ""):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] Pre-email dup skipped: '{lead['Name']}'")
                    continue

                # Email extraction
                jobs[job_id]['status_text'] = f"Extracting email: {lead['Name']}..."
                extracted_email = email_lib.get_email(website)

                if extracted_email == "N/A":
                    logger.info(f"[EMAIL] ❌ No email at {website}")
                    continue

                jobs[job_id]['stats']['emails_found'] += 1
                logger.info(f"[EMAIL] ✅ {extracted_email} for '{lead['Name']}'")

                # ── FIX 5: Post-email duplicate check (email as primary key) ──
                # Prevents same email from being saved twice via different keywords
                if dedup.is_duplicate(lead['Name'], website, extracted_email):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] Post-email dup skipped: '{lead['Name']}' / {extracted_email}")
                    continue

                # Register in dedup store
                dedup.register(lead['Name'], website, extracted_email)

                # ── FIX 5 + FIX 6: Save to Qualified Leads with ALL fields ──
                # Duplicate guard already passed — this lead is unique.
                db.send_action("add_email_lead", {
                    "business_name": lead['Name'],
                    "website":       website,
                    "email":         extracted_email,
                    "source_page":   website,
                    "status":        "qualified",
                })
                # FIX 6: Full data in Qualified_Leads sheet
                db.send_action("add_qualified", {
                    "business_name": lead['Name'],
                    "email":         extracted_email,
                    "website":       website,
                    "phone":         lead.get('Phone', 'N/A'),
                    "address":       lead.get('Address', 'N/A'),
                    "rating":        lead.get('Rating', 'N/A'),
                    "review_count":  lead.get('ReviewCount', 'N/A'),
                    "maps_url":      maps_url,              # FIX 4: maps URL in qualified record
                    "keyword":       current_kw,
                    "personalization_line": "Pending AI...",
                    "email_sent":    "no",
                })

                lead['Email'] = extracted_email
                jobs[job_id]['leads'].append(lead)
                jobs[job_id]['count'] = len(jobs[job_id]['leads'])
                jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped

                logger.info(
                    f"[LEAD] ✅ #{jobs[job_id]['count']}/{max_leads} "
                    f"'{lead['Name']}' | {extracted_email} | maps={maps_url}"
                )
                jobs[job_id]['status_text'] = (
                    f"✅ {jobs[job_id]['count']}/{max_leads} leads — "
                    f"latest: {lead['Name']}"
                )

                if len(jobs[job_id]['leads']) >= max_leads:
                    return True

            return False

        # ── FIX 2: MAIN LOOP — one keyword at a time ─────────────────
        # Correct flow:
        #   1. Scrape base keyword first (no expansion yet)
        #   2. Process all leads from that keyword
        #   3. Check target → if met: STOP
        #   4. Generate ONE new keyword → scrape → check → repeat
        current_keyword = base_keyword  # always start with user's keyword

        while len(jobs[job_id]['leads']) < max_leads:
            used_keywords.add(current_keyword.lower())
            jobs[job_id]['stats']['keywords_used'] += 1

            jobs[job_id]['status_text'] = f"Scraping: '{current_keyword}' in '{location}'..."
            logger.info(
                f"[JOB] ── Keyword #{jobs[job_id]['stats']['keywords_used']}: "
                f"'{current_keyword}' | leads so far: {len(jobs[job_id]['leads'])}/{max_leads}"
            )

            raw_leads = maps_scraper.fetch_batch(current_keyword, location)

            if not raw_leads:
                logger.info(f"[JOB] No results for '{current_keyword}' — fetching next keyword")
            else:
                logger.info(f"[JOB] Businesses found: {len(raw_leads)}")
                target_reached = _process_lead_batch(raw_leads, current_keyword)

                if target_reached:
                    logger.info(f"[JOB] STOP: target {max_leads} reached")
                    break

            logger.info(f"[JOB] Qualified: {len(jobs[job_id]['leads'])}/{max_leads} — fetching next single keyword")

            # ── FIX 2: Generate ONLY ONE new keyword before next iteration ──
            current_keyword = _next_keyword()
            time.sleep(random.uniform(1.0, 2.0))

        # Final stats
        s = jobs[job_id]['stats']
        final_count = len(jobs[job_id]['leads'])
        logger.info(
            f"[JOB] COMPLETE — scraped={s['scraped_total']} "
            f"after_filter={s['after_rating_filter']} emails={s['emails_found']} "
            f"dupes={s['duplicates_skipped']} kw_used={s['keywords_used']} "
            f"final_leads={final_count}"
        )
        db.send_action("update_config", {
            "keyword_seed": base_keyword, "location": location,
            "target_leads": max_leads, "min_rating": "",
            "max_rating": max_rating or "", "email_required": "true", "status": "stopped",
        })
        db.log("Scraping Done", f"Qualified: {final_count}")
        final_leads = jobs[job_id]['leads']

        # Phase 2: Email sending
        if webhook_url and templates and final_leads:
            jobs[job_id]['status'] = 'sending_emails'
            jobs[job_id]['total_to_send'] = len(final_leads)
            emails_sent = 0
            for lead in final_leads:
                jobs[job_id]['status_text'] = f"Sending {emails_sent+1}/{len(final_leads)} → {lead['Email']}"
                template = random.choice(templates)
                p_subject, p_body, p_line = personalize_email(
                    lead['Name'], base_keyword, template['subject'], template['body'], lead['Rating']
                )
                try:
                    requests.post(webhook_url, json={"to": lead['Email'], "subject": p_subject, "body": p_body}, timeout=10)
                    emails_sent += 1
                    jobs[job_id]['emails_sent'] = emails_sent
                    db.send_action("update_email_sent", {"email": lead['Email'], "personalization_line": p_line})
                    db.log("Email Sent", f"→ {lead['Email']}")
                except Exception as e:
                    jobs[job_id]['stats']['errors'] += 1
                    logger.error(f"[EMAIL-SEND] Failed → {lead['Email']}: {e}")
                if emails_sent < len(final_leads):
                    delay = random.randint(60, 120)
                    for i in range(delay, 0, -1):
                        jobs[job_id]['status_text'] = f"Cooldown: {i}s..."
                        time.sleep(1)

        jobs[job_id]['status'] = 'done'
        jobs[job_id]['status_text'] = f"✅ Done! {final_count} leads."
        db.log("Complete", f"Leads: {final_count}")

    except Exception as e:
        logger.error(f"[JOB] Fatal: {e}", exc_info=True)
        jobs[job_id] = jobs.get(job_id, {})
        jobs[job_id]['status'] = 'error'
        jobs[job_id]['error']  = str(e)


# ════════════════════════════════════════════════════
#   FLASK APP
# ════════════════════════════════════════════════════
flask_app = Flask(__name__)
jobs: dict = {}

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
  --bg:#f5f4f0;--surface:#fff;--surface2:#f0efe9;--border:#e2e0d8;
  --ink:#1a1916;--ink2:#6b6860;--ink3:#a09e97;
  --accent:#d4522a;--accent-h:#b8431f;
  --green:#1e8a5e;--amber:#c9820a;--red:#c0392b;--blue:#2962a8;
  --shadow:0 1px 3px rgba(0,0,0,.07),0 4px 16px rgba(0,0,0,.05);
  --r:10px;
}
html{font-size:16px}
body{background:var(--bg);color:var(--ink);font-family:'Outfit',system-ui,sans-serif;min-height:100vh;-webkit-font-smoothing:antialiased}
h1,h2,h3,.syne{font-family:'Syne',sans-serif}
.wrap{max-width:920px;margin:0 auto;padding:0 16px}
/* NAV */
.nav{background:var(--surface);border-bottom:1px solid var(--border);position:sticky;top:0;z-index:40}
.nav-inner{display:flex;align-items:center;justify-content:space-between;padding:13px 16px;max-width:920px;margin:0 auto}
.brand{display:flex;align-items:center;gap:10px}
.logo{width:34px;height:34px;background:var(--accent);border-radius:8px;display:flex;align-items:center;justify-content:center;color:#fff;font-size:15px;flex-shrink:0}
.title{font-family:'Syne',sans-serif;font-size:15px;font-weight:700}
.title span{color:var(--accent)}
.sub{font-size:11px;color:var(--ink3)}
/* STATS */
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin:20px 0}
@media(max-width:600px){.stats{grid-template-columns:repeat(2,1fr)}}
.sc{background:var(--surface);border:1px solid var(--border);border-radius:var(--r);padding:14px 16px;box-shadow:var(--shadow)}
.sc:hover{border-color:rgba(212,82,42,.25)}
.sv{font-family:'Syne',sans-serif;font-size:26px;font-weight:700;line-height:1}
.sl{font-size:11px;color:var(--ink3);margin-top:4px;font-weight:500;text-transform:uppercase;letter-spacing:.04em}
.dot{width:7px;height:7px;border-radius:50%;display:inline-block;margin-right:5px}
/* TABS */
.tabs{display:flex;gap:2px;overflow-x:auto;border-bottom:2px solid var(--border);margin-bottom:20px;-webkit-overflow-scrolling:touch;scrollbar-width:none;padding-bottom:1px}
.tabs::-webkit-scrollbar{display:none}
.tab{background:none;border:none;padding:9px 14px;font-size:13px;font-weight:600;color:var(--ink3);cursor:pointer;white-space:nowrap;border-bottom:2px solid transparent;margin-bottom:-2px;transition:color .15s,border-color .15s;font-family:'Outfit',sans-serif;border-radius:6px 6px 0 0}
.tab:hover{color:var(--ink)}
.tab.on{color:var(--accent);border-bottom-color:var(--accent)}
/* CARDS */
.card{background:var(--surface);border:1px solid var(--border);border-radius:var(--r);padding:20px;box-shadow:var(--shadow);margin-bottom:16px}
.ct{font-family:'Syne',sans-serif;font-size:14px;font-weight:700;display:flex;align-items:center;gap:8px;margin-bottom:16px}
.ct i{color:var(--accent);width:16px;text-align:center}
/* FORM */
.fg{display:flex;flex-direction:column;gap:5px}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:12px}
@media(max-width:560px){.grid2{grid-template-columns:1fr}}
label{font-size:12px;font-weight:600;color:var(--ink2);letter-spacing:.01em;text-transform:uppercase}
.inp{background:var(--bg);border:1.5px solid var(--border);color:var(--ink);border-radius:8px;padding:10px 13px;font-size:14px;width:100%;font-family:'Outfit',sans-serif;transition:border .15s,box-shadow .15s;outline:none}
.inp:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(212,82,42,.1)}
.inp::placeholder{color:var(--ink3)}
/* BUTTONS */
.btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;border:none;border-radius:8px;font-weight:600;font-size:14px;cursor:pointer;transition:all .15s;font-family:'Outfit',sans-serif;padding:11px 20px;white-space:nowrap}
.btn:disabled{opacity:.4;cursor:not-allowed;pointer-events:none}
.btn-p{background:var(--accent);color:#fff}
.btn-p:hover{background:var(--accent-h);transform:translateY(-1px);box-shadow:0 4px 14px rgba(212,82,42,.3)}
.btn-g{background:var(--green);color:#fff}
.btn-g:hover{filter:brightness(1.1);transform:translateY(-1px)}
.btn-n{background:var(--surface2);color:var(--ink);border:1.5px solid var(--border)}
.btn-n:hover{border-color:var(--ink2)}
.btn-ghost{background:none;color:var(--ink3);border:1.5px solid var(--border);font-size:12px;padding:7px 13px}
.btn-ghost:hover{color:var(--red);border-color:var(--red)}
.btn-full{width:100%}
/* STATUS */
.prog{height:4px;background:var(--surface2);border-radius:99px;overflow:hidden;margin-bottom:10px}
.prog-f{height:100%;border-radius:99px;background:var(--accent);transition:width .5s ease}
.sdet{font-size:12px;color:var(--ink3);font-family:monospace;background:var(--surface2);padding:10px 13px;border-radius:7px;min-height:36px;word-break:break-all;line-height:1.5}
.dchips{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px}
.chip{font-size:11px;padding:3px 9px;border-radius:99px;font-weight:600}
.c-bl{background:rgba(41,98,168,.1);color:var(--blue)}
.c-gr{background:rgba(30,138,94,.1);color:var(--green)}
.c-am{background:rgba(201,130,10,.1);color:var(--amber)}
.c-rd{background:rgba(192,57,43,.1);color:var(--red)}
.c-pu{background:rgba(103,58,183,.1);color:#673ab7}
/* TABLE */
.tbl-wrap{overflow-x:auto;-webkit-overflow-scrolling:touch;border-radius:8px;border:1px solid var(--border)}
table{width:100%;border-collapse:collapse;min-width:500px}
th{padding:9px 12px;text-align:left;font-size:11px;font-weight:700;text-transform:uppercase;letter-spacing:.05em;color:var(--ink3);background:var(--surface2);white-space:nowrap}
td{padding:10px 12px;font-size:12px;border-top:1px solid var(--border);vertical-align:middle}
tr:hover td{background:var(--bg)}
.badge{display:inline-block;padding:2px 8px;border-radius:6px;font-size:11px;font-weight:700}
.b-ok{background:rgba(30,138,94,.1);color:var(--green)}
.b-na{background:rgba(160,158,151,.12);color:var(--ink3)}
.b-wa{background:rgba(201,130,10,.1);color:var(--amber)}
.b-in{background:rgba(41,98,168,.1);color:var(--blue)}
/* NOTICES */
.notice{border-radius:8px;padding:10px 13px;font-size:12px;font-weight:500;margin-bottom:12px;display:flex;gap:8px;align-items:flex-start}
.notice i{margin-top:1px;flex-shrink:0}
.n-warn{background:rgba(201,130,10,.08);border:1px solid rgba(201,130,10,.2);color:#7a4f00}
.n-info{background:rgba(41,98,168,.07);border:1px solid rgba(41,98,168,.15);color:#183d6d}
/* TEMPLATE / HISTORY ITEMS */
.ti{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px;position:relative}
.tn{font-family:'Syne',sans-serif;font-size:13px;font-weight:700;margin-bottom:3px}
.ts{font-size:12px;color:var(--blue);margin-bottom:4px}
.tb2{font-size:11px;color:var(--ink3);overflow:hidden;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical}
.tdel{position:absolute;top:10px;right:10px;background:none;border:none;color:var(--ink3);cursor:pointer;font-size:13px;padding:4px}
.tdel:hover{color:var(--red)}
.hi{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px}
/* LOCK SYSTEM */
.lock-row{display:flex;align-items:center;gap:10px;padding:10px 13px;border:1.5px solid var(--border);border-radius:8px;margin-bottom:12px;background:var(--surface2)}
.lock-icon{font-size:18px;flex-shrink:0}
.lock-icon.locked{color:var(--red)}
.lock-icon.unlocked{color:var(--green)}
.lock-label{flex:1;font-size:13px;font-weight:600}
.lock-sub{font-size:11px;color:var(--ink3);margin-top:1px}
/* PIN MODAL */
.modal-overlay{position:fixed;inset:0;background:rgba(0,0,0,.45);display:flex;align-items:center;justify-content:center;z-index:100;backdrop-filter:blur(4px)}
.modal{background:var(--surface);border-radius:14px;padding:28px;width:320px;max-width:90vw;box-shadow:0 20px 60px rgba(0,0,0,.2)}
.modal h3{font-family:'Syne',sans-serif;font-size:18px;font-weight:700;margin-bottom:6px}
.modal p{font-size:13px;color:var(--ink3);margin-bottom:20px}
.pin-input{font-size:24px;text-align:center;letter-spacing:12px;font-family:'Syne',sans-serif}
.pin-error{color:var(--red);font-size:12px;text-align:center;margin-top:8px;min-height:18px}
/* ANIMATIONS */
.spin{animation:spin 1s linear infinite}
.blink{animation:bl 1.3s ease infinite}
@keyframes spin{to{transform:rotate(360deg)}}
@keyframes bl{0%,100%{opacity:1}50%{opacity:.3}}
.fade{animation:fi .25s ease}
@keyframes fi{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:translateY(0)}}
.hidden{display:none!important}
.flex{display:flex}.ac{align-items:center}.jb{justify-content:space-between}
.gap2{gap:8px}.gap3{gap:12px}.mt2{margin-top:8px}.mt3{margin-top:12px}
.xs{font-size:11px}.sm{font-size:12px}.muted{color:var(--ink3)}
.bold{font-weight:700}.space-y>*+*{margin-top:10px}
@media(max-width:480px){.card{padding:14px}.btn{padding:10px 16px;font-size:13px}.sv{font-size:22px}}
</style>
</head>
<body>

<!-- PIN MODAL -->
<div id="pin-modal" class="modal-overlay hidden">
  <div class="modal">
    <h3>🔒 Enter PIN</h3>
    <p id="pin-modal-label">Enter your 4-digit PIN to unlock this feature.</p>
    <input id="pin-input" class="inp pin-input" type="password" maxlength="4" placeholder="••••" autocomplete="off">
    <div id="pin-error" class="pin-error"></div>
    <div class="flex gap2 mt3">
      <button onclick="pinCancel()" class="btn btn-n flex-1">Cancel</button>
      <button onclick="pinConfirm()" class="btn btn-p flex-1"><i class="fa-solid fa-unlock"></i>Unlock</button>
    </div>
  </div>
</div>

<!-- NAV -->
<nav class="nav">
  <div class="nav-inner">
    <div class="brand">
      <div class="logo"><i class="fa-solid fa-bolt"></i></div>
      <div>
        <div class="title">Lead<span>Gen</span> Pro</div>
        <div class="sub">Scrape · Filter · Email</div>
      </div>
    </div>
    <div id="job-badge" style="display:none">
      <span class="badge b-wa blink">● RUNNING</span>
    </div>
  </div>
</nav>

<div class="wrap" style="padding-top:20px;padding-bottom:40px">

  <!-- STATS -->
  <div class="stats">
    <div class="sc"><div class="sv" id="st-leads">0</div><div class="sl"><span class="dot" style="background:var(--accent)"></span>Valid Leads</div></div>
    <div class="sc"><div class="sv" id="st-emails" style="color:var(--green)">0</div><div class="sl"><span class="dot" style="background:var(--green)"></span>Emails Sent</div></div>
    <div class="sc"><div class="sv" id="st-phones" style="color:var(--blue)">0</div><div class="sl"><span class="dot" style="background:var(--blue)"></span>With Phone</div></div>
    <div class="sc"><div class="sv" id="st-webs" style="color:var(--amber)">0</div><div class="sl"><span class="dot" style="background:var(--amber)"></span>Websites</div></div>
  </div>

  <!-- TABS -->
  <div class="tabs">
    <button class="tab on" id="tab-search"    onclick="showTab('search')"><i class="fa-solid fa-magnifying-glass"></i> Search</button>
    <button class="tab"    id="tab-database"  onclick="showTab('database')"><i class="fa-solid fa-database"></i> Database</button>
    <button class="tab"    id="tab-connect"   onclick="showTab('connect')"><i class="fa-solid fa-paper-plane"></i> Email</button>
    <button class="tab"    id="tab-templates" onclick="showTab('templates')"><i class="fa-solid fa-file-lines"></i> Templates</button>
    <button class="tab"    id="tab-history"   onclick="showTab('history')"><i class="fa-solid fa-clock-rotate-left"></i> History</button>
  </div>

  <!-- ═══ SEARCH ═══ -->
  <div id="pane-search" class="fade">
    <div class="card">
      <div class="ct"><i class="fa-solid fa-crosshairs"></i>Target Parameters</div>
      <div class="grid2">
        <div class="fg"><label>📍 Location *</label><input id="m-loc" class="inp" placeholder="e.g. New York" autocomplete="off"></div>
        <div class="fg"><label>🔍 Keyword *</label><input id="m-kw" class="inp" placeholder="e.g. dentist" autocomplete="off"></div>
        <div class="fg"><label>🎯 Target Leads (max 200)</label><input id="m-count" type="number" min="1" max="200" value="10" class="inp"></div>
        <div class="fg"><label>⭐ Max Rating (optional)</label><input id="m-rating" type="number" step="0.1" min="1" max="5" class="inp" placeholder="e.g. 3.5"></div>
      </div>
      <div class="notice n-warn mt2">
        <i class="fa-solid fa-triangle-exclamation"></i>
        <span><b>Flow:</b> Scrapes Yelp + Google + Bing first → 4-stage website resolver → email extraction → keywords expanded only if target not met. Worst-rated businesses first.</span>
      </div>
      <button onclick="startJob()" id="btn-run" class="btn btn-p btn-full" style="margin-top:12px">
        <i class="fa-solid fa-play"></i>Start Scraping
      </button>
    </div>

    <div id="sbox" class="hidden card fade">
      <div class="flex ac gap2" style="margin-bottom:12px;flex-wrap:wrap">
        <i id="si" class="fa-solid fa-circle-notch spin" style="font-size:18px;color:var(--accent);flex-shrink:0"></i>
        <span id="stxt" class="bold" style="font-family:'Syne',sans-serif;font-size:14px">Processing...</span>
      </div>
      <div class="prog"><div class="prog-f" id="sbar" style="width:0%"></div></div>
      <div id="sdet" class="sdet">Initialising...</div>
      <div class="dchips" id="dbg"></div>
      <button id="dlbtn" onclick="doDL()" class="btn btn-g btn-full mt3 hidden">
        <i class="fa-solid fa-download"></i>Download Leads CSV
      </button>
    </div>

    <div id="pvbox" class="hidden card fade">
      <div class="flex ac jb" style="margin-bottom:14px">
        <div class="ct" style="margin-bottom:0"><i class="fa-solid fa-table-cells"></i>Preview <span id="pvcnt" class="muted" style="font-weight:400;font-size:12px"></span></div>
        <button onclick="doDL()" class="btn btn-n sm" style="padding:7px 13px"><i class="fa-solid fa-download"></i> CSV</button>
      </div>
      <div class="tbl-wrap">
        <table><thead><tr id="th"></tr></thead><tbody id="tb"></tbody></table>
      </div>
    </div>
  </div>

  <!-- ═══ DATABASE ═══ -->
  <div id="pane-database" class="hidden fade">
    <div class="card">
      <div class="ct"><i class="fa-solid fa-database"></i>Google Sheets Database</div>

      <!-- Lock row -->
      <div class="lock-row" id="db-lock-row">
        <i id="db-lock-icon" class="fa-solid fa-lock lock-icon locked"></i>
        <div>
          <div class="lock-label" id="db-lock-label">Database Connection — Locked</div>
          <div class="lock-sub" id="db-lock-sub">Enter PIN to configure</div>
        </div>
        <button id="db-lock-btn" onclick="requestPin('database')" class="btn btn-n" style="font-size:12px;padding:7px 13px">
          Unlock
        </button>
      </div>

      <div id="db-content" class="hidden">
        <div class="notice n-info">
          <i class="fa-solid fa-circle-info"></i>
          <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → New Project → paste script → Deploy as Web App (Anyone) → copy URL. <b>Settings saved to server — works on all devices.</b></span>
        </div>
        <div style="position:relative;margin-bottom:14px">
          <button onclick="copyDBScript()" class="btn btn-n" style="position:absolute;top:8px;right:8px;font-size:11px;padding:5px 10px;z-index:1">Copy</button>
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
      getOrCreateSheet("Qualified_Leads",["business_name","email","website","phone","address","rating","review_count","maps_url","keyword","personalization_line","email_sent"]);
      getOrCreateSheet("Logs",["timestamp","action","details"]);
    } else if (action === "log") { var s=ss.getSheetByName("Logs"); if(s) s.appendRow([data.timestamp,data.action,data.details]); }
    else if (action === "add_keyword") { var s=ss.getSheetByName("Generated_Keywords"); if(s) s.appendRow([data.keyword,data.source_seed,data.status]); }
    else if (action === "add_scraped") { var s=ss.getSheetByName("Scraped_Businesses"); if(s) s.appendRow([data.business_name,data.address,data.phone,data.rating,data.review_count,data.website,data.maps_url||"",data.keyword,data.status]); }
    else if (action === "add_email_lead") { var s=ss.getSheetByName("Email_Leads"); if(s) s.appendRow([data.business_name,data.website,data.email,data.source_page,data.status]); }
    else if (action === "add_qualified") { var s=ss.getSheetByName("Qualified_Leads"); if(s) s.appendRow([data.business_name,data.email,data.website,data.phone||"",data.address||"",data.rating||"",data.review_count||"",data.maps_url||"",data.keyword,data.personalization_line,data.email_sent]); }
    else if (action === "update_config") { var s=ss.getSheetByName("Config"); if(s){s.clearContents();s.appendRow(["keyword_seed","location","target_leads","min_rating","max_rating","email_required","status"]);s.appendRow([data.keyword_seed,data.location,data.target_leads,data.min_rating,data.max_rating,data.email_required,data.status]);} }
    else if (action === "update_email_sent") { var s=ss.getSheetByName("Qualified_Leads"); if(s){var v=s.getDataRange().getValues();for(var i=1;i<v.length;i++){if(v[i][1]===data.email){s.getRange(i+1,6).setValue(data.personalization_line);s.getRange(i+1,7).setValue("yes");break;}}} }
    return ContentService.createTextOutput(JSON.stringify({status:"success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(e) { return ContentService.createTextOutput(JSON.stringify({status:"error",message:e.toString()})).setMimeType(ContentService.MimeType.JSON); }
  finally { lock.releaseLock(); }
}
function doGet(e) { return ContentService.createTextOutput(JSON.stringify({status:"active"})).setMimeType(ContentService.MimeType.JSON); }</textarea>
        </div>
        <div class="fg" style="margin-bottom:12px">
          <label>🔗 Database Web App URL</label>
          <input id="db-webhook-url" class="inp" placeholder="https://script.google.com/macros/s/AKfycb.../exec">
        </div>
        <button onclick="saveDBWebhook()" class="btn btn-p btn-full"><i class="fa-solid fa-link"></i>Save & Connect Database</button>
      </div>
    </div>
  </div>

  <!-- ═══ EMAIL ═══ -->
  <div id="pane-connect" class="hidden fade">
    <div class="card">
      <div class="ct"><i class="fa-solid fa-paper-plane"></i>Gmail Sender Setup</div>

      <!-- Lock row -->
      <div class="lock-row" id="email-lock-row">
        <i id="email-lock-icon" class="fa-solid fa-lock lock-icon locked"></i>
        <div>
          <div class="lock-label" id="email-lock-label">Email Connection — Locked</div>
          <div class="lock-sub" id="email-lock-sub">Enter PIN to configure</div>
        </div>
        <button id="email-lock-btn" onclick="requestPin('email')" class="btn btn-n" style="font-size:12px;padding:7px 13px">
          Unlock
        </button>
      </div>

      <div id="email-content" class="hidden">
        <div class="notice n-info">
          <i class="fa-solid fa-circle-info"></i>
          <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → paste code → Deploy as Web App (Anyone) → copy URL. <b>Settings saved to server — works on all devices.</b></span>
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
        <div class="fg" style="margin-bottom:12px">
          <label>🔗 Email Web App URL</label>
          <input id="webhook-url" class="inp" placeholder="https://script.google.com/macros/s/AKfycb.../exec">
        </div>
        <button onclick="saveWebhook()" class="btn btn-g btn-full"><i class="fa-solid fa-save"></i>Save Email Webhook</button>
      </div>
    </div>
  </div>

  <!-- ═══ TEMPLATES ═══ -->
  <div id="pane-templates" class="hidden fade">
    <div class="card">
      <div class="ct"><i class="fa-solid fa-plus"></i>Add Template</div>
      <div class="fg" style="margin-bottom:10px"><label>Template Name</label><input id="t-name" class="inp" placeholder="e.g. SEO Pitch"></div>
      <div class="fg" style="margin-bottom:10px"><label>Subject</label><input id="t-sub" class="inp" placeholder="Subject (AI personalizes this)"></div>
      <div class="fg" style="margin-bottom:12px"><label>Body (HTML allowed)</label><textarea id="t-body" class="inp" style="height:90px;resize:vertical" placeholder="Use {name}, {niche} as placeholders."></textarea></div>
      <button onclick="addTemplate()" class="btn btn-p btn-full"><i class="fa-solid fa-plus"></i>Add Template</button>
    </div>
    <div class="card"><div class="ct"><i class="fa-solid fa-list"></i>Saved Templates</div><div id="t-list" class="space-y"></div></div>
  </div>

  <!-- ═══ HISTORY ═══ -->
  <div id="pane-history" class="hidden fade">
    <div class="card">
      <div class="flex ac jb" style="margin-bottom:14px">
        <div class="ct" style="margin-bottom:0"><i class="fa-solid fa-clock-rotate-left"></i>History</div>
        <button onclick="clearHistory()" class="btn btn-ghost"><i class="fa-solid fa-trash"></i> Clear</button>
      </div>
      <div id="h-list" class="space-y"></div>
    </div>
  </div>

</div><!-- /wrap -->

<script>
// ── State ──────────────────────────────────────────────────────────
let jid=null, templates=[], historyData=[], tableShown=false;
let dbUnlocked=false, emailUnlocked=false;
let pinTarget='', pinCallback=null;

// ── Boot: load settings from SERVER (not localStorage) ────────────
window.onload = async () => {
  historyData = JSON.parse(localStorage.getItem('lgp_history') || '[]');
  renderHistory();
  await loadServerSettings();
};

async function loadServerSettings() {
  try {
    const r = await fetch('/api/settings');
    const d = await r.json();
    document.getElementById('webhook-url').value    = d.webhook_url    || '';
    document.getElementById('db-webhook-url').value = d.db_webhook_url || '';
    templates = d.templates || [];
    renderTemplates();
  } catch(e) { console.warn('Could not load settings:', e); }
}

// ── Tab switching ──────────────────────────────────────────────────
const TABS = ['search','database','connect','templates','history'];
function showTab(t) {
  TABS.forEach(x => {
    document.getElementById('pane-'+x).classList.add('hidden');
    document.getElementById('tab-'+x).classList.remove('on');
  });
  document.getElementById('pane-'+t).classList.remove('hidden');
  document.getElementById('tab-'+t).classList.add('on');
}

// ── PIN system ────────────────────────────────────────────────────
function requestPin(target) {
  pinTarget = target;
  document.getElementById('pin-input').value = '';
  document.getElementById('pin-error').textContent = '';
  const label = target === 'database' ? 'Database Connection' : 'Email Connection';
  document.getElementById('pin-modal-label').textContent = `Enter PIN to unlock: ${label}`;
  document.getElementById('pin-modal').classList.remove('hidden');
  setTimeout(() => document.getElementById('pin-input').focus(), 100);
}
function pinCancel() {
  document.getElementById('pin-modal').classList.add('hidden');
  pinTarget = '';
}
async function pinConfirm() {
  const pin = document.getElementById('pin-input').value;
  try {
    const r = await fetch('/api/verify-pin', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({pin})});
    const d = await r.json();
    if (d.ok) {
      document.getElementById('pin-modal').classList.add('hidden');
      if (pinTarget === 'database') unlockSection('database');
      else if (pinTarget === 'email') unlockSection('email');
    } else {
      document.getElementById('pin-error').textContent = '❌ Incorrect PIN. Try again.';
      document.getElementById('pin-input').value = '';
    }
  } catch(e) {
    document.getElementById('pin-error').textContent = 'Error verifying PIN.';
  }
}
// Allow Enter key in PIN input
document.addEventListener('DOMContentLoaded', () => {
  document.getElementById('pin-input').addEventListener('keydown', e => {
    if (e.key === 'Enter') pinConfirm();
  });
});
function unlockSection(section) {
  if (section === 'database') {
    dbUnlocked = true;
    document.getElementById('db-lock-icon').className = 'fa-solid fa-lock-open lock-icon unlocked';
    document.getElementById('db-lock-label').textContent = 'Database Connection — Unlocked';
    document.getElementById('db-lock-sub').textContent = 'Configure your Google Sheets database below';
    document.getElementById('db-lock-btn').textContent = '✓ Unlocked';
    document.getElementById('db-lock-btn').disabled = true;
    document.getElementById('db-content').classList.remove('hidden');
  } else {
    emailUnlocked = true;
    document.getElementById('email-lock-icon').className = 'fa-solid fa-lock-open lock-icon unlocked';
    document.getElementById('email-lock-label').textContent = 'Email Connection — Unlocked';
    document.getElementById('email-lock-sub').textContent = 'Configure your Gmail sender below';
    document.getElementById('email-lock-btn').textContent = '✓ Unlocked';
    document.getElementById('email-lock-btn').disabled = true;
    document.getElementById('email-content').classList.remove('hidden');
  }
}

// ── Save settings to SERVER ────────────────────────────────────────
async function saveWebhook() {
  const url = document.getElementById('webhook-url').value.trim();
  await fetch('/api/settings', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({webhook_url: url})});
  alert('✅ Email webhook saved to server! Works on all devices.');
}
async function saveDBWebhook() {
  const url = document.getElementById('db-webhook-url').value.trim();
  await fetch('/api/settings', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({db_webhook_url: url})});
  alert('✅ Database webhook saved to server! Works on all devices.');
}
function copyDBScript() { const el=document.getElementById('db-script-code'); el.select(); document.execCommand('copy'); alert('Script copied!'); }

// ── Templates (saved to server) ────────────────────────────────────
async function addTemplate() {
  const n=document.getElementById('t-name').value.trim();
  const s=document.getElementById('t-sub').value.trim();
  const b=document.getElementById('t-body').value.trim();
  if(!n||!s||!b) return alert('Fill all template fields!');
  templates.push({name:n,subject:s,body:b});
  await fetch('/api/settings', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({templates})});
  ['t-name','t-sub','t-body'].forEach(id=>document.getElementById(id).value='');
  renderTemplates();
}
async function delTemplate(i) {
  templates.splice(i,1);
  await fetch('/api/settings', {method:'POST', headers:{'Content-Type':'application/json'}, body: JSON.stringify({templates})});
  renderTemplates();
}
function renderTemplates() {
  const el=document.getElementById('t-list');
  if(!templates.length) return el.innerHTML='<p class="xs muted" style="text-align:center;padding:8px">No templates yet.</p>';
  el.innerHTML=templates.map((t,i)=>`
    <div class="ti">
      <button class="tdel" onclick="delTemplate(${i})"><i class="fa-solid fa-xmark"></i></button>
      <div class="tn">${t.name}</div>
      <div class="ts">${t.subject}</div>
      <div class="tb2">${t.body.replace(/</g,'&lt;')}</div>
    </div>`).join('');
}

// ── History ────────────────────────────────────────────────────────
function renderHistory() {
  const el=document.getElementById('h-list');
  if(!historyData.length) return el.innerHTML='<p class="xs muted" style="text-align:center;padding:8px">No history yet.</p>';
  el.innerHTML=historyData.map(h=>`
    <div class="hi">
      <div class="bold sm">${h.kw} <span class="muted">in</span> ${h.loc}</div>
      <div class="xs muted mt2">Target: ${h.target} · ${h.date}</div>
    </div>`).join('');
}
function clearHistory() { historyData=[]; localStorage.removeItem('lgp_history'); renderHistory(); }

// ── Status ────────────────────────────────────────────────────────
function setSt(msg, state='load', pct=null) {
  document.getElementById('sbox').classList.remove('hidden');
  document.getElementById('sdet').textContent = msg;
  const ic=document.getElementById('si'), txt=document.getElementById('stxt');
  const m={load:['fa-circle-notch spin','var(--accent)','Scraping…'],email:['fa-paper-plane blink','var(--green)','Sending Emails…'],done:['fa-circle-check','var(--green)','Completed!'],err:['fa-circle-xmark','var(--red)','Error']};
  const [cls,col,label]=m[state]||m.load;
  ic.className=`fa-solid ${cls}`;ic.style.color=col;txt.textContent=label;
  if(pct!=null) document.getElementById('sbar').style.width=Math.min(100,pct)+'%';
  document.getElementById('job-badge').style.display=(state==='load'||state==='email')?'':'none';
}
function renderDbg(s){
  if(!s) return;
  document.getElementById('dbg').innerHTML=`
    <span class="chip c-bl" title="Total businesses scraped">Scraped: ${s.scraped_total||0}</span>
    <span class="chip c-am" title="After rating filter">Filtered: ${s.after_rating_filter||0}</span>
    <span class="chip c-gr" title="Emails found">Emails: ${s.emails_found||0}</span>
    <span class="chip c-rd" title="Duplicates skipped">Dupes: ${s.duplicates_skipped||0}</span>
    <span class="chip c-pu" title="Keywords used">KW: ${s.keywords_used||0}</span>
    <span class="chip c-rd">Errors: ${s.errors||0}</span>`;
}
function updStats(leads){
  document.getElementById('st-leads').textContent=leads.length;
  document.getElementById('st-emails').textContent=leads.filter(l=>l.Email&&l.Email!='N/A').length;
  document.getElementById('st-phones').textContent=leads.filter(l=>l.Phone&&l.Phone!='N/A').length;
  document.getElementById('st-webs').textContent=leads.filter(l=>l.Website&&l.Website!='N/A').length;
}
function showPV(leads){
  if(!leads?.length) return;
  document.getElementById('pvbox').classList.remove('hidden');
  document.getElementById('pvcnt').textContent=`(${leads.length} total · top 10)`;
  const keys=Object.keys(leads[0]).filter(k=>!k.startsWith('_')&&k!=='Maps_Link');
  document.getElementById('th').innerHTML=keys.map(k=>`<th>${k}</th>`).join('');
  document.getElementById('tb').innerHTML=leads.slice(0,10).map(l=>
    `<tr>${keys.map(k=>{
      const v=(l[k]||'N/A').toString();
      const c=v==='N/A'?'b-na':k==='Email'?'b-ok':k==='Rating'?'b-wa':k==='Phone'?'b-in':'';
      return `<td>${c?`<span class="badge ${c}">${v.length>40?v.slice(0,40)+'…':v}</span>`:v.length>40?v.slice(0,40)+'…':v}</td>`;
    }).join('')}</tr>`).join('');
}

// ── Start job ──────────────────────────────────────────────────────
async function startJob(){
  const loc=document.getElementById('m-loc').value.trim();
  const kw=document.getElementById('m-kw').value.trim();
  let count=Math.min(parseInt(document.getElementById('m-count').value)||10,200);
  if(!loc||!kw) return alert('Location and Keyword are required!');

  setSt(`Starting scrape for: ${kw} in ${loc}...`,'load',2);
  document.getElementById('dlbtn').classList.add('hidden');
  document.getElementById('pvbox').classList.add('hidden');
  document.getElementById('dbg').innerHTML='';
  document.getElementById('btn-run').disabled=true;
  tableShown=false;

  // Settings come from server — no need to read from inputs
  const payload={location:loc,keyword:kw,max_leads:count,
    max_rating:document.getElementById('m-rating').value.trim()||null,
    templates:templates};
  try {
    const r=await fetch('/api/scrape',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});
    const d=await r.json();
    if(d.error){setSt(d.error,'err');document.getElementById('btn-run').disabled=false;return;}
    jid=d.job_id;
    historyData.unshift({loc,kw,target:count,date:new Date().toLocaleString()});
    localStorage.setItem('lgp_history',JSON.stringify(historyData)); renderHistory();
    startPolling(count);
  } catch(e){setSt('Server error','err');document.getElementById('btn-run').disabled=false;}
}

// ── Polling ────────────────────────────────────────────────────────
function startPolling(target){
  const poll=async()=>{
    try{
      const r2=await fetch('/api/status/'+jid);
      const d2=await r2.json();
      if(d2.stats) renderDbg(d2.stats);
      if(d2.status==='scraping'){
        setSt(d2.status_text||'Scraping…','load',Math.max(3,(d2.count/target)*95));
        if(d2.leads?.length){updStats(d2.leads);if(!tableShown){showPV(d2.leads);tableShown=true;}}
        setTimeout(poll,2500);
      } else if(d2.status==='sending_emails'){
        if(!tableShown&&d2.leads){updStats(d2.leads);showPV(d2.leads);tableShown=true;}
        document.getElementById('dlbtn').classList.remove('hidden');
        setSt(d2.status_text||'Sending…','email',d2.total_to_send>0?(d2.emails_sent/d2.total_to_send)*100:50);
        setTimeout(poll,2500);
      } else if(d2.status==='done'){
        document.getElementById('btn-run').disabled=false;
        if(d2.leads){updStats(d2.leads);showPV(d2.leads);}
        setSt(d2.status_text||'Done!','done',100);
        document.getElementById('dlbtn').classList.remove('hidden');
      } else if(d2.status==='error'){
        document.getElementById('btn-run').disabled=false;
        setSt(d2.error||'Unknown error','err');
      } else { setTimeout(poll,2500); }
    } catch(e){setTimeout(poll,2500);}
  };
  setTimeout(poll,1500);
}
function doDL(){if(jid)window.location='/api/download/'+jid;}
</script>
</body>
</html>"""


# ════════════════════════════════════════════════════
#   FLASK ROUTES
# ════════════════════════════════════════════════════
@flask_app.route('/')
def index():
    return render_template_string(HTML_TEMPLATE)


@flask_app.route('/api/settings', methods=['GET'])
def get_settings_api():
    return jsonify(get_settings())


@flask_app.route('/api/settings', methods=['POST'])
def save_settings_api():
    data = request.json or {}
    for key in ('webhook_url', 'db_webhook_url', 'templates'):
        if key in data:
            save_settings(key, data[key])
    logger.info(f"[SETTINGS] Updated: {list(data.keys())}")
    return jsonify({'ok': True})


@flask_app.route('/api/verify-pin', methods=['POST'])
def verify_pin():
    data = request.json or {}
    pin = str(data.get('pin', ''))
    ok = (pin == ACCESS_PIN)
    logger.info(f"[PIN] Verification attempt — {'OK' if ok else 'FAILED'}")
    return jsonify({'ok': ok})


@flask_app.route('/api/scrape', methods=['POST'])
def start_api_job():
    data = request.json
    job_id = str(uuid.uuid4())[:8]
    logger.info(
        f"[API] Job {job_id}: kw='{data.get('keyword')}' "
        f"loc='{data.get('location')}' target={data.get('max_leads')} "
        f"max_rating={data.get('max_rating')}"
    )
    t = threading.Thread(target=run_job_thread, args=(job_id, data))
    t.daemon = True
    t.start()
    return jsonify({'job_id': job_id})


@flask_app.route('/api/status/<job_id>')
def status(job_id):
    job = jobs.get(job_id, {'status': 'not_found'})
    out = dict(job)
    if out.get('status') in ['sending_emails', 'done', 'scraping']:
        out['leads'] = job.get('leads', [])
    return jsonify(out)


@flask_app.route('/api/download/<job_id>')
def download(job_id):
    job = jobs.get(job_id)
    if not job or job.get('status') not in ['done', 'sending_emails']:
        return "Not ready", 400
    leads = job.get('leads', [])
    if not leads:
        return "No leads found", 404
    # Strip internal fields before export
    export_leads = [{k: v for k, v in lead.items() if not k.startswith('_')} for lead in leads]
    out = io.StringIO()
    writer = csv.DictWriter(out, fieldnames=export_leads[0].keys())
    writer.writeheader()
    writer.writerows(export_leads)
    out.seek(0)
    return send_file(
        io.BytesIO(out.getvalue().encode('utf-8-sig')),
        mimetype='text/csv',
        as_attachment=True,
        download_name='Target_Leads.csv',
    )


# ════════════════════════════════════════════════════
#   TELEGRAM BOT  (PRESERVED — UNCHANGED)
# ════════════════════════════════════════════════════
def to_csv(leads):
    tmp = tempfile.NamedTemporaryFile(mode='w', suffix='.csv', delete=False,
                                      encoding='utf-8-sig', newline='')
    export = [{k: v for k, v in l.items() if not k.startswith('_')} for l in leads]
    if export:
        writer = csv.DictWriter(tmp, fieldnames=export[0].keys())
        writer.writeheader()
        writer.writerows(export)
    tmp.close()
    return tmp.name

M_LOC, M_KW, M_COUNT, M_RATING = range(4)
bot_store = {}

async def start(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    kb = [[InlineKeyboardButton("🚀 Start Search", callback_data="start_manual")]]
    await update.message.reply_text(
        "👋 *LeadGen Pro Bot*\n\n✅ Yelp+Google+Bing scraping\n✅ 4-stage website resolver\n✅ Worst-rated first\n✅ Max: 200",
        parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(kb)
    )

async def handle_mode(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    bot_store[q.from_user.id] = {}
    await q.edit_message_text("📍 Enter Location:")
    return M_LOC

async def m_loc(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    bot_store[update.message.from_user.id]['loc'] = update.message.text
    await update.message.reply_text("🔍 Enter Keyword:")
    return M_KW

async def m_kw(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    bot_store[update.message.from_user.id]['kw'] = update.message.text
    await update.message.reply_text("🔢 Target Leads (Max 200):")
    return M_COUNT

async def m_count(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    count = int(update.message.text) if update.message.text.isdigit() else 10
    if count > 200: count = 200
    uid = update.message.from_user.id
    bot_store[uid]['count'] = count
    await update.message.reply_text("⭐ Max Rating? (type 'skip'):")
    return M_RATING

async def m_rating(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    txt = update.message.text.lower()
    uid = update.message.from_user.id
    bot_store[uid]['rating'] = None if txt == 'skip' else txt
    data = bot_store[uid]
    summary = f"📋 *Config*\n📍 {data['loc']}\n🔍 {data['kw']}\n🔢 {data['count']}\n⭐ {data.get('rating') or 'None'}\n\nStart?"
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

    m_scraper  = GoogleMapsScraper()
    e_lib      = DeepEmailExtractor()
    kw_engine  = AdvancedKeywordEngine()
    dedup      = DeduplicationStore()

    used_keywords  = set()
    final_leads    = []
    # FIX 2 (bot): one keyword at a time
    _bot_pool: list = []
    _bot_pool_built = False

    def _bot_next_kw() -> str:
        nonlocal _bot_pool_built
        while _bot_pool:
            kw = _bot_pool.pop(0)
            if kw.lower() not in used_keywords:
                return kw
        if not _bot_pool_built:
            new_kws = kw_engine.generate_full_pool(base_keyword, location, used_keywords)
            _bot_pool_built = True
        else:
            new_kws = generate_ai_keywords(base_keyword, location, used_keywords)
        random.shuffle(new_kws)
        _bot_pool.extend([k for k in new_kws if k.lower() not in used_keywords])
        while _bot_pool:
            kw = _bot_pool.pop(0)
            if kw.lower() not in used_keywords:
                return kw
        return f"top {base_keyword} {location}"

    current_kw_bot = base_keyword
    while len(final_leads) < max_leads:
        used_keywords.add(current_kw_bot.lower())
        raw_leads = m_scraper.fetch_batch(current_kw_bot, location)

        for lead in raw_leads:
            if len(final_leads) >= max_leads: break

            if max_rating_float is not None and lead['Rating'] != "N/A":
                try:
                    if float(lead['Rating']) > max_rating_float: continue
                except: pass

            # FIX 1 (bot): 4-stage website resolution
            existing = lead.get('Website', 'N/A')
            yelp_url = lead.get('_yelp_url', 'N/A')
            website = m_scraper.resolve_website(lead['Name'], location, existing, yelp_url)
            lead['Website'] = website
            if not is_valid_business_website(website): continue

            # FIX 5 (bot): dedup before adding — email is primary key
            if dedup.is_duplicate(lead['Name'], website, ""): continue
            extracted_email = e_lib.get_email(website)
            if extracted_email == "N/A": continue
            if dedup.is_duplicate(lead['Name'], website, extracted_email): continue
            dedup.register(lead['Name'], website, extracted_email)

            # FIX 4 (bot): ensure maps_url always set
            lead['Maps_Link'] = lead.get('Maps_Link') or (
                f"https://www.google.com/maps/search/{urllib.parse.quote_plus(lead['Name'] + ' ' + location)}/"
            )
            lead['Email'] = extracted_email
            final_leads.append(lead)

        if len(final_leads) >= max_leads: break
        current_kw_bot = _bot_next_kw()
        time.sleep(random.uniform(1.0, 2.0))

    return final_leads

async def background_bot_task(chat_id, message_id, data, bot):
    try:
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id,
            text="⏳ *Scraping (Yelp+Google+Bing)...*\n_4-stage website resolution active._",
            parse_mode='Markdown')
        loop = asyncio.get_event_loop()
        final_leads = await loop.run_in_executor(None, run_bot_scrape_fast, data)
        if not final_leads:
            await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="😔 No results found.")
            return
        path = to_csv(final_leads)
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="✅ Done! Sending CSV...")
        with open(path, 'rb') as f:
            await bot.send_document(chat_id=chat_id, document=f, filename="Target_Leads.csv",
                caption=f"🎯 Valid Leads: {len(final_leads)}", parse_mode='Markdown')
        os.unlink(path)
    except Exception as e:
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id,
            text=f"❌ Error: `{e}`", parse_mode='Markdown')

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
        fallbacks=[], per_message=False,
    )
    app.add_handler(CommandHandler("start", start))
    app.add_handler(conv)
    app.add_handler(CallbackQueryHandler(execute_scrape, pattern="^start_scrape$"))
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)


# ════════════════════════════════════════════════════
#   ENTRY POINT
# ════════════════════════════════════════════════════
if __name__ == "__main__":
    if TELEGRAM_TOKEN:
        threading.Thread(target=run_telegram_bot, daemon=True).start()
        logger.info("[BOOT] Telegram bot started")
    port = int(os.environ.get("PORT", 10000))
    logger.info(f"[BOOT] Flask on port {port}")
    flask_app.run(host='0.0.0.0', port=port)
