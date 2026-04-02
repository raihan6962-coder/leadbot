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

# ════════════════════════════════════════════════════
#   STOP FLAGS
#   job_stop_flags[job_id]        → threading.Event for scraping
#   email_stop_flags[job_id]      → threading.Event for email sending
#   Setting the event = "STOP NOW"
# ════════════════════════════════════════════════════
job_stop_flags:   dict = {}
email_stop_flags: dict = {}

def _should_stop(job_id: str) -> bool:
    flag = job_stop_flags.get(job_id)
    return flag is not None and flag.is_set()

def _email_should_stop(job_id: str) -> bool:
    flag = email_stop_flags.get(job_id)
    return flag is not None and flag.is_set()

# ════════════════════════════════════════════════════
#   BACKEND PERSISTENT SETTINGS
#   Works across all browsers / devices on same Render instance.
# ════════════════════════════════════════════════════
_settings: dict = {
    "webhook_url":    "",
    "db_webhook_url": "",
    "apify_api_key":  "",
    "templates":      [],
}
_settings_lock = threading.Lock()

def get_settings() -> dict:
    with _settings_lock:
        return dict(_settings)

def save_settings(key: str, value) -> None:
    with _settings_lock:
        _settings[key] = value

# PIN for locking sensitive settings
ACCESS_PIN = "0123"

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
#   Strict: email (primary) OR website OR name+location
# ════════════════════════════════════════════════════
class DeduplicationStore:
    def __init__(self):
        self._lock      = threading.Lock()
        self._websites:  set = set()
        self._emails:    set = set()
        self._name_locs: set = set()
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

    def is_duplicate(self, name: str, location: str, website: str, email: str) -> bool:
        ne   = self._norm(email)
        nw   = self._norm_url(website)
        nloc = f"{self._norm(name)} {self._norm(location)}"
        with self._lock:
            if ne   and ne   in self._emails:    return True
            if nw   and nw   in self._websites:  return True
            if nloc and nloc in self._name_locs: return True
        return False

    def register(self, name: str, location: str, website: str, email: str):
        ne   = self._norm(email)
        nw   = self._norm_url(website)
        nn   = self._norm(name)
        nl   = self._norm(location)
        with self._lock:
            if ne: self._emails.add(ne)
            if nw: self._websites.add(nw)
            if nn and nl: self._name_locs.add(f"{nn} {nl}")

    def mark_skipped(self):
        with self._lock:
            self._total_skipped += 1

    @property
    def skipped(self):
        with self._lock:
            return self._total_skipped


# ════════════════════════════════════════════════════
#   WEBSITE VALIDATOR
# ════════════════════════════════════════════════════
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
    'mapquest.com', 'zoominfo.com', 'manta.com',
    'superpages.com', 'homeadvisor.com',
)

def is_valid_business_website(url: str) -> bool:
    if not url or url == "N/A" or not url.startswith('http'):
        return False
    url_lower = url.lower()
    if any(bl in url_lower for bl in _WEBSITE_BLACKLIST):
        return False
    try:
        host = urllib.parse.urlparse(url_lower).netloc
        if not host or '.' not in host:
            return False
        if re.match(r'^\d+\.\d+\.\d+\.\d+', host):
            return False
        return True
    except:
        return False


# ════════════════════════════════════════════════════
#   KEYWORD ENGINE
#   generate_single_keyword() — strict one-at-a-time
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
        "best rated", "top rated", "highly reviewed",
        "recommended", "free quote", "free estimate", "low cost",
        "reviews", "bad reviews", "poor service", "negative reviews",
    ]

    def __init__(self):
        self.session = requests.Session()

    def expand_with_variations(self, base_kw):
        results = set()
        for prefix in self.COMMERCIAL_PREFIXES:
            results.add(f"{prefix} {base_kw}")
        for suffix in self.COMMERCIAL_SUFFIXES:
            results.add(f"{base_kw} {suffix}")
        for modifier in self.INTENT_MODIFIERS:
            results.add(f"{modifier} {base_kw}")
        return list(results)

    def ai_generate(self, base_kw, location, used_kws):
        fallback = self.expand_with_variations(base_kw)
        if not GROQ_API_KEY:
            return fallback
        try:
            client = Groq(api_key=GROQ_API_KEY)
            prompt = (
                f'Local SEO expert. Seed: "{base_kw}". Location: "{location}". '
                f'Already used: {list(used_kws)[:20]}. '
                f'Generate 120 unique search terms. '
                f'Return ONLY comma-separated list. No explanation.'
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
            return list(set(ai_kws + fallback))
        except Exception as e:
            logger.warning(f"[KEYWORDS] AI gen failed: {e}")
            return fallback

    def generate_full_pool(self, base_kw, location, used_kws):
        all_kws = set(self.ai_generate(base_kw, location, used_kws))
        all_kws.update(self.expand_with_variations(base_kw))
        final = [k for k in all_kws if k.lower() not in used_kws and len(k) > 3]
        logger.info(f"[KEYWORDS] Full pool → {len(final)} for '{base_kw}'")
        return list(set(final))

    # ONE keyword at a time — used by main loop
    def generate_single_keyword(self, base_kw, location, used_kws) -> str:
        """Return exactly ONE new keyword string, or None if exhausted."""
        if GROQ_API_KEY:
            try:
                client = Groq(api_key=GROQ_API_KEY)
                prompt = (
                    f"Local SEO expert. Base: '{base_kw}'. Location: '{location}'. "
                    f"Used: {list(used_kws)[:50]}. "
                    f"Generate EXACTLY ONE new search term. "
                    f"Return ONLY the exact search term. No quotes, no intro."
                )
                res = client.chat.completions.create(
                    messages=[{"role": "user", "content": prompt}],
                    model="llama3-8b-8192",
                    temperature=0.85,
                    max_tokens=30,
                )
                kw = res.choices[0].message.content.strip().strip('"').strip("'")
                kw = kw.split('\n')[0].split(',')[0].strip()
                if kw and kw.lower() not in used_kws and len(kw) > 3:
                    logger.info(f"[KEYWORDS] Single AI keyword: '{kw}'")
                    return kw
            except Exception as e:
                logger.warning(f"[KEYWORDS] AI single gen failed: {e}")

        # Fallback: prefix/suffix variants
        for p in self.COMMERCIAL_PREFIXES:
            c = f"{p} {base_kw}"
            if c.lower() not in used_kws:
                return c
        for s in self.COMMERCIAL_SUFFIXES:
            c = f"{base_kw} {s}"
            if c.lower() not in used_kws:
                return c
        return None


# ════════════════════════════════════════════════════
#   GOOGLE MAPS SCRAPER
#   Primary source: Google Maps search HTML (fast, real data)
#   Fallback sources: Google Local tbm=lcl, Yelp, Bing
#   Block detection: if 3 consecutive keywords return 0 results → Apify
#   [PROBLEM 5] Results sorted by rating ASC (worst-rated first)
# ════════════════════════════════════════════════════
class GoogleMapsScraper:
    MAX_RETRIES  = 3
    RETRY_DELAY  = 1.5

    # ── [PROBLEM 1] Working scraper from doc 6 — Google Maps tbm=lcl ──
    # This is the original "SUPER FAST PURE PYTHON SCRAPER" approach that
    # correctly extracts rating and review count from Google Maps local results.
    def _scrape_google_maps_lcl(self, keyword: str, location: str) -> list:
        """
        [INTEGRATED FROM WORKING SCRAPER] Uses Google Maps local pack
        via tbm=lcl, which reliably returns rating + review count.
        Multiple page offsets to maximise volume.
        """
        query = urllib.parse.quote_plus(f"{keyword} in {location}")
        all_results = []

        def _fetch_one_offset(start: int) -> list:
            url = f"https://www.google.com/search?q={query}&tbm=lcl&start={start}&num=20&hl=en&gl=us"
            for attempt in range(1, self.MAX_RETRIES + 1):
                try:
                    # [PROBLEM 2] Short timeout so stop flag takes effect quickly
                    resp = requests.get(url, headers=get_headers(), timeout=8, verify=False)
                    logger.info(f"[MAPS-LCL] offset={start} HTTP {resp.status_code}")
                    if resp.status_code != 200:
                        time.sleep(self.RETRY_DELAY * attempt)
                        continue

                    soup = BeautifulSoup(resp.text, 'html.parser')

                    # Extended selector list — covers old and new Google Maps layouts
                    blocks = soup.select(
                        'div.VkpGBb, div.rllt__details, div.uMdZh, div.cXedhc, '
                        'div.lqhpac, div[data-cid], div.rl_tit, li.rllt__list-item, '
                        'div[class*="rllt"]'
                    )
                    logger.info(f"[MAPS-LCL] offset={start} — {len(blocks)} blocks")

                    batch = []
                    for block in blocks:
                        text_content = block.get_text(separator=' ', strip=True)

                        # Name extraction
                        name_el = block.select_one(
                            'div[role="heading"], .dbg0pd, span.OSrXXb, '
                            '.rllt__details div:first-child, [class*="tit"], '
                            'div.rllt__details > div:first-child'
                        )
                        name = name_el.get_text(strip=True) if name_el else "N/A"
                        if name == "N/A" or len(name) < 3:
                            # Fallback: first short text child
                            for el in block.children:
                                t = el.get_text(strip=True) if hasattr(el, 'get_text') else ''
                                if 3 < len(t) < 80:
                                    name = t
                                    break
                        if name == "N/A" or len(name) < 3:
                            continue

                        # [PROBLEM 1 FIX] Rating — matches "4.2" patterns reliably
                        rating = "N/A"
                        rm = re.search(r'\b([1-5][.,]\d)\b', text_content)
                        if rm:
                            rv = rm.group(1).replace(',', '.')
                            try:
                                if 1.0 <= float(rv) <= 5.0:
                                    rating = rv
                            except:
                                pass

                        # [PROBLEM 1 FIX] Review count — matches "(123)" patterns
                        review_count = "0"
                        rc = re.search(r'\((\d{1,6})\)', text_content)
                        if rc:
                            review_count = rc.group(1)

                        # Phone
                        phone = "N/A"
                        ph = re.search(
                            r'(\+?1?\s*[\-\.]?\(?\d{3}\)?[\s\-\.]?\d{3}[\s\-\.]?\d{4})',
                            text_content
                        )
                        if ph:
                            phone = ph.group(0).strip()

                        # Website — validated immediately
                        website = "N/A"
                        for a in block.select('a[href]'):
                            href = a.get('href', '')
                            if '/url?q=' in href:
                                clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                                if is_valid_business_website(clean):
                                    website = clean
                                    break
                            elif is_valid_business_website(href):
                                website = href
                                break

                        # [PROBLEM 4 / Maps URL] Always build canonical Maps link
                        maps_link = (
                            f"https://www.google.com/maps/search/"
                            f"{urllib.parse.quote_plus(name + ' ' + location)}/"
                        )

                        batch.append({
                            "Name":        name,
                            "Phone":       phone,
                            "Website":     website,
                            "Rating":      rating,
                            "ReviewCount": review_count,
                            "Address":     location,
                            "Category":    keyword,
                            "Maps_Link":   maps_link,
                        })

                    logger.info(f"[MAPS-LCL] offset={start} → {len(batch)} parsed")
                    return batch

                except requests.exceptions.RequestException as e:
                    logger.warning(f"[MAPS-LCL] Request error offset={start} attempt={attempt}: {e}")
                    time.sleep(self.RETRY_DELAY * attempt)
                except Exception as e:
                    logger.error(f"[MAPS-LCL] Unexpected error offset={start}: {e}")
                    break
            return []

        # Run offsets in parallel — fast, non-blocking
        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:
            futures = {ex.submit(_fetch_one_offset, s): s for s in [0, 20, 40, 60, 80]}
            for f in concurrent.futures.as_completed(futures):
                try:
                    all_results.extend(f.result())
                except Exception as e:
                    logger.error(f"[MAPS-LCL] Thread error: {e}")

        logger.info(f"[MAPS-LCL] Total: {len(all_results)} for '{keyword}'")
        return all_results

    # ── Yelp scraper (fallback A) ─────────────────────────────────────
    def _scrape_yelp(self, keyword: str, location: str) -> list:
        results = []
        seen = set()
        for page_start in [0, 10, 20, 30]:
            q   = urllib.parse.quote_plus(keyword)
            loc = urllib.parse.quote_plus(location)
            url = f"https://www.yelp.com/search?find_desc={q}&find_loc={loc}&start={page_start}"
            try:
                resp = requests.get(url, headers=get_headers(), timeout=10, verify=False)
                if resp.status_code != 200:
                    continue
                soup = BeautifulSoup(resp.text, 'html.parser')
                biz_links = soup.select('a[href*="/biz/"]')
                for link in biz_links[:15]:
                    name = link.get_text(strip=True)
                    name = re.sub(r'^\d+\.\s*', '', name).strip()
                    if not name or len(name) < 3 or name in seen:
                        continue
                    if any(skip in name.lower() for skip in ['more', 'see all', 'review', 'directions', 'photo']):
                        continue
                    seen.add(name)
                    biz_url = ('https://www.yelp.com' + link['href']
                               if link['href'].startswith('/') else link['href'])
                    text = link.parent.get_text(separator=' ', strip=True) if link.parent else ''
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
                        "Website":     "N/A",
                        "Rating":      rating,
                        "ReviewCount": "0",
                        "Address":     location,
                        "Category":    keyword,
                        "Maps_Link":   f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/",
                        "_yelp_url":   biz_url,
                    })
            except Exception as e:
                logger.debug(f"[YELP] Error: {e}")
            time.sleep(random.uniform(0.5, 1.0))
        logger.info(f"[YELP] {len(results)} businesses for '{keyword}'")
        return results

    # ── Bing scraper (fallback B) ─────────────────────────────────────
    def _scrape_bing(self, keyword: str, location: str) -> list:
        results = []
        seen = set()
        query = urllib.parse.quote_plus(f"{keyword} near {location}")
        url = f"https://www.bing.com/search?q={query}&count=30&setlang=en"
        try:
            resp = requests.get(url, headers=get_headers(), timeout=10, verify=False)
            if resp.status_code != 200:
                return results
            soup = BeautifulSoup(resp.text, 'html.parser')
            for item in soup.select('li.b_algo')[:20]:
                name_el = item.select_one('h2 a, h3 a')
                if not name_el:
                    continue
                name = name_el.get_text(strip=True)
                if not name or len(name) < 3 or name in seen:
                    continue
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
                    "Maps_Link":   f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/",
                })
        except Exception as e:
            logger.debug(f"[BING] Error: {e}")
        logger.info(f"[BING] {len(results)} businesses for '{keyword}'")
        return results

    # ── [PROBLEM 3] Apify fallback ────────────────────────────────────
    def _scrape_apify(self, keyword: str, location: str, apify_key: str) -> list:
        """
        [PROBLEM 3 — APIFY FALLBACK]
        Uses Apify compass/crawler-google-places actor when local scraping is blocked.
        Returns same lead dict format as the main scraper.
        """
        if not apify_key:
            return []
        logger.info(f"[APIFY] Triggering fallback for '{keyword}' in '{location}'")
        results = []
        try:
            # Start Apify run
            run_url = "https://api.apify.com/v2/acts/compass~crawler-google-places/runs"
            payload = {
                "searchStringsArray": [f"{keyword} {location}"],
                "maxCrawledPlaces": 50,
                "language": "en",
                "exportPlaceUrls": False,
            }
            headers = {"Authorization": f"Bearer {apify_key}", "Content-Type": "application/json"}
            run_resp = requests.post(run_url, json=payload, headers=headers, timeout=30)
            if run_resp.status_code not in (200, 201):
                logger.warning(f"[APIFY] Run start failed: {run_resp.status_code}")
                return results

            run_id = run_resp.json().get('data', {}).get('id')
            if not run_id:
                return results

            # Poll until finished (max 3 min)
            for _ in range(36):
                time.sleep(5)
                status_url = f"https://api.apify.com/v2/acts/compass~crawler-google-places/runs/{run_id}"
                st = requests.get(status_url, headers=headers, timeout=10).json()
                if st.get('data', {}).get('status') in ('SUCCEEDED', 'FAILED', 'ABORTED'):
                    break

            # Fetch dataset
            ds_id = run_resp.json().get('data', {}).get('defaultDatasetId', '')
            items_url = f"https://api.apify.com/v2/datasets/{ds_id}/items?format=json&clean=true"
            items = requests.get(items_url, headers=headers, timeout=20).json()

            for item in items:
                name = item.get('title') or item.get('name', 'N/A')
                if not name or name == 'N/A': continue
                # [PROBLEM 5] Rating extracted and stored for sorting
                rating = str(item.get('totalScore', 'N/A'))
                review_count = str(item.get('reviewsCount', '0'))
                website = item.get('website', 'N/A') or 'N/A'
                if website != 'N/A' and not is_valid_business_website(website):
                    website = 'N/A'
                phone = item.get('phone', 'N/A') or 'N/A'
                address = item.get('address', location)
                maps_url = item.get('url', f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/")
                results.append({
                    "Name":        name,
                    "Phone":       phone,
                    "Website":     website,
                    "Rating":      rating,
                    "ReviewCount": review_count,
                    "Address":     address,
                    "Category":    keyword,
                    "Maps_Link":   maps_url,
                })
            logger.info(f"[APIFY] Got {len(results)} results")
        except Exception as e:
            logger.error(f"[APIFY] Error: {e}")
        return results

    # ── Website resolver — 4 stages ───────────────────────────────────
    def resolve_website(self, business_name: str, location: str,
                        existing_url: str = "N/A", yelp_url: str = "N/A") -> str:
        # Stage 1: what the scraper already found
        if is_valid_business_website(existing_url):
            return existing_url

        # Stage 2: Yelp detail page
        if yelp_url and yelp_url != "N/A" and "yelp.com/biz/" in yelp_url:
            try:
                resp = requests.get(yelp_url, headers=get_headers(), timeout=8, verify=False)
                if resp.status_code == 200:
                    soup = BeautifulSoup(resp.text, 'html.parser')
                    for a in soup.select('a[href][target="_blank"]'):
                        href = a.get('href', '')
                        if 'biz_redir' in href or 'redirect_url' in href:
                            parsed = urllib.parse.parse_qs(urllib.parse.urlparse(href).query)
                            u = (parsed.get('url', [None])[0] or
                                 parsed.get('redirect_url', [None])[0])
                            if u and is_valid_business_website(urllib.parse.unquote(u)):
                                return urllib.parse.unquote(u)
                        if is_valid_business_website(href):
                            return href
            except: pass

        # Stage 3: Google search
        for q_str in [
            f'"{business_name}" {location} official website',
            f'{business_name} {location} contact',
        ]:
            try:
                url = f"https://www.google.com/search?q={urllib.parse.quote_plus(q_str)}&num=5&hl=en"
                resp = requests.get(url, headers=get_headers(), timeout=7, verify=False)
                soup = BeautifulSoup(resp.text, 'html.parser')
                for a in soup.select('a[href]'):
                    href = a.get('href', '')
                    if '/url?q=' in href:
                        clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                        if is_valid_business_website(clean):
                            return clean
                    elif is_valid_business_website(href):
                        return href
            except: pass
            time.sleep(0.4)

        # Stage 4: Bing
        try:
            bq = urllib.parse.quote_plus(f"{business_name} {location} website")
            resp = requests.get(f"https://www.bing.com/search?q={bq}&count=5",
                                headers=get_headers(), timeout=7, verify=False)
            soup = BeautifulSoup(resp.text, 'html.parser')
            for a in soup.select('li.b_algo h2 a'):
                href = a.get('href', '')
                if is_valid_business_website(href):
                    return href
        except: pass

        return "N/A"

    # ── Master fetch_batch ────────────────────────────────────────────
    def fetch_batch(self, keyword: str, location: str,
                    job_id: str = None, apify_key: str = "") -> list:
        """
        [PROBLEM 1] Correct scraping from Google Maps + fallbacks.
        [PROBLEM 3] Block detection → Apify fallback.
        [PROBLEM 5] Sort by rating ASC (worst-rated first).
        """
        logger.info(f"[SCRAPE] ═══ '{keyword}' in '{location}' ═══")
        all_leads = []

        # Primary: Google Maps local results (best rating+review data)
        lcl = self._scrape_google_maps_lcl(keyword, location)
        logger.info(f"[SCRAPE] Google Maps LCL → {len(lcl)}")
        all_leads.extend(lcl)

        # Fallback A: Yelp (when Google returns nothing)
        if len(all_leads) < 3:
            yelp = self._scrape_yelp(keyword, location)
            logger.info(f"[SCRAPE] Yelp → {len(yelp)}")
            all_leads.extend(yelp)

        # Fallback B: Bing (additional gap-filler)
        if len(all_leads) < 3:
            bing = self._scrape_bing(keyword, location)
            logger.info(f"[SCRAPE] Bing → {len(bing)}")
            all_leads.extend(bing)

        # [PROBLEM 3] Apify fallback if all sources returned nothing
        if len(all_leads) < 2 and apify_key:
            logger.warning(f"[SCRAPE] Block detected — switching to Apify fallback")
            apify = self._scrape_apify(keyword, location, apify_key)
            logger.info(f"[SCRAPE] Apify → {len(apify)}")
            all_leads.extend(apify)

        # Deduplicate by name within this batch
        seen = set()
        unique = []
        for lead in all_leads:
            key = lead["Name"].strip().lower()
            if key and key != "n/a" and len(key) > 2 and key not in seen:
                seen.add(key)
                unique.append(lead)

        # [PROBLEM 5] Sort: worst rating first (ascending) — N/A at end
        def _sort_key(lead):
            try:
                return float(lead["Rating"])
            except:
                return 6.0
        unique.sort(key=_sort_key)

        logger.info(f"[SCRAPE] ✅ {len(all_leads)} raw → {len(unique)} unique, worst-rated first")
        return unique


# ════════════════════════════════════════════════════
#   DEEP EMAIL EXTRACTOR
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
            '/support', '/help', '/info', '/reach-us', '/get-in-touch',
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
            c = (ob.replace('[at]', '@').replace('(at)', '@')
                   .replace('[dot]', '.').replace('(dot)', '.').replace(' ', ''))
            if '@' in c:
                emails.add(c.lower())
        emails.update(re.findall(
            r'mailto:([a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,})', html
        ))
        return [e for e in emails if self.is_valid_email(e)]

    def crawl_page(self, url: str, timeout: int = 7) -> str:
        try:
            r = requests.get(url, headers=get_headers(), timeout=timeout,
                             verify=False, allow_redirects=True)
            if r.status_code == 200:
                return r.text
        except: pass
        return ""

    def get_internal_links(self, html: str, base_url: str) -> list:
        soup = BeautifulSoup(html, 'html.parser')
        KW = ['contact', 'about', 'support', 'help', 'reach', 'info', 'team']
        links = []
        for a in soup.select('a[href]'):
            href = a.get('href', '').lower()
            if any(kw in href for kw in KW):
                full = urllib.parse.urljoin(base_url, a['href'])
                if full.startswith('http'):
                    links.append(full)
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
                    return emails[0]
                for link in self.get_internal_links(html, url)[:4]:
                    if link in visited: continue
                    ph = self.crawl_page(link)
                    visited.add(link)
                    if ph:
                        e2 = self.extract_from_html(ph)
                        if e2: return e2[0]
            for path in self.CONTACT_PATHS:
                attempt = base + path
                if attempt in visited: continue
                ph = self.crawl_page(attempt, timeout=5)
                visited.add(attempt)
                if ph:
                    e3 = self.extract_from_html(ph)
                    if e3: return e3[0]
        except: pass
        return "N/A"


# ════════════════════════════════════════════════════
#   AI EMAIL PERSONALIZER
# ════════════════════════════════════════════════════
def personalize_email(lead_name, niche, template_subject, template_body, rating):
    if not GROQ_API_KEY:
        return template_subject, template_body, ""
    try:
        client = Groq(api_key=GROQ_API_KEY)
        prompt = f"""Expert cold email copywriter. Personalize this email.
Business: {lead_name}  Niche: {niche}  Rating: {rating}
Subject: {template_subject}
Body: {template_body}
Return ONLY valid JSON: {{"subject":..., "body":..., "personalization_line":...}}"""
        res = client.chat.completions.create(
            messages=[{"role": "user", "content": prompt}],
            model="llama3-8b-8192", temperature=0.5,
        )
        m = re.search(r'\{.*\}', res.choices[0].message.content, re.DOTALL)
        if m:
            d = json.loads(m.group(0))
            return (d.get("subject", template_subject),
                    d.get("body", template_body),
                    d.get("personalization_line", ""))
        return template_subject, template_body, ""
    except Exception as e:
        logger.warning(f"[EMAIL-AI] personalize failed: {e}")
        return template_subject, template_body, ""


# ════════════════════════════════════════════════════
#   MASTER JOB RUNNER
#   [PROBLEM 2] Every inner loop checks stop flag frequently
#   [PROBLEM 6] Once target reached, email phase starts immediately
#   Flow: scrape base keyword → process fully → if not met → one new keyword → repeat
# ════════════════════════════════════════════════════
latest_job_id: str = None

def run_job_thread(job_id: str, data: dict):
    global latest_job_id

    # Initialise job dict FIRST so /api/status never sees missing key
    jobs[job_id] = {
        'status':        'starting',
        'count':         0,
        'leads':         [],
        'emails_sent':   0,
        'total_to_send': 0,
        'status_text':   'Initialising…',
        'is_running':    True,
        'stats': {
            'scraped_total':       0,
            'after_rating_filter': 0,
            'duplicates_skipped':  0,
            'emails_found':        0,
            'errors':              0,
            'keywords_used':       0,
            'keywords_generated':  0,
            'apify_used':          0,
        },
    }

    try:
        location       = data.get('location', '').strip()
        base_keyword   = data.get('keyword', '').strip()
        max_leads      = min(int(data.get('max_leads', 10)), 200)
        max_rating     = data.get('max_rating')
        webhook_url    = data.get('webhook_url', '') or get_settings().get('webhook_url', '')
        db_webhook_url = data.get('db_webhook_url', '') or get_settings().get('db_webhook_url', '')
        templates      = data.get('templates', []) or get_settings().get('templates', [])
        apify_key      = data.get('apify_api_key', '') or get_settings().get('apify_api_key', '')

        max_rating_float = None
        if max_rating:
            try:
                max_rating_float = float(str(max_rating).replace(',', '.'))
                logger.info(f"[JOB] Rating filter: <= {max_rating_float}")
            except:
                logger.warning(f"[JOB] Invalid max_rating '{max_rating}'")

        maps_scraper = GoogleMapsScraper()
        email_lib    = DeepEmailExtractor()
        kw_engine    = AdvancedKeywordEngine()
        db           = GoogleSheetsDB(db_webhook_url)
        dedup        = DeduplicationStore()

        # Consecutive-zero-result counter for block detection
        _zero_streak = 0
        _BLOCK_THRESHOLD = 3  # switch to Apify after 3 empty results in a row

        jobs[job_id].update({
            'status':      'scraping',
            'status_text': f'Starting scrape: {base_keyword} in {location}...',
        })

        if db_webhook_url:
            db.send_action("init", {})
            db.send_action("update_config", {
                "keyword_seed": base_keyword, "location": location,
                "target_leads": max_leads, "min_rating": "",
                "max_rating": max_rating or "", "email_required": "true",
                "status": "running",
            })
            db.log("Job Start", f"kw='{base_keyword}' loc='{location}' target={max_leads}")

        used_keywords  = set()
        _one_kw_pool: list = []     # lazily populated one-by-one keyword pool
        _pool_built    = False

        def _next_single_keyword() -> str:
            """Pop ONE keyword — expand pool when exhausted."""
            nonlocal _pool_built
            while _one_kw_pool:
                kw = _one_kw_pool.pop(0)
                if kw.lower() not in used_keywords:
                    return kw
            # Try AI single-keyword first
            new_kw = kw_engine.generate_single_keyword(base_keyword, location, used_keywords)
            if new_kw:
                logger.info(f"[KW] Single keyword: '{new_kw}'")
                db.send_action("add_keyword", {"keyword": new_kw, "source_seed": base_keyword, "status": "pending"})
                return new_kw
            # Fallback: generate a pool, drain one at a time
            if not _pool_built:
                new_kws = kw_engine.generate_full_pool(base_keyword, location, used_keywords)
                _pool_built = True
            else:
                new_kws = kw_engine.ai_generate(base_keyword, location, used_keywords)
            random.shuffle(new_kws)
            _one_kw_pool.extend([k for k in new_kws if k.lower() not in used_keywords])
            jobs[job_id]['stats']['keywords_generated'] += len(new_kws)
            for kw in new_kws:
                db.send_action("add_keyword", {"keyword": kw, "source_seed": base_keyword, "status": "pending"})
            while _one_kw_pool:
                kw = _one_kw_pool.pop(0)
                if kw.lower() not in used_keywords:
                    return kw
            return f"top {base_keyword} {location}"

        def _process_lead_batch(raw_leads: list, current_kw: str) -> bool:
            """
            Process one batch fully.
            Returns True if target reached OR stop requested.
            """
            nonlocal _zero_streak
            jobs[job_id]['stats']['scraped_total'] += len(raw_leads)
            logger.info(f"[JOB] {len(raw_leads)} businesses from '{current_kw}'")

            for lead in raw_leads:
                # [PROBLEM 2] Check stop flag frequently inside lead loop
                if _should_stop(job_id):
                    logger.info("[JOB] 🛑 STOP — breaking lead loop")
                    return True
                if len(jobs[job_id]['leads']) >= max_leads:
                    logger.info(f"[JOB] 🎯 TARGET {max_leads} reached")
                    return True

                # [PROBLEM 4] Maps URL always preserved
                maps_url = lead.get('Maps_Link') or (
                    f"https://www.google.com/maps/search/"
                    f"{urllib.parse.quote_plus(lead['Name'] + ' ' + location)}/"
                )
                lead['Maps_Link'] = maps_url

                logger.info(
                    f"[JOB] '{lead['Name']}' rating={lead['Rating']} "
                    f"reviews={lead.get('ReviewCount','?')} website={lead['Website']}"
                )

                # Save raw to DB with full data
                db.send_action("add_scraped", {
                    "business_name": lead['Name'],
                    "address":       lead['Address'],
                    "phone":         lead['Phone'],
                    "rating":        lead['Rating'],
                    "review_count":  lead.get('ReviewCount', 'N/A'),
                    "website":       lead['Website'],
                    "maps_url":      maps_url,
                    "keyword":       current_kw,
                    "status":        "scraped",
                })

                # Rating filter
                if max_rating_float is not None and lead['Rating'] != "N/A":
                    try:
                        r_val = float(lead['Rating'])
                        if r_val > max_rating_float:
                            logger.info(f"[FILTER] ❌ {lead['Name']} rating={r_val} > {max_rating_float}")
                            continue
                        logger.info(f"[FILTER] ✅ {lead['Name']} rating={r_val}")
                    except ValueError:
                        pass

                jobs[job_id]['stats']['after_rating_filter'] += 1

                # Website resolution (4-stage)
                existing_url = lead.get('Website', 'N/A')
                yelp_url     = lead.get('_yelp_url', 'N/A')
                if is_valid_business_website(existing_url):
                    website = existing_url
                else:
                    jobs[job_id]['status_text'] = f"Resolving website: {lead['Name']}..."
                    website = maps_scraper.resolve_website(lead['Name'], location, existing_url, yelp_url)
                    lead['Website'] = website

                if not is_valid_business_website(website):
                    logger.info(f"[WEBSITE] ❌ No valid website for '{lead['Name']}'")
                    continue

                # Pre-email dedup
                if dedup.is_duplicate(lead['Name'], location, website, ""):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] Pre-email dup: '{lead['Name']}'")
                    continue

                # [PROBLEM 2] Check stop again before slow email extraction
                if _should_stop(job_id):
                    return True

                # Email extraction
                jobs[job_id]['status_text'] = f"Extracting email: {lead['Name']}..."
                extracted_email = email_lib.get_email(website)
                if extracted_email == "N/A":
                    logger.info(f"[EMAIL] ❌ No email at {website}")
                    continue

                jobs[job_id]['stats']['emails_found'] += 1
                logger.info(f"[EMAIL] ✅ {extracted_email} for '{lead['Name']}'")

                # Post-email dedup
                if dedup.is_duplicate(lead['Name'], location, website, extracted_email):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] Post-email dup: '{lead['Name']}' / {extracted_email}")
                    continue

                dedup.register(lead['Name'], location, website, extracted_email)

                # Save qualified lead with ALL data
                db.send_action("add_email_lead", {
                    "business_name": lead['Name'], "website": website,
                    "email": extracted_email, "source_page": website, "status": "qualified",
                })
                db.send_action("add_qualified", {
                    "business_name": lead['Name'],
                    "address":       lead.get('Address', 'N/A'),
                    "phone":         lead.get('Phone', 'N/A'),
                    "rating":        lead.get('Rating', 'N/A'),
                    "review_count":  lead.get('ReviewCount', 'N/A'),
                    "website":       website,
                    "email":         extracted_email,
                    "maps_url":      maps_url,
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
                    f"'{lead['Name']}' | {extracted_email}"
                )
                jobs[job_id]['status_text'] = (
                    f"✅ {jobs[job_id]['count']}/{max_leads} leads — "
                    f"latest: {lead['Name']}"
                )

                if len(jobs[job_id]['leads']) >= max_leads:
                    return True

            return False

        # ── MAIN SCRAPING LOOP ──────────────────────────────────────────
        # [PROBLEM 6] Flow: scrape → process → check → ONE new keyword → repeat
        current_keyword = base_keyword

        while len(jobs[job_id]['leads']) < max_leads:
            # [PROBLEM 2] Stop check at top of every iteration
            if _should_stop(job_id):
                logger.info("[JOB] 🛑 STOP — exiting main loop")
                break

            used_keywords.add(current_keyword.lower())
            jobs[job_id]['stats']['keywords_used'] += 1

            jobs[job_id]['status_text'] = f"Scraping: '{current_keyword}' in '{location}'..."
            logger.info(
                f"[JOB] Keyword #{jobs[job_id]['stats']['keywords_used']}: "
                f"'{current_keyword}' | leads: {len(jobs[job_id]['leads'])}/{max_leads}"
            )

            # [PROBLEM 3] Pass apify_key so _scrape_apify can be used if blocked
            raw_leads = maps_scraper.fetch_batch(
                current_keyword, location, job_id=job_id, apify_key=apify_key
            )

            if not raw_leads:
                _zero_streak += 1
                logger.info(f"[JOB] No results for '{current_keyword}' (zero streak: {_zero_streak})")
                if _zero_streak >= _BLOCK_THRESHOLD and apify_key:
                    logger.warning("[JOB] Block threshold reached — using Apify for next keyword")
                    jobs[job_id]['stats']['apify_used'] += 1
                # Get next keyword and continue
            else:
                _zero_streak = 0
                if _should_stop(job_id): break
                target_reached = _process_lead_batch(raw_leads, current_keyword)
                if target_reached:
                    logger.info("[JOB] STOP: target reached or stop requested")
                    break

            logger.info(f"[JOB] Qualified: {len(jobs[job_id]['leads'])}/{max_leads}")
            if _should_stop(job_id): break

            # Get ONE next keyword
            nxt = _next_single_keyword()
            if not nxt:
                logger.info("[JOB] Keyword pool exhausted")
                break
            current_keyword = nxt
            time.sleep(random.uniform(0.8, 1.8))

        # ── Phase wrap-up ───────────────────────────────────────────────
        s = jobs[job_id]['stats']
        final_count   = len(jobs[job_id]['leads'])
        stopped_early = _should_stop(job_id)

        logger.info(
            f"[JOB] {'STOPPED' if stopped_early else 'COMPLETE'} — "
            f"scraped={s['scraped_total']} filter={s['after_rating_filter']} "
            f"emails={s['emails_found']} dupes={s['duplicates_skipped']} "
            f"kw={s['keywords_used']} final={final_count}"
        )
        db.send_action("update_config", {
            "keyword_seed": base_keyword, "location": location,
            "target_leads": max_leads, "min_rating": "",
            "max_rating": max_rating or "", "email_required": "true",
            "status": "stopped" if stopped_early else "done",
        })
        db.log("Scraping Done", f"Qualified: {final_count}")

        final_leads = jobs[job_id]['leads']

        # ── [PROBLEM 6] Email phase starts immediately after target met ──
        # [PROBLEM 4] Separate Send Email / Stop Email control
        if webhook_url and templates and final_leads and not stopped_early:
            jobs[job_id]['status'] = 'sending_emails'
            jobs[job_id]['total_to_send'] = len(final_leads)
            emails_sent = 0

            for lead in final_leads:
                # [PROBLEM 4] Check email-stop flag
                if _email_should_stop(job_id):
                    logger.info("[JOB] 🛑 STOP EMAIL — aborting send loop")
                    break
                # [PROBLEM 2] Also check main stop flag
                if _should_stop(job_id):
                    break

                jobs[job_id]['status_text'] = (
                    f"Sending {emails_sent + 1}/{len(final_leads)} → {lead['Email']}"
                )
                template = random.choice(templates)
                p_subject, p_body, p_line = personalize_email(
                    lead['Name'], base_keyword,
                    template['subject'], template['body'], lead['Rating']
                )
                try:
                    requests.post(
                        webhook_url,
                        json={"to": lead['Email'], "subject": p_subject, "body": p_body},
                        timeout=10
                    )
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

                # Anti-spam cooldown with frequent stop checks
                if emails_sent < len(final_leads):
                    delay = random.randint(60, 120)
                    for i in range(delay, 0, -1):
                        # [PROBLEM 2] Check every second — near-instant stop
                        if _email_should_stop(job_id) or _should_stop(job_id):
                            logger.info("[JOB] 🛑 STOP during email cooldown")
                            break
                        jobs[job_id]['status_text'] = f"Cooldown: {i}s..."
                        time.sleep(1)

        # Final status
        if _should_stop(job_id) or _email_should_stop(job_id):
            jobs[job_id]['status'] = 'stopped'
            jobs[job_id]['status_text'] = f"🛑 Stopped. {final_count} leads collected."
        else:
            jobs[job_id]['status'] = 'done'
            jobs[job_id]['status_text'] = f"✅ Done! {final_count} qualified leads."

        jobs[job_id]['is_running'] = False
        db.log("Complete", f"Leads: {final_count}")

    except Exception as e:
        logger.error(f"[JOB] ❌ Fatal: {e}", exc_info=True)
        jobs[job_id]['status']     = 'error'
        jobs[job_id]['error']      = str(e)
        jobs[job_id]['is_running'] = False


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
h1,h2,h3{font-family:'Syne',sans-serif}
.wrap{max-width:940px;margin:0 auto;padding:0 16px}
.nav{background:var(--surface);border-bottom:1px solid var(--border);position:sticky;top:0;z-index:40}
.nav-inner{display:flex;align-items:center;justify-content:space-between;padding:13px 16px;max-width:940px;margin:0 auto}
.brand{display:flex;align-items:center;gap:10px}
.logo{width:34px;height:34px;background:var(--accent);border-radius:8px;display:flex;align-items:center;justify-content:center;color:#fff;font-size:15px;flex-shrink:0}
.nav-title{font-family:'Syne',sans-serif;font-size:15px;font-weight:700}
.nav-title span{color:var(--accent)}
.nav-sub{font-size:11px;color:var(--ink3)}
.run-pill{display:inline-flex;align-items:center;gap:6px;font-size:12px;font-weight:700;padding:4px 12px;border-radius:99px}
.run-pill.running{background:rgba(30,138,94,.12);color:var(--green)}
.run-pill.stopped{background:rgba(160,158,151,.12);color:var(--ink3)}
.run-pill.error{background:rgba(192,57,43,.1);color:var(--red)}
.stats{display:grid;grid-template-columns:repeat(4,1fr);gap:10px;margin:20px 0}
@media(max-width:600px){.stats{grid-template-columns:repeat(2,1fr)}}
.sc{background:var(--surface);border:1px solid var(--border);border-radius:var(--r);padding:14px 16px;box-shadow:var(--shadow)}
.sv{font-family:'Syne',sans-serif;font-size:26px;font-weight:700;line-height:1}
.sl{font-size:11px;color:var(--ink3);margin-top:4px;font-weight:500;text-transform:uppercase;letter-spacing:.04em}
.dot{width:7px;height:7px;border-radius:50%;display:inline-block;margin-right:5px}
.tabs{display:flex;gap:2px;overflow-x:auto;border-bottom:2px solid var(--border);margin-bottom:20px;-webkit-overflow-scrolling:touch;scrollbar-width:none;padding-bottom:1px}
.tabs::-webkit-scrollbar{display:none}
.tab{background:none;border:none;padding:9px 14px;font-size:13px;font-weight:600;color:var(--ink3);cursor:pointer;white-space:nowrap;border-bottom:2px solid transparent;margin-bottom:-2px;transition:color .15s,border-color .15s;font-family:'Outfit',sans-serif;border-radius:6px 6px 0 0}
.tab:hover{color:var(--ink)}
.tab.on{color:var(--accent);border-bottom-color:var(--accent)}
.card{background:var(--surface);border:1px solid var(--border);border-radius:var(--r);padding:20px;box-shadow:var(--shadow);margin-bottom:16px}
.ct{font-family:'Syne',sans-serif;font-size:14px;font-weight:700;display:flex;align-items:center;gap:8px;margin-bottom:16px}
.ct i{color:var(--accent);width:16px;text-align:center}
.fg{display:flex;flex-direction:column;gap:5px}
.grid2{display:grid;grid-template-columns:1fr 1fr;gap:12px}
@media(max-width:560px){.grid2{grid-template-columns:1fr}}
label{font-size:12px;font-weight:600;color:var(--ink2);letter-spacing:.01em;text-transform:uppercase}
.inp{background:var(--bg);border:1.5px solid var(--border);color:var(--ink);border-radius:8px;padding:10px 13px;font-size:14px;width:100%;font-family:'Outfit',sans-serif;transition:border .15s,box-shadow .15s;outline:none}
.inp:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(212,82,42,.1)}
.inp:disabled{opacity:.55;cursor:not-allowed;background:var(--surface2)}
.inp::placeholder{color:var(--ink3)}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;border:none;border-radius:8px;font-weight:600;font-size:14px;cursor:pointer;transition:all .15s;font-family:'Outfit',sans-serif;padding:11px 20px;white-space:nowrap}
.btn:disabled{opacity:.4;cursor:not-allowed;pointer-events:none}
.btn-p{background:var(--accent);color:#fff}
.btn-p:hover{background:var(--accent-h);transform:translateY(-1px);box-shadow:0 4px 14px rgba(212,82,42,.3)}
.btn-g{background:var(--green);color:#fff}
.btn-g:hover{filter:brightness(1.1);transform:translateY(-1px)}
.btn-r{background:var(--red);color:#fff}
.btn-r:hover{filter:brightness(1.1);transform:translateY(-1px)}
.btn-n{background:var(--surface2);color:var(--ink);border:1.5px solid var(--border)}
.btn-n:hover{border-color:var(--ink2)}
.btn-ghost{background:none;color:var(--ink3);border:1.5px solid var(--border);font-size:12px;padding:7px 13px}
.btn-ghost:hover{color:var(--red);border-color:var(--red)}
.btn-full{width:100%}
.btn-row{display:flex;gap:8px;margin-top:12px;flex-wrap:wrap}
.btn-row .btn{flex:1;min-width:120px}
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
.notice{border-radius:8px;padding:10px 13px;font-size:12px;font-weight:500;margin-bottom:12px;display:flex;gap:8px;align-items:flex-start}
.notice i{margin-top:1px;flex-shrink:0}
.n-warn{background:rgba(201,130,10,.08);border:1px solid rgba(201,130,10,.2);color:#7a4f00}
.n-info{background:rgba(41,98,168,.07);border:1px solid rgba(41,98,168,.15);color:#183d6d}
.ti{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px;position:relative}
.tn{font-family:'Syne',sans-serif;font-size:13px;font-weight:700;margin-bottom:3px}
.ts{font-size:12px;color:var(--blue);margin-bottom:4px}
.tb2{font-size:11px;color:var(--ink3);overflow:hidden;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical}
.tdel{position:absolute;top:10px;right:10px;background:none;border:none;color:var(--ink3);cursor:pointer;font-size:13px;padding:4px}
.tdel:hover{color:var(--red)}
.hi{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px}
/* Lock / PIN */
.lock-row{display:flex;align-items:center;gap:10px;padding:10px 13px;border:1.5px solid var(--border);border-radius:8px;margin-bottom:12px;background:var(--surface2)}
.lock-ico{font-size:18px;flex-shrink:0}
.lock-ico.locked{color:var(--red)}.lock-ico.unlocked{color:var(--green)}
.lock-lbl{flex:1;font-size:13px;font-weight:600}
.lock-sub{font-size:11px;color:var(--ink3);margin-top:1px}
.modal-overlay{position:fixed;inset:0;background:rgba(0,0,0,.45);display:flex;align-items:center;justify-content:center;z-index:100;backdrop-filter:blur(4px)}
.modal{background:var(--surface);border-radius:14px;padding:28px;width:320px;max-width:90vw;box-shadow:0 20px 60px rgba(0,0,0,.2)}
.pin-in{font-size:24px;text-align:center;letter-spacing:12px;font-family:'Syne',sans-serif}
.pin-err{color:var(--red);font-size:12px;text-align:center;margin-top:8px;min-height:18px}
.spin{animation:spin 1s linear infinite}
.blink{animation:bl 1.3s ease infinite}
@keyframes spin{to{transform:rotate(360deg)}}
@keyframes bl{0%,100%{opacity:1}50%{opacity:.3}}
.fade{animation:fi .25s ease}
@keyframes fi{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:translateY(0)}}
.hidden{display:none!important}
.flex{display:flex}.ac{align-items:center}.jb{justify-content:space-between}
.gap2{gap:8px}.gap3{gap:12px}.mt2{margin-top:8px}.mt3{margin-top:12px}
.xs{font-size:11px}.sm{font-size:12px}.muted{color:var(--ink3)}.bold{font-weight:700}
.space-y>*+*{margin-top:10px}
@media(max-width:480px){.card{padding:14px}.btn{font-size:13px;padding:10px 16px}.sv{font-size:22px}}
</style>
</head>
<body>

<!-- PIN MODAL -->
<div id="pin-modal" class="modal-overlay hidden">
  <div class="modal">
    <h3 style="font-family:'Syne',sans-serif;font-size:18px;font-weight:700;margin-bottom:6px">🔒 Enter PIN</h3>
    <p id="pin-modal-label" class="sm muted" style="margin-bottom:20px">PIN required to unlock this section.</p>
    <input id="pin-input" class="inp pin-in" type="password" maxlength="4" placeholder="••••" autocomplete="off">
    <div id="pin-error" class="pin-err"></div>
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
        <div class="nav-title">Lead<span>Gen</span> Pro</div>
        <div class="nav-sub">Scrape · Filter · Email</div>
      </div>
    </div>
    <div id="run-pill" class="run-pill stopped">
      <i class="fa-solid fa-circle" style="font-size:8px"></i>
      <span id="run-text">Idle</span>
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
    <button class="tab"    id="tab-apify"     onclick="showTab('apify')"><i class="fa-solid fa-shield-halved"></i> Apify</button>
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
        <span><b>Flow:</b> Scrapes Google Maps (rating+reviews) → ONE keyword at a time → 4-stage website resolver → email extraction → if blocked, Apify takes over. Worst-rated first.</span>
      </div>
      <!-- Scraping controls -->
      <div class="btn-row">
        <button onclick="startJob()" id="btn-run" class="btn btn-p">
          <i class="fa-solid fa-play"></i>Start Scraping
        </button>
        <button onclick="stopJob()" id="btn-stop" class="btn btn-r" disabled>
          <i class="fa-solid fa-stop"></i>Stop
        </button>
      </div>
      <!-- [PROBLEM 4] Send Email / Stop Email buttons -->
      <div class="btn-row">
        <button onclick="sendEmails()" id="btn-send-email" class="btn btn-g" disabled>
          <i class="fa-solid fa-envelope"></i>Send Emails
        </button>
        <button onclick="stopEmails()" id="btn-stop-email" class="btn btn-n" disabled>
          <i class="fa-solid fa-envelope-circle-check"></i>Stop Email
        </button>
      </div>
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
        <div class="ct" style="margin-bottom:0"><i class="fa-solid fa-table-cells"></i>Preview <span id="pvcnt" class="muted sm"></span></div>
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
      <!-- [PROBLEM 3 PIN] Lock row -->
      <div class="lock-row">
        <i id="db-lock-ico" class="fa-solid fa-lock lock-ico locked"></i>
        <div>
          <div class="lock-lbl" id="db-lock-lbl">Database — Locked</div>
          <div class="lock-sub">Enter PIN 0123 to configure</div>
        </div>
        <button id="db-unlock-btn" onclick="requestPin('database')" class="btn btn-n sm" style="padding:7px 13px">Unlock</button>
      </div>
      <div id="db-content" class="hidden">
        <div class="notice n-info"><i class="fa-solid fa-circle-info"></i>
          <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → New Project → paste script → Deploy as Web App (Anyone) → copy URL. <b>Saved to server — works on all devices.</b></span>
        </div>
        <div style="position:relative;margin-bottom:14px">
          <button onclick="copyDBScript()" class="btn btn-n" style="position:absolute;top:8px;right:8px;font-size:11px;padding:5px 10px;z-index:1">Copy</button>
          <textarea id="db-script-code" readonly class="inp" style="font-family:monospace;font-size:11px;height:170px;resize:none;padding-top:10px;color:var(--blue)">
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
      getOrCreateSheet("Qualified_Leads",["business_name","address","phone","rating","review_count","website","email","maps_url","keyword","personalization_line","email_sent"]);
      getOrCreateSheet("Logs",["timestamp","action","details"]);
    } else if (action === "log") { var s=ss.getSheetByName("Logs"); if(s) s.appendRow([data.timestamp,data.action,data.details]); }
    else if (action === "add_keyword") { var s=ss.getSheetByName("Generated_Keywords"); if(s) s.appendRow([data.keyword,data.source_seed,data.status]); }
    else if (action === "add_scraped") { var s=ss.getSheetByName("Scraped_Businesses"); if(s) s.appendRow([data.business_name,data.address,data.phone,data.rating,data.review_count,data.website,data.maps_url||"",data.keyword,data.status]); }
    else if (action === "add_email_lead") { var s=ss.getSheetByName("Email_Leads"); if(s) s.appendRow([data.business_name,data.website,data.email,data.source_page,data.status]); }
    else if (action === "add_qualified") { var s=ss.getSheetByName("Qualified_Leads"); if(s) s.appendRow([data.business_name,data.address||"",data.phone||"",data.rating||"",data.review_count||"",data.website,data.email,data.maps_url||"",data.keyword,data.personalization_line,data.email_sent]); }
    else if (action === "update_config") { var s=ss.getSheetByName("Config"); if(s){s.clearContents();s.appendRow(["keyword_seed","location","target_leads","min_rating","max_rating","email_required","status"]);s.appendRow([data.keyword_seed,data.location,data.target_leads,data.min_rating,data.max_rating,data.email_required,data.status]);} }
    else if (action === "update_email_sent") { var s=ss.getSheetByName("Qualified_Leads"); if(s){var v=s.getDataRange().getValues();for(var i=1;i<v.length;i++){if(v[i][6]===data.email){s.getRange(i+1,10).setValue(data.personalization_line);s.getRange(i+1,11).setValue("yes");break;}}} }
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
      <div class="lock-row">
        <i id="email-lock-ico" class="fa-solid fa-lock lock-ico locked"></i>
        <div>
          <div class="lock-lbl" id="email-lock-lbl">Email Connection — Locked</div>
          <div class="lock-sub">Enter PIN 0123 to configure</div>
        </div>
        <button id="email-unlock-btn" onclick="requestPin('email')" class="btn btn-n sm" style="padding:7px 13px">Unlock</button>
      </div>
      <div id="email-content" class="hidden">
        <div class="notice n-info"><i class="fa-solid fa-circle-info"></i>
          <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → paste code → Deploy as Web App (Anyone) → copy URL. <b>Saved to server.</b></span>
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

  <!-- ═══ APIFY ═══ -->
  <!-- [PROBLEM 7] Apify API input UI -->
  <div id="pane-apify" class="hidden fade">
    <div class="card">
      <div class="ct"><i class="fa-solid fa-shield-halved"></i>Apify Fallback Scraper</div>
      <div class="notice n-warn">
        <i class="fa-solid fa-triangle-exclamation"></i>
        <span>When Google/Bing/Yelp return no results for 3 consecutive keywords (IP blocked), the system automatically switches to Apify actor <b>compass/crawler-google-places</b>.</span>
      </div>
      <div class="lock-row">
        <i id="apify-lock-ico" class="fa-solid fa-lock lock-ico locked"></i>
        <div>
          <div class="lock-lbl" id="apify-lock-lbl">Apify API Key — Locked</div>
          <div class="lock-sub">Enter PIN 0123 to configure</div>
        </div>
        <button id="apify-unlock-btn" onclick="requestPin('apify')" class="btn btn-n sm" style="padding:7px 13px">Unlock</button>
      </div>
      <div id="apify-content" class="hidden">
        <p class="sm muted" style="margin-bottom:14px">Get your API key from <a href="https://console.apify.com/account/integrations" target="_blank" style="color:var(--blue)">console.apify.com</a> → Account → Integrations.</p>
        <div class="fg" style="margin-bottom:12px">
          <label>🔑 Apify API Key</label>
          <input id="apify-api-key" class="inp" placeholder="apify_api_xxxxxxxxxxxxxxxx" type="password">
        </div>
        <button onclick="saveApifyKey()" class="btn btn-p btn-full"><i class="fa-solid fa-save"></i>Save Apify Key</button>
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

</div>

<script>
// ── State ──
let jid=null, templates=[], historyData=[], tableShown=false, pollTimer=null;
let pinTarget='';

// ── Boot ──
window.onload = async () => {
  historyData = JSON.parse(localStorage.getItem('lgp_history')||'[]');
  renderHistory();
  await loadServerSettings();
  await restoreActiveJob();
  document.getElementById('pin-input').addEventListener('keydown', e => { if(e.key==='Enter') pinConfirm(); });
};

async function loadServerSettings() {
  try {
    const r = await fetch('/api/settings');
    const d = await r.json();
    document.getElementById('webhook-url').value    = d.webhook_url    || '';
    document.getElementById('db-webhook-url').value = d.db_webhook_url || '';
    document.getElementById('apify-api-key').value  = d.apify_api_key  || '';
    templates = d.templates || [];
    renderTemplates();
  } catch(e) { console.warn('Settings load failed:', e); }
}

async function restoreActiveJob() {
  try {
    const r = await fetch('/api/global_status');
    const d = await r.json();
    if(!d.job_id || d.status === 'not_found') return;
    jid = d.job_id;
    if(d.leads?.length){ updStats(d.leads); showPV(d.leads); tableShown=true; }
    if(d.status === 'scraping' || d.status === 'sending_emails' || d.status === 'starting') {
      setSt(d.status_text||'Resuming…', d.status==='sending_emails'?'email':'load', 50);
      if(d.stats) renderDbg(d.stats);
      document.getElementById('sbox').classList.remove('hidden');
      setRunUI(true, d.status);
      startPolling(d.count||10);
    } else if(d.status==='done'||d.status==='stopped') {
      setSt(d.status_text||'Done', 'done', 100);
      if(d.stats) renderDbg(d.stats);
      document.getElementById('sbox').classList.remove('hidden');
      if(d.leads?.length) document.getElementById('dlbtn').classList.remove('hidden');
      setRunUI(false, d.status);
    }
  } catch(e) {}
}

// ── PIN System ──
function requestPin(target) {
  pinTarget = target;
  const labels = { database:'Database Connection', email:'Email Connection', apify:'Apify API Key' };
  document.getElementById('pin-modal-label').textContent = `Enter PIN to unlock: ${labels[target]||target}`;
  document.getElementById('pin-input').value = '';
  document.getElementById('pin-error').textContent = '';
  document.getElementById('pin-modal').classList.remove('hidden');
  setTimeout(()=>document.getElementById('pin-input').focus(), 100);
}
function pinCancel() {
  document.getElementById('pin-modal').classList.add('hidden');
  pinTarget = '';
}
async function pinConfirm() {
  const pin = document.getElementById('pin-input').value;
  try {
    const r = await fetch('/api/verify-pin',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({pin})});
    const d = await r.json();
    if(d.ok) {
      document.getElementById('pin-modal').classList.add('hidden');
      unlockSection(pinTarget);
    } else {
      document.getElementById('pin-error').textContent = '❌ Incorrect PIN.';
      document.getElementById('pin-input').value = '';
    }
  } catch(e) { document.getElementById('pin-error').textContent = 'Error.'; }
}
function unlockSection(section) {
  const map = {
    database: ['db-lock-ico','db-lock-lbl','db-unlock-btn','db-content','Database — Unlocked'],
    email:    ['email-lock-ico','email-lock-lbl','email-unlock-btn','email-content','Email — Unlocked'],
    apify:    ['apify-lock-ico','apify-lock-lbl','apify-unlock-btn','apify-content','Apify Key — Unlocked'],
  };
  const [ico,lbl,btn,content,text] = map[section];
  document.getElementById(ico).className = 'fa-solid fa-lock-open lock-ico unlocked';
  document.getElementById(lbl).textContent = text;
  const btnEl = document.getElementById(btn);
  btnEl.textContent = '✓ Unlocked'; btnEl.disabled = true;
  document.getElementById(content).classList.remove('hidden');
}

// ── Save Settings to Server ──
async function saveWebhook()   { const u=document.getElementById('webhook-url').value.trim();    await fetch('/api/settings',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({webhook_url:u})}); alert('Email webhook saved!'); }
async function saveDBWebhook() { const u=document.getElementById('db-webhook-url').value.trim(); await fetch('/api/settings',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({db_webhook_url:u})}); alert('Database webhook saved!'); }
async function saveApifyKey()  { const k=document.getElementById('apify-api-key').value.trim();  await fetch('/api/settings',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({apify_api_key:k})}); alert('Apify key saved!'); }
function copyDBScript() { const el=document.getElementById('db-script-code'); el.select(); document.execCommand('copy'); alert('Script copied!'); }

// ── Tabs ──
const TABS=['search','database','connect','apify','templates','history'];
function showTab(t){TABS.forEach(x=>{document.getElementById('pane-'+x).classList.add('hidden');document.getElementById('tab-'+x).classList.remove('on');});document.getElementById('pane-'+t).classList.remove('hidden');document.getElementById('tab-'+t).classList.add('on');}

// ── Templates ──
async function addTemplate(){
  const n=document.getElementById('t-name').value.trim(), s=document.getElementById('t-sub').value.trim(), b=document.getElementById('t-body').value.trim();
  if(!n||!s||!b) return alert('Fill all template fields!');
  templates.push({name:n,subject:s,body:b});
  await fetch('/api/settings',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({templates})});
  ['t-name','t-sub','t-body'].forEach(id=>document.getElementById(id).value='');
  renderTemplates();
}
async function delTemplate(i){templates.splice(i,1); await fetch('/api/settings',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify({templates})}); renderTemplates();}
function renderTemplates(){
  const el=document.getElementById('t-list');
  if(!templates.length) return el.innerHTML='<p class="xs muted" style="text-align:center;padding:8px">No templates yet.</p>';
  el.innerHTML=templates.map((t,i)=>`<div class="ti"><button class="tdel" onclick="delTemplate(${i})"><i class="fa-solid fa-xmark"></i></button><div class="tn">${t.name}</div><div class="ts">${t.subject}</div><div class="tb2">${t.body.replace(/</g,'&lt;')}</div></div>`).join('');
}
function renderHistory(){const el=document.getElementById('h-list');if(!historyData.length)return el.innerHTML='<p class="xs muted" style="text-align:center;padding:8px">No history yet.</p>';el.innerHTML=historyData.map(h=>`<div class="hi"><div class="bold sm">${h.kw} <span class="muted">in</span> ${h.loc}</div><div class="xs muted mt2">Target: ${h.target} · ${h.date}</div></div>`).join('');}
function clearHistory(){historyData=[];localStorage.removeItem('lgp_history');renderHistory();}

// ── UI State ──
function setRunUI(running, status='') {
  const pill=document.getElementById('run-pill'), txt=document.getElementById('run-text');
  const btnRun=document.getElementById('btn-run'), btnStop=document.getElementById('btn-stop');
  const btnSend=document.getElementById('btn-send-email'), btnStopEmail=document.getElementById('btn-stop-email');
  if(running) {
    pill.className='run-pill running'; txt.textContent='Running';
    btnRun.disabled=true; btnStop.disabled=false;
  } else {
    pill.className='run-pill stopped'; txt.textContent='Idle';
    btnRun.disabled=false; btnStop.disabled=true;
  }
  if(status==='sending_emails') {
    btnSend.disabled=true; btnStopEmail.disabled=false;
  } else if(!running) {
    // Enable Send Email if we have leads
    btnStopEmail.disabled=true;
  }
}

function setSt(msg, state='load', pct=null){
  document.getElementById('sbox').classList.remove('hidden');
  document.getElementById('sdet').textContent=msg;
  const ic=document.getElementById('si'), txt=document.getElementById('stxt');
  const m={load:['fa-circle-notch spin','var(--accent)','Scraping…'],email:['fa-paper-plane blink','var(--green)','Sending Emails…'],done:['fa-circle-check','var(--green)','Completed!'],stopped:['fa-stop-circle','var(--ink3)','Stopped'],err:['fa-circle-xmark','var(--red)','Error']};
  const [cls,col,label]=m[state]||m.load;
  ic.className=`fa-solid ${cls}`; ic.style.color=col; txt.textContent=label;
  if(pct!=null) document.getElementById('sbar').style.width=Math.min(100,pct)+'%';
}
function renderDbg(s){
  if(!s) return;
  document.getElementById('dbg').innerHTML=`
    <span class="chip c-bl" title="Scraped">Scraped: ${s.scraped_total||0}</span>
    <span class="chip c-am" title="After filter">Filtered: ${s.after_rating_filter||0}</span>
    <span class="chip c-gr" title="Emails found">Emails: ${s.emails_found||0}</span>
    <span class="chip c-rd" title="Dupes skipped">Dupes: ${s.duplicates_skipped||0}</span>
    <span class="chip c-pu" title="Keywords used">KW: ${s.keywords_used||0}</span>
    <span class="chip c-rd" title="Errors">Errors: ${s.errors||0}</span>
    ${s.apify_used>0?`<span class="chip c-am" title="Apify fallback used">Apify: ${s.apify_used}</span>`:''}`;
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
  const keys=Object.keys(leads[0]).filter(k=>!k.startsWith('_'));
  document.getElementById('th').innerHTML=keys.map(k=>`<th>${k}</th>`).join('');
  document.getElementById('tb').innerHTML=leads.slice(0,10).map(l=>`<tr>${keys.map(k=>{const v=(l[k]||'N/A').toString();const c=v==='N/A'?'b-na':k==='Email'?'b-ok':k==='Rating'?'b-wa':k==='Phone'?'b-in':'';const d=v.length>40?v.slice(0,40)+'…':v;return `<td>${c?`<span class="badge ${c}">${d}</span>`:d}</td>`;}).join('')}</tr>`).join('');
}

// ── Start / Stop Scraping ──
async function startJob(){
  const loc=document.getElementById('m-loc').value.trim();
  const kw=document.getElementById('m-kw').value.trim();
  let count=Math.min(parseInt(document.getElementById('m-count').value)||10,200);
  if(!loc||!kw) return alert('Location and Keyword are required!');

  setSt(`Starting: ${kw} in ${loc}…`,'load',2);
  document.getElementById('dlbtn').classList.add('hidden');
  document.getElementById('pvbox').classList.add('hidden');
  document.getElementById('dbg').innerHTML='';
  tableShown=false;
  setRunUI(true,'scraping');

  const payload={location:loc,keyword:kw,max_leads:count,
    max_rating:document.getElementById('m-rating').value.trim()||null,
    templates:templates};
  try{
    const r=await fetch('/api/scrape',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});
    const d=await r.json();
    if(d.error){setSt(d.error,'err');setRunUI(false);return;}
    jid=d.job_id;
    historyData.unshift({loc,kw,target:count,date:new Date().toLocaleString()});
    localStorage.setItem('lgp_history',JSON.stringify(historyData)); renderHistory();
    startPolling(count);
  }catch(e){setSt('Server error','err');setRunUI(false);}
}

async function stopJob(){
  if(!jid) return;
  document.getElementById('btn-stop').disabled=true;
  document.getElementById('btn-stop').innerHTML='<i class="fa-solid fa-spinner spin"></i> Stopping…';
  await fetch('/api/stop/'+jid,{method:'POST'});
  setSt('Stop signal sent…','load',null);
}

// ── [PROBLEM 4] Send Email / Stop Email ──
async function sendEmails(){
  if(!jid) return;
  document.getElementById('btn-send-email').disabled=true;
  document.getElementById('btn-stop-email').disabled=false;
  try{
    await fetch('/api/send_emails/'+jid,{method:'POST'});
    setSt('Email automation started…','email',0);
    setRunUI(false,'sending_emails');
    startPolling(document.getElementById('m-count').value||10);
  }catch(e){ alert('Failed to start email sending.'); }
}

async function stopEmails(){
  if(!jid) return;
  await fetch('/api/stop_emails/'+jid,{method:'POST'});
  document.getElementById('btn-stop-email').disabled=true;
  setSt('Email stop signal sent…','load',null);
}

// ── Polling ──
function startPolling(target){
  if(pollTimer) clearTimeout(pollTimer);
  const poll=async()=>{
    try{
      const r2=await fetch('/api/status/'+jid);
      const d2=await r2.json();
      if(d2.stats) renderDbg(d2.stats);
      if(d2.status==='scraping'||d2.status==='starting'){
        setSt(d2.status_text||'Scraping…','load',Math.max(3,(d2.count/target)*95));
        if(d2.leads?.length){updStats(d2.leads);if(!tableShown){showPV(d2.leads);tableShown=true;}}
        pollTimer=setTimeout(poll,2500);
      } else if(d2.status==='sending_emails'){
        if(!tableShown&&d2.leads){updStats(d2.leads);showPV(d2.leads);tableShown=true;}
        document.getElementById('dlbtn').classList.remove('hidden');
        setSt(d2.status_text||'Sending…','email',d2.total_to_send>0?(d2.emails_sent/d2.total_to_send)*100:50);
        setRunUI(false,'sending_emails');
        pollTimer=setTimeout(poll,2500);
      } else if(d2.status==='done'){
        setRunUI(false,'done');
        if(d2.leads){updStats(d2.leads);showPV(d2.leads);}
        setSt(d2.status_text||'Done!','done',100);
        document.getElementById('dlbtn').classList.remove('hidden');
        // Enable Send Email button when leads are ready
        if(d2.leads?.length) document.getElementById('btn-send-email').disabled=false;
        document.getElementById('btn-stop').innerHTML='<i class="fa-solid fa-stop"></i> Stop';
      } else if(d2.status==='stopped'){
        setRunUI(false,'stopped');
        if(d2.leads){updStats(d2.leads);showPV(d2.leads);}
        setSt(d2.status_text||'Stopped','stopped',100);
        if(d2.leads?.length){document.getElementById('dlbtn').classList.remove('hidden');document.getElementById('btn-send-email').disabled=false;}
        document.getElementById('btn-stop').innerHTML='<i class="fa-solid fa-stop"></i> Stop';
      } else if(d2.status==='error'){
        setRunUI(false,'error');
        setSt(d2.error||'Unknown error','err');
      } else { pollTimer=setTimeout(poll,2500); }
    }catch(e){pollTimer=setTimeout(poll,2500);}
  };
  pollTimer=setTimeout(poll,1500);
}
function doDL(){if(jid)window.location='/api/download/'+jid;}
</script>
</body>
</html>"""


@flask_app.route('/')
def index():
    return render_template_string(HTML_TEMPLATE)


@flask_app.route('/api/settings', methods=['GET'])
def get_settings_api():
    return jsonify(get_settings())


@flask_app.route('/api/settings', methods=['POST'])
def save_settings_api():
    data = request.json or {}
    for key in ('webhook_url', 'db_webhook_url', 'apify_api_key', 'templates'):
        if key in data:
            save_settings(key, data[key])
    return jsonify({'ok': True})


@flask_app.route('/api/verify-pin', methods=['POST'])
def verify_pin():
    pin = str((request.json or {}).get('pin', ''))
    ok = (pin == ACCESS_PIN)
    logger.info(f"[PIN] {'OK' if ok else 'FAIL'}")
    return jsonify({'ok': ok})


@flask_app.route('/api/scrape', methods=['POST'])
def start_api_job():
    global latest_job_id
    data = request.json
    job_id = str(uuid.uuid4())[:8]
    logger.info(f"[API] Job {job_id}: kw='{data.get('keyword')}' loc='{data.get('location')}' target={data.get('max_leads')}")
    job_stop_flags[job_id]   = threading.Event()
    email_stop_flags[job_id] = threading.Event()
    latest_job_id = job_id
    t = threading.Thread(target=run_job_thread, args=(job_id, data))
    t.daemon = True
    t.start()
    return jsonify({'job_id': job_id})


@flask_app.route('/api/stop/<job_id>', methods=['POST'])
def stop_job(job_id):
    """[PROBLEM 2] Immediately sets the stop flag — near-instant effect."""
    flag = job_stop_flags.get(job_id)
    if flag:
        flag.set()
        logger.info(f"[API] 🛑 Stop for job {job_id}")
        return jsonify({'status': 'stop_requested'})
    return jsonify({'status': 'not_found'}), 404


@flask_app.route('/api/send_emails/<job_id>', methods=['POST'])
def send_emails_api(job_id):
    """[PROBLEM 4] Trigger email sending phase for an existing completed job."""
    job = jobs.get(job_id)
    if not job:
        return jsonify({'error': 'job not found'}), 404
    leads = job.get('leads', [])
    if not leads:
        return jsonify({'error': 'no leads'}), 400

    settings    = get_settings()
    webhook_url = settings.get('webhook_url', '')
    tmplts      = settings.get('templates', [])
    if not webhook_url or not tmplts:
        return jsonify({'error': 'No email webhook or templates configured'}), 400

    # Reset email stop flag
    email_stop_flags[job_id] = threading.Event()
    jobs[job_id]['status']        = 'sending_emails'
    jobs[job_id]['total_to_send'] = len(leads)
    jobs[job_id]['emails_sent']   = 0

    def _send():
        base_kw = jobs[job_id].get('leads', [{}])[0].get('Category', '')
        emails_sent = 0
        for lead in leads:
            if _email_should_stop(job_id) or _should_stop(job_id):
                break
            template = random.choice(tmplts)
            p_subject, p_body, p_line = personalize_email(
                lead.get('Name', ''), base_kw,
                template['subject'], template['body'], lead.get('Rating', 'N/A')
            )
            try:
                requests.post(webhook_url, json={"to": lead['Email'], "subject": p_subject, "body": p_body}, timeout=10)
                emails_sent += 1
                jobs[job_id]['emails_sent'] = emails_sent
                logger.info(f"[EMAIL-SEND] ✅ {lead['Email']}")
            except Exception as e:
                logger.error(f"[EMAIL-SEND] ❌ {lead['Email']}: {e}")
            if emails_sent < len(leads):
                delay = random.randint(60, 120)
                for i in range(delay, 0, -1):
                    if _email_should_stop(job_id) or _should_stop(job_id): break
                    jobs[job_id]['status_text'] = f"Cooldown: {i}s..."
                    time.sleep(1)
        if _email_should_stop(job_id):
            jobs[job_id]['status'] = 'stopped'
            jobs[job_id]['status_text'] = f"Email stopped. Sent {emails_sent}/{len(leads)}."
        else:
            jobs[job_id]['status'] = 'done'
            jobs[job_id]['status_text'] = f"✅ Emails sent: {emails_sent}/{len(leads)}."
    threading.Thread(target=_send, daemon=True).start()
    return jsonify({'status': 'email_started'})


@flask_app.route('/api/stop_emails/<job_id>', methods=['POST'])
def stop_emails_api(job_id):
    """[PROBLEM 4] Immediately stop email sending."""
    flag = email_stop_flags.get(job_id)
    if flag:
        flag.set()
        logger.info(f"[API] 🛑 Stop email for job {job_id}")
        return jsonify({'status': 'stop_email_requested'})
    return jsonify({'status': 'not_found'}), 404


@flask_app.route('/api/status/<job_id>')
def status(job_id):
    job = jobs.get(job_id, {'status': 'not_found'})
    out = dict(job)
    if out.get('status') in ['sending_emails', 'done', 'scraping', 'stopped', 'starting']:
        out['leads'] = [
            {k: v for k, v in lead.items() if not k.startswith('_')}
            for lead in job.get('leads', [])
        ]
    return jsonify(out)


@flask_app.route('/api/global_status')
def global_status():
    global latest_job_id
    if not latest_job_id or latest_job_id not in jobs:
        return jsonify({'status': 'not_found', 'job_id': None})
    job = jobs[latest_job_id]
    out = dict(job)
    out['job_id'] = latest_job_id
    out['leads']  = [
        {k: v for k, v in lead.items() if not k.startswith('_')}
        for lead in job.get('leads', [])
    ]
    return jsonify(out)


@flask_app.route('/api/download/<job_id>')
def download(job_id):
    job = jobs.get(job_id)
    if not job or job.get('status') not in ['done', 'sending_emails', 'stopped']:
        return "Not ready", 400
    leads = job.get('leads', [])
    if not leads:
        return "No leads found", 404
    export = [{k: v for k, v in l.items() if not k.startswith('_')} for l in leads]
    out = io.StringIO()
    writer = csv.DictWriter(out, fieldnames=export[0].keys())
    writer.writeheader()
    writer.writerows(export)
    out.seek(0)
    return send_file(
        io.BytesIO(out.getvalue().encode('utf-8-sig')),
        mimetype='text/csv', as_attachment=True, download_name='Target_Leads.csv',
    )


# ════════════════════════════════════════════════════
#   TELEGRAM BOT
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
        "👋 *LeadGen Pro Bot*\n\n"
        "✅ Google Maps scraping (rating + reviews)\n"
        "✅ One keyword at a time\n"
        "✅ Worst-rated first\n"
        "✅ 4-stage website resolution\n"
        "✅ Deduplication active\n"
        "✅ Max: 200 leads",
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
    bot_store[update.message.from_user.id]['count'] = count
    await update.message.reply_text("⭐ Max Rating? (type 'skip'):")
    return M_RATING

async def m_rating(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    uid = update.message.from_user.id
    bot_store[uid]['rating'] = None if update.message.text.lower() == 'skip' else update.message.text
    d = bot_store[uid]
    summary = f"📋 *Config*\n📍 {d['loc']}\n🔍 {d['kw']}\n🔢 {d['count']}\n⭐ {d.get('rating') or 'None'}\n\nStart?"
    kb = [[InlineKeyboardButton("✅ Start", callback_data="start_scrape")]]
    await update.message.reply_text(summary, parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(kb))
    return ConversationHandler.END

def run_bot_scrape_fast(data: dict) -> list:
    location    = data['loc']
    base_kw     = data['kw']
    max_leads   = data['count']
    max_rating  = data.get('rating')
    apify_key   = get_settings().get('apify_api_key', '')

    max_rating_float = None
    if max_rating:
        try: max_rating_float = float(str(max_rating).replace(',', '.'))
        except: pass

    m_scraper = GoogleMapsScraper()
    e_lib     = DeepEmailExtractor()
    kw_engine = AdvancedKeywordEngine()
    dedup     = DeduplicationStore()

    used_keywords  = set()
    final_leads    = []
    current_kw_bot = base_kw
    _zero_streak   = 0

    while len(final_leads) < max_leads:
        used_keywords.add(current_kw_bot.lower())
        raw_leads = m_scraper.fetch_batch(current_kw_bot, location, apify_key=apify_key)

        if not raw_leads:
            _zero_streak += 1
        else:
            _zero_streak = 0
            for lead in raw_leads:
                if len(final_leads) >= max_leads: break
                if max_rating_float is not None and lead['Rating'] != "N/A":
                    try:
                        if float(lead['Rating']) > max_rating_float: continue
                    except: pass
                existing = lead.get('Website', 'N/A')
                yelp_url = lead.get('_yelp_url', 'N/A')
                website  = m_scraper.resolve_website(lead['Name'], location, existing, yelp_url)
                lead['Website'] = website
                if not is_valid_business_website(website): continue
                if dedup.is_duplicate(lead['Name'], location, website, ""): continue
                email = e_lib.get_email(website)
                if email == "N/A": continue
                if dedup.is_duplicate(lead['Name'], location, website, email): continue
                dedup.register(lead['Name'], location, website, email)
                lead['Email'] = extracted_email = email
                lead['Maps_Link'] = lead.get('Maps_Link') or (
                    f"https://www.google.com/maps/search/{urllib.parse.quote_plus(lead['Name'] + ' ' + location)}/"
                )
                final_leads.append(lead)

        if len(final_leads) >= max_leads: break

        nxt = kw_engine.generate_single_keyword(base_kw, location, used_keywords)
        if not nxt: break
        current_kw_bot = nxt
        time.sleep(random.uniform(0.8, 1.5))

    return final_leads

async def background_bot_task(chat_id, message_id, data, bot):
    try:
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id,
            text="⏳ *Scraping (Google Maps → Yelp → Bing)*\n_One keyword at a time · worst-rated first_",
            parse_mode='Markdown')
        loop = asyncio.get_event_loop()
        final_leads = await loop.run_in_executor(None, run_bot_scrape_fast, data)
        if not final_leads:
            await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="😔 No results found.")
            return
        path = to_csv(final_leads)
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="✅ Done! Sending CSV…")
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
    msg = await q.edit_message_text("⏳ *Initialising…*", parse_mode='Markdown')
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
