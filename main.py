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
#   [STOP FEATURE] GLOBAL STOP FLAG
#   is_running is a dict keyed by job_id so multiple
#   jobs can be individually stopped without collision.
#   A global `global_stop` flag halts ALL jobs at once.
# ════════════════════════════════════════════════════
job_stop_flags: dict = {}   # job_id -> threading.Event
# Helper: check if a specific job should stop
def _should_stop(job_id: str) -> bool:
    flag = job_stop_flags.get(job_id)
    return flag is not None and flag.is_set()

# ════════════════════════════════════════════════════
#   ROTATING HEADERS  — multiple realistic profiles
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
#   DEDUPLICATION STORE  (UPDATED FOR PROBLEM 5)
# ════════════════════════════════════════════════════
class DeduplicationStore:
    def __init__(self):
        self._lock = threading.Lock()
        self._websites: set = set()
        self._emails:   set = set()
        self._name_locs: set = set() # [PROBLEM 5] Strict Name + Location checking
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

    # [PROBLEM 5] Added location to ensure strict deduplication across the board
    def is_duplicate(self, name: str, location: str, website: str, email: str) -> bool:
        nn = self._norm(name)
        nl = self._norm(location)
        nloc = f"{nn} {nl}"
        nw = self._norm_url(website)
        ne = self._norm(email)
        
        with self._lock:
            # Check if exists based on Email OR Website OR Name+Location
            if ne and ne in self._emails:   return True
            if nw and nw in self._websites: return True
            if nn and nl and nloc in self._name_locs: return True
        return False

    def register(self, name: str, location: str, website: str, email: str):
        nn = self._norm(name)
        nl = self._norm(location)
        nloc = f"{nn} {nl}"
        nw = self._norm_url(website)
        ne = self._norm(email)
        
        with self._lock:
            if nn and nl: self._name_locs.add(nloc)
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
#   ADVANCED KEYWORD ENGINE  (PRESERVED ALL + ADDED 1-by-1)
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

    # [PROBLEM 2] ADDED STRICT ONE-BY-ONE KEYWORD GENERATOR
    def generate_single_keyword(self, base_kw, location, used_kws) -> str:
        if GROQ_API_KEY:
            try:
                client = Groq(api_key=GROQ_API_KEY)
                prompt = (
                    f"You are a local SEO expert. Base keyword: '{base_kw}'. Location: '{location}'. "
                    f"Used keywords: {list(used_kws)[:50]}. "
                    f"Generate EXACTLY ONE new, highly relevant search term a user would type to find these local businesses. "
                    f"Return ONLY the exact search term string. No quotes, no intro, no numbering."
                )
                res = client.chat.completions.create(
                    messages=[{"role": "user", "content": prompt}],
                    model="llama3-8b-8192",
                    temperature=0.8,
                    max_tokens=30,
                )
                text = res.choices[0].message.content.strip().strip('"').strip("'")
                kw = text.split('\n')[0].split(',')[0].strip() # Clean output
                if kw and kw.lower() not in used_kws and len(kw) > 3:
                    logger.info(f"[KEYWORDS] AI generated single keyword: '{kw}'")
                    return kw
            except Exception as e:
                logger.warning(f"[KEYWORDS] AI single gen failed: {e}")

        # Fallback loop
        for p in self.COMMERCIAL_PREFIXES:
            kw = f"{p} {base_kw}"
            if kw.lower() not in used_kws: return kw
        for s in self.COMMERCIAL_SUFFIXES:
            kw = f"{base_kw} {s}"
            if kw.lower() not in used_kws: return kw
            
        return None


# ════════════════════════════════════════════════════
#   GOOGLE MAPS SCRAPER  — UPDATED FOR PROBLEM 1
# ════════════════════════════════════════════════════
class GoogleMapsScraper:
    MAX_RETRIES = 3
    RETRY_DELAY = 2

    # [PROBLEM 1] Website Validation Logic
    def is_valid_website(self, url: str) -> bool:
        if not url or url == "N/A": return False
        lower_url = url.lower()
        blacklist = [
            'google.com', 'google.co', 'yelp.com', 'tripadvisor.com', 'facebook.com',
            'instagram.com', 'twitter.com', 'linkedin.com', 'youtube.com', 'bbb.org',
            'yellowpages.com', 'mapquest.com', 'foursquare.com', 'yahoo.com', 'bing.com',
            'zoominfo.com', 'chamberofcommerce.com', 'houzz.com', 'angi.com', 'thumbtack.com',
            '/url?q='
        ]
        for b in blacklist:
            if b in lower_url: return False
        if not lower_url.startswith('http'): return False
        return True

    # [PROBLEM 1] Step 2: Fetch external website explicitly from Google Maps details block
    def fetch_website_from_details(self, maps_url: str) -> str:
        if not maps_url or maps_url == "N/A": return "N/A"
        try:
            resp = requests.get(maps_url, headers=get_headers(), timeout=10, verify=False)
            urls = re.findall(r'"(https?://[^"]+)"', resp.text)
            for u in urls:
                u_clean = u.replace('\\u0026', '&')
                if self.is_valid_website(u_clean):
                    logger.info(f"[WEBSITE-DETAILS] Found real site via maps page: {u_clean}")
                    return u_clean
        except Exception as e:
            logger.debug(f"[WEBSITE-DETAILS] Error fetching {maps_url}: {e}")
        return "N/A"

    def _scrape_google_maps(self, keyword: str, location: str) -> list:
        results = []
        query = urllib.parse.quote_plus(f"{keyword} {location}")
        url = f"https://www.google.com/maps/search/{query}/"

        for attempt in range(1, self.MAX_RETRIES + 1):
            try:
                logger.info(f"[SCRAPE-MAPS] Attempt {attempt}: {url}")
                session = requests.Session()
                session.headers.update(get_headers())

                resp = session.get(url, timeout=15, verify=False, allow_redirects=True)
                logger.info(f"[SCRAPE-MAPS] HTTP {resp.status_code} | content-length={len(resp.text)}")

                if resp.status_code != 200:
                    time.sleep(self.RETRY_DELAY * attempt)
                    continue

                html = resp.text
                businesses = self._parse_maps_html(html, keyword, location)

                if businesses:
                    logger.info(f"[SCRAPE-MAPS] Parsed {len(businesses)} businesses from Maps HTML")
                    return businesses

                businesses = self._parse_maps_html_elements(html, keyword, location)
                if businesses:
                    logger.info(f"[SCRAPE-MAPS] Parsed {len(businesses)} businesses from Maps HTML elements")
                    return businesses

                logger.warning(f"[SCRAPE-MAPS] Attempt {attempt}: zero results parsed, retrying...")
                time.sleep(self.RETRY_DELAY * attempt)

            except requests.exceptions.RequestException as e:
                logger.warning(f"[SCRAPE-MAPS] Request error attempt={attempt}: {e}")
                time.sleep(self.RETRY_DELAY * attempt)
            except Exception as e:
                logger.error(f"[SCRAPE-MAPS] Unexpected error: {e}")
                break

        return results

    def _parse_maps_html(self, html: str, keyword: str, location: str) -> list:
        results = []
        seen_names = set()

        try:
            soup = BeautifulSoup(html, 'html.parser')
            for script in soup.find_all('script', type='application/ld+json'):
                try:
                    data = json.loads(script.string or '')
                    items = data if isinstance(data, list) else [data]
                    for item in items:
                        if item.get('@type') in ('LocalBusiness', 'Restaurant', 'Store',
                                                  'MedicalBusiness', 'LegalService', 'HomeAndConstructionBusiness',
                                                  'HealthAndBeautyBusiness', 'FoodEstablishment'):
                            name = item.get('name', 'N/A')
                            if not name or name in seen_names:
                                continue
                            seen_names.add(name)
                            results.append({
                                "Name":        name,
                                "Phone":       item.get('telephone', 'N/A') or 'N/A',
                                "Website":     item.get('url', 'N/A') or 'N/A',
                                "Rating":      str(item.get('aggregateRating', {}).get('ratingValue', 'N/A')),
                                "ReviewCount": str(item.get('aggregateRating', {}).get('reviewCount', '0')),
                                "Address":     location,
                                "Category":    keyword,
                                "Maps_Link":   item.get('hasMap', 'N/A') or f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/",
                            })
                except:
                    pass
        except Exception as e:
            logger.debug(f"[PARSE] JSON-LD parse error: {e}")

        if results:
            return results

        try:
            name_pattern = re.findall(
                r'"([A-Z][^"]{2,60})"[^"]*?"([1-5]\.[0-9])"',
                html
            )
            for name, rating in name_pattern[:50]:
                name = name.strip()
                if (len(name) < 3 or name in seen_names or
                        any(c in name for c in ['\\', '/', '{', '}', '(', ')', '='])):
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
                    "Maps_Link":   f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/",
                })
        except Exception as e:
            logger.debug(f"[PARSE] Regex parse error: {e}")

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
                logger.info(f"[PARSE-ELEMENTS] Using selector '{sel}' → {len(found)} blocks")
                break

        for block in blocks[:30]:
            try:
                text = block.get_text(separator=' ', strip=True)

                name = "N/A"
                aria = block.get('aria-label', '')
                if aria and len(aria) > 2 and len(aria) < 100:
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
                for a in block.select('a[href]'):
                    href = a.get('href', '')
                    if '/url?q=' in href:
                        clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                        if clean.startswith('http') and 'google' not in clean.lower():
                            website = clean
                            break
                    elif href.startswith('http') and 'google' not in href.lower():
                        website = href
                        break

                results.append({
                    "Name":        name,
                    "Phone":       phone,
                    "Website":     website,
                    "Rating":      rating,
                    "ReviewCount": review_count,
                    "Address":     location,
                    "Category":    keyword,
                    "Maps_Link":   f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}/",
                })
            except Exception as e:
                logger.debug(f"[PARSE-ELEMENTS] Block error: {e}")

        return results

    def _scrape_google_local(self, keyword: str, location: str) -> list:
        query = urllib.parse.quote_plus(f"{keyword} {location}")
        all_results = []

        def fetch_one_offset(start: int) -> list:
            url = f"https://www.google.com/search?q={query}&tbm=lcl&start={start}&num=20&hl=en&gl=us"
            for attempt in range(1, self.MAX_RETRIES + 1):
                try:
                    resp = requests.get(url, headers=get_headers(), timeout=12, verify=False)
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

                    logger.info(f"[SCRAPE-LCL] offset={start} → {len(blocks)} blocks found")

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
                                if len(txt) > 3 and len(txt) < 80:
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
                        for a in block.select('a[href]'):
                            href = a.get('href', '')
                            if '/url?q=' in href:
                                clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                                if clean.startswith('http') and 'google' not in clean.lower():
                                    website = clean
                                    break
                            elif href.startswith('http') and 'google' not in href.lower():
                                website = href
                                break

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

                    logger.info(f"[SCRAPE-LCL] offset={start} → {len(batch)} businesses parsed")
                    return batch

                except requests.exceptions.RequestException as e:
                    logger.warning(f"[SCRAPE-LCL] Request error offset={start} attempt={attempt}: {e}")
                    time.sleep(self.RETRY_DELAY * attempt)
                except Exception as e:
                    logger.error(f"[SCRAPE-LCL] Unexpected error offset={start}: {e}")
                    break
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
            resp = requests.get(url, headers=get_headers(), timeout=12, verify=False)
            logger.info(f"[SCRAPE-DDG] HTTP {resp.status_code}")
            if resp.status_code != 200:
                return results

            soup = BeautifulSoup(resp.text, 'html.parser')
            result_items = soup.select('.result, .results_links, div.result__body')

            logger.info(f"[SCRAPE-DDG] {len(result_items)} result blocks found")

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
                        except:
                            pass

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
                    logger.debug(f"[SCRAPE-DDG] Item error: {e}")

        except Exception as e:
            logger.warning(f"[SCRAPE-DDG] Error: {e}")

        logger.info(f"[SCRAPE-DDG] Extracted {len(results)} businesses")
        return results

    def fetch_batch(self, keyword: str, location: str) -> list:
        logger.info(f"[SCRAPE] ═══ Starting scrape for keyword: '{keyword}' in '{location}' ═══")
        all_leads = []

        maps_results = self._scrape_google_maps(keyword, location)
        logger.info(f"[SCRAPE] Strategy A (Google Maps): {len(maps_results)} businesses")
        all_leads.extend(maps_results)

        local_results = self._scrape_google_local(keyword, location)
        logger.info(f"[SCRAPE] Strategy B (Google Local): {len(local_results)} businesses")
        all_leads.extend(local_results)

        if len(all_leads) < 3:
            logger.info("[SCRAPE] Insufficient results from Google — trying DuckDuckGo fallback")
            ddg_results = self._scrape_duckduckgo(keyword, location)
            logger.info(f"[SCRAPE] Strategy C (DuckDuckGo): {len(ddg_results)} businesses")
            all_leads.extend(ddg_results)

        seen_names = set()
        unique_leads = []
        for lead in all_leads:
            key = lead["Name"].strip().lower()
            if key not in seen_names and key != "n/a" and len(key) > 2:
                seen_names.add(key)
                unique_leads.append(lead)

        def sort_key(lead):
            try:
                return float(lead["Rating"])
            except:
                return 6.0

        unique_leads.sort(key=sort_key)

        logger.info(
            f"[SCRAPE] ✅ TOTAL for '{keyword}': "
            f"{len(all_leads)} raw → {len(unique_leads)} unique (bad-rating-first order)"
        )
        return unique_leads

    # [PROBLEM 1] Step 3: Better find_website_via_search with validation
    def find_website_via_search(self, business_name: str, location: str) -> str:
        query = urllib.parse.quote_plus(f"{business_name} {location} official website")
        
        # 1. Google Search
        try:
            url = f"https://www.google.com/search?q={query}&num=5&hl=en"
            resp = requests.get(url, headers=get_headers(), timeout=8, verify=False)
            soup = BeautifulSoup(resp.text, 'html.parser')
            for a in soup.select('a[href]'):
                href = a.get('href', '')
                if '/url?q=' in href:
                    clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                    if self.is_valid_website(clean):
                        logger.info(f"[WEBSITE-SEARCH] Found via Google for '{business_name}': {clean}")
                        return clean
        except Exception as e:
            logger.debug(f"[WEBSITE-SEARCH] Google search failed: {e}")

        # 2. DuckDuckGo Fallback
        try:
            url_ddg = f"https://html.duckduckgo.com/html/?q={query}"
            resp_ddg = requests.get(url_ddg, headers=get_headers(), timeout=8, verify=False)
            soup_ddg = BeautifulSoup(resp_ddg.text, 'html.parser')
            for a in soup_ddg.select('a.result__url, .result__url'):
                href = a.get('href', '') or a.get_text(strip=True)
                if href and not href.startswith('http'): href = 'https://' + href
                if self.is_valid_website(href):
                    logger.info(f"[WEBSITE-SEARCH] Found via DDG for '{business_name}': {href}")
                    return href
        except Exception as e:
            logger.debug(f"[WEBSITE-SEARCH] DDG failed: {e}")

        return "N/A"


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
#   MASTER JOB RUNNER  — WITH STOP FLAG CHECKS
#
#   [STOP FEATURE] Every loop now checks _should_stop(job_id).
#   If the stop flag is set, loops break gracefully.
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
                logger.info(f"[JOB] Rating filter active: rating <= {max_rating_float}")
            except:
                logger.warning(f"[JOB] Invalid max_rating value '{max_rating}' — filter disabled")

        maps_scraper   = GoogleMapsScraper()
        email_lib      = DeepEmailExtractor()
        kw_engine      = AdvancedKeywordEngine()
        db             = GoogleSheetsDB(db_webhook_url)
        dedup          = DeduplicationStore()

        jobs[job_id] = {
            'status':       'scraping',
            'count':        0,
            'leads':        [],
            'emails_sent':  0,
            'total_to_send': 0,
            'status_text':  f'Starting scrape for: {base_keyword} in {location}...',
            # [STOP FEATURE] Track is_running per-job for frontend display
            'is_running':   True,
            'stats': {
                'scraped_total':      0,
                'after_rating_filter': 0,
                'duplicates_skipped': 0,
                'emails_found':       0,
                'errors':             0,
                'keywords_used':      0,
                'keywords_generated': 0,
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
        pending_keywords      = [base_keyword]

        def _process_lead_batch(raw_leads: list, current_kw: str) -> bool:
            """
            Process one batch of scraped businesses.
            Returns True if target was reached OR stop was requested.
            [STOP FEATURE] Checks _should_stop(job_id) at each lead iteration.
            """
            jobs[job_id]['stats']['scraped_total'] += len(raw_leads)
            logger.info(f"[JOB] Processing {len(raw_leads)} businesses from keyword '{current_kw}'")

            for lead in raw_leads:
                # [STOP FEATURE] Check stop flag before processing each lead
                if _should_stop(job_id):
                    logger.info(f"[JOB] 🛑 STOP requested — breaking lead processing loop")
                    return True

                if len(jobs[job_id]['leads']) >= max_leads:
                    logger.info(f"[JOB] 🎯 TARGET REACHED: {max_leads} leads — stopping")
                    return True

                logger.info(f"[JOB] Processing business: '{lead['Name']}' | rating={lead['Rating']} | website={lead['Website']}")

                # [PROBLEM 6] Store Maps URL and all data
                maps_url = lead.get('Maps_Link', 'N/A')

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

                if max_rating_float is not None and lead['Rating'] != "N/A":
                    try:
                        r_val = float(lead['Rating'])
                        if r_val > max_rating_float:
                            logger.info(
                                f"[FILTER] ❌ SKIPPED '{lead['Name']}' "
                                f"rating={r_val} > max={max_rating_float}"
                            )
                            continue
                        else:
                            logger.info(
                                f"[FILTER] ✅ ACCEPTED '{lead['Name']}' "
                                f"rating={r_val} <= max={max_rating_float}"
                            )
                    except ValueError:
                        logger.debug(
                            f"[FILTER] Cannot parse rating '{lead['Rating']}' "
                            f"for '{lead['Name']}' — allowing through"
                        )

                jobs[job_id]['stats']['after_rating_filter'] += 1

                # [PROBLEM 1] FULL WEBSITE EXTRACTION PIPELINE
                website = lead['Website']
                if not maps_scraper.is_valid_website(website):
                    website = "N/A"

                if website == "N/A" and maps_url != "N/A":
                    jobs[job_id]['status_text'] = f"Checking details page for: {lead['Name']}..."
                    logger.info(f"[WEBSITE] Not found in listing — checking Maps detail page...")
                    website = maps_scraper.fetch_website_from_details(maps_url)

                if website == "N/A":
                    jobs[job_id]['status_text'] = f"Finding website via search: {lead['Name']}..."
                    logger.info(f"[WEBSITE] Not found in details — searching Google/DDG...")
                    website = maps_scraper.find_website_via_search(lead['Name'], location)
                    
                lead['Website'] = website
                if website != "N/A":
                    logger.info(f"[WEBSITE] ✅ Valid website found: {website}")
                else:
                    logger.info(f"[WEBSITE] ❌ Not found for '{lead['Name']}' — skipping")
                    continue

                # [PROBLEM 5] STRICT DEDUPLICATION BEFORE EMAIL
                if dedup.is_duplicate(lead['Name'], location, website, ""):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] ⚠ Pre-email duplicate: '{lead['Name']}'")
                    continue

                # [STOP FEATURE] Check stop flag before slow email extraction
                if _should_stop(job_id):
                    logger.info(f"[JOB] 🛑 STOP requested — aborting before email extraction")
                    return True

                jobs[job_id]['status_text'] = f"Extracting email from: {lead['Name']}..."
                extracted_email = email_lib.get_email(website)

                if extracted_email == "N/A":
                    logger.info(f"[EMAIL] ❌ No email found for '{lead['Name']}' at {website}")
                    continue

                jobs[job_id]['stats']['emails_found'] += 1
                logger.info(f"[EMAIL] ✅ Found: {extracted_email} for '{lead['Name']}'")

                # [PROBLEM 5] STRICT DEDUPLICATION AFTER EMAIL
                if dedup.is_duplicate(lead['Name'], location, website, extracted_email):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] ⚠ Post-email duplicate: '{lead['Name']}' / {extracted_email}")
                    continue

                dedup.register(lead['Name'], location, website, extracted_email)

                # [PROBLEM 6] FULL DATA SAVE TO DB
                db.send_action("add_email_lead", {
                    "business_name": lead['Name'], "website": website,
                    "email": extracted_email, "source_page": website, "status": "qualified",
                })
                db.send_action("add_qualified", {
                    "business_name": lead['Name'], "address": lead['Address'], "phone": lead['Phone'],
                    "rating": lead['Rating'], "review_count": lead.get('ReviewCount', 'N/A'),
                    "website": website, "email": extracted_email, "maps_url": maps_url,
                    "keyword": current_kw, "personalization_line": "Pending AI...",
                    "email_sent": "no",
                })

                lead['Email'] = extracted_email
                jobs[job_id]['leads'].append(lead)
                jobs[job_id]['count'] = len(jobs[job_id]['leads'])
                jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped

                logger.info(
                    f"[LEAD] ✅ #{jobs[job_id]['count']}/{max_leads} "
                    f"'{lead['Name']}' | rating={lead['Rating']} | {extracted_email}"
                )
                jobs[job_id]['status_text'] = (
                    f"✅ {jobs[job_id]['count']}/{max_leads} leads found! "
                    f"Latest: {lead['Name']} ({extracted_email})"
                )

                if len(jobs[job_id]['leads']) >= max_leads:
                    logger.info(f"[JOB] 🎯 TARGET REACHED inside batch — stopping")
                    return True

            return False

        # ════════════════════════════════════════════════════════════
        # MAIN LOOP — with stop flag check at each iteration
        # ════════════════════════════════════════════════════════════
        while len(jobs[job_id]['leads']) < max_leads:

            # [STOP FEATURE] Check stop flag at the top of every main loop iteration
            if _should_stop(job_id):
                logger.info(f"[JOB] 🛑 STOP requested — exiting main keyword loop")
                break

            if not pending_keywords:
                # [STOP FEATURE] Check before keyword generation (can be slow with AI)
                if _should_stop(job_id):
                    break

                # [PROBLEM 2] STRICT ONE-BY-ONE KEYWORD GENERATION
                jobs[job_id]['status_text'] = f"Generating 1 new exact keyword for '{base_keyword}'..."
                logger.info(f"[JOB] Target not reached. Generating ONE new keyword...")
                new_kw = kw_engine.generate_single_keyword(base_keyword, location, used_keywords)
                
                if new_kw:
                    pending_keywords.append(new_kw)
                    jobs[job_id]['stats']['keywords_generated'] += 1
                    logger.info(f"[JOB] Added new keyword: '{new_kw}'")
                    db.send_action("add_keyword", {
                        "keyword": new_kw, "source_seed": base_keyword, "status": "pending"
                    })
                else:
                    logger.info("[JOB] Keyword pool exhausted. Cannot generate more.")
                    break

            current_kw = pending_keywords.pop(0)
            used_keywords.add(current_kw.lower())
            jobs[job_id]['stats']['keywords_used'] += 1

            jobs[job_id]['status_text'] = (
                f"[STEP 1] Scraping: '{current_kw}' in '{location}'..."
            )
            logger.info(
                f"[JOB] ── Scraping keyword {jobs[job_id]['stats']['keywords_used']}: "
                f"'{current_kw}' | leads so far: {len(jobs[job_id]['leads'])}/{max_leads}"
            )

            # [STOP FEATURE] Check before starting a new scrape batch
            if _should_stop(job_id):
                logger.info(f"[JOB] 🛑 STOP requested — not starting scrape for '{current_kw}'")
                break

            raw_leads = maps_scraper.fetch_batch(current_kw, location)

            if not raw_leads:
                logger.info(f"[JOB] No businesses found for '{current_kw}' — moving to next keyword")
                time.sleep(random.uniform(1.0, 2.5))
                continue

            logger.info(f"[JOB] Businesses found: {len(raw_leads)} for '{current_kw}'")

            target_reached = _process_lead_batch(raw_leads, current_kw)

            if target_reached:
                logger.info(f"[JOB] STOP CONDITION met: {max_leads} qualified leads reached or stop requested")
                break

            logger.info(
                f"[JOB] Qualified leads count: {len(jobs[job_id]['leads'])}/{max_leads} "
                f"— continuing to next keyword"
            )
            time.sleep(random.uniform(1.0, 2.0))

        # ── Final stats ──
        s = jobs[job_id]['stats']
        final_count = len(jobs[job_id]['leads'])

        # [STOP FEATURE] If stopped early, set appropriate status
        stopped_early = _should_stop(job_id)

        logger.info(
            f"[JOB] ═══ SCRAPING {'STOPPED' if stopped_early else 'COMPLETE'} ═══\n"
            f"  scraped_total     : {s['scraped_total']}\n"
            f"  after_filter      : {s['after_rating_filter']}\n"
            f"  emails_found      : {s['emails_found']}\n"
            f"  duplicates_skipped: {s['duplicates_skipped']}\n"
            f"  keywords_used     : {s['keywords_used']}\n"
            f"  keywords_generated: {s['keywords_generated']}\n"
            f"  final_leads       : {final_count}"
        )
        db.send_action("update_config", {
            "keyword_seed": base_keyword, "location": location,
            "target_leads": max_leads, "min_rating": "",
            "max_rating": max_rating or "", "email_required": "true",
            "status": "stopped" if stopped_early else "done",
        })
        db.log("Scraping Done", f"Qualified: {final_count} | Keywords used: {s['keywords_used']}")

        final_leads = jobs[job_id]['leads']

        # ════════════════════════════════════════════════════
        # PHASE 2: SEND EMAILS
        # [STOP FEATURE] Skip email sending if stop was requested
        # ════════════════════════════════════════════════════
        if webhook_url and templates and final_leads and not stopped_early:
            jobs[job_id]['status'] = 'sending_emails'
            jobs[job_id]['total_to_send'] = len(final_leads)
            emails_sent = 0

            for lead in final_leads:
                # [STOP FEATURE] Check stop flag before each email send
                if _should_stop(job_id):
                    logger.info(f"[JOB] 🛑 STOP requested — aborting email send loop")
                    break

                jobs[job_id]['status_text'] = (
                    f"Sending email {emails_sent + 1}/{len(final_leads)} → {lead['Email']}"
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
                    logger.info(f"[EMAIL-SEND] ✅ Sent to {lead['Email']}")
                except Exception as e:
                    jobs[job_id]['stats']['errors'] += 1
                    logger.error(f"[EMAIL-SEND] ❌ Failed → {lead['Email']}: {e}")

                if emails_sent < len(final_leads) and not _should_stop(job_id):
                    delay = random.randint(60, 120)
                    for i in range(delay, 0, -1):
                        # [STOP FEATURE] Check stop flag during cooldown countdown
                        if _should_stop(job_id):
                            logger.info(f"[JOB] 🛑 STOP during cooldown — aborting")
                            break
                        jobs[job_id]['status_text'] = (
                            f"Anti-spam cooldown: {i}s before next email..."
                        )
                        time.sleep(1)

        # [STOP FEATURE] Set final status and is_running=False
        if _should_stop(job_id):
            jobs[job_id]['status'] = 'stopped'
            jobs[job_id]['status_text'] = (
                f"🛑 Stopped by user. {final_count} leads collected."
            )
        else:
            jobs[job_id]['status'] = 'done'
            jobs[job_id]['status_text'] = (
                f"✅ Completed! {final_count} qualified leads found."
            )

        # [STOP FEATURE] Mark job as no longer running
        jobs[job_id]['is_running'] = False

        db.log("Job Complete", f"All tasks finished. Leads: {final_count}")
        logger.info(f"[JOB] ✅ JOB {job_id} COMPLETE — {final_count} leads")

    except Exception as e:
        logger.error(f"[JOB] ❌ Fatal error in job {job_id}: {e}", exc_info=True)
        if job_id in jobs:
            jobs[job_id]['status'] = 'error'
            jobs[job_id]['error']  = str(e)
            jobs[job_id]['is_running'] = False  # [STOP FEATURE] ensure flag cleared on error
        else:
            jobs[job_id] = {'status': 'error', 'error': str(e), 'is_running': False}


# ════════════════════════════════════════════════════
#   FLASK APP + UI
# ════════════════════════════════════════════════════
flask_app = Flask(__name__)
jobs: dict = {}

# [REFRESH FIX] Global latest job ID — used to restore state on page reload
latest_job_id: str = None

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
.inp:disabled{opacity:0.6;cursor:not-allowed;background:var(--surface2)}
.inp::placeholder{color:var(--ink3)}
.btn{display:inline-flex;align-items:center;justify-content:center;gap:8px;border:none;border-radius:8px;font-weight:600;font-size:14px;cursor:pointer;transition:all .15s;font-family:'Outfit',sans-serif;padding:11px 20px;white-space:nowrap}
.btn:disabled{opacity:.4;cursor:not-allowed;pointer-events:none}
.btn-primary{background:var(--accent);color:#fff}
.btn-primary:hover{background:var(--accent-h);transform:translateY(-1px);box-shadow:0 4px 14px rgba(212,82,42,.3)}
.btn-success{background:var(--green);color:#fff}
.btn-success:hover{filter:brightness(1.1);transform:translateY(-1px)}
.btn-danger{background:var(--red);color:#fff}
.btn-danger:hover{filter:brightness(1.1);transform:translateY(-1px);box-shadow:0 4px 14px rgba(192,57,43,.3)}
.btn-neutral{background:var(--surface2);color:var(--ink);border:1.5px solid var(--border)}
.btn-neutral:hover{border-color:var(--ink2)}
.btn-ghost{background:none;color:var(--ink3);border:1.5px solid var(--border);font-size:12px;padding:7px 13px}
.btn-ghost:hover{color:var(--red);border-color:var(--red)}
.btn-full{width:100%}
/* [STOP FEATURE] Button row for start+stop side by side */
.btn-row{display:flex;gap:10px;margin-top:12px}
.btn-row .btn{flex:1}
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
/* [STOP FEATURE] Running indicator pill */
.run-pill{display:inline-flex;align-items:center;gap:6px;font-size:12px;font-weight:700;padding:4px 12px;border-radius:99px}
.run-pill.running{background:rgba(30,138,94,.12);color:var(--green)}
.run-pill.stopped{background:rgba(160,158,151,.12);color:var(--ink3)}
.run-pill.error{background:rgba(192,57,43,.1);color:var(--red)}
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
.divider{height:1px;background:var(--border);margin:16px 0}
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
@media(max-width:480px){.card{padding:14px}.btn{padding:10px 16px;font-size:13px}.stat-val{font-size:22px}.nav-title{font-size:14px}.btn-row{flex-direction:column}}
</style>
</head>
<body>
<nav class="nav">
  <div class="nav-inner">
    <div class="nav-brand">
      <div class="nav-logo"><i class="fa-solid fa-bolt"></i></div>
      <div>
        <div class="nav-title">Lead<span>Gen</span> Pro</div>
        <div class="nav-sub">Scrape · Filter · Email</div>
      </div>
    </div>
    <!-- [STOP FEATURE] Global running status pill in navbar -->
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
        <span><b>Flow:</b> Scrapes your keyword first → filters by rating → extracts websites → extracts emails → generates ONE keyword at a time if target not met.</span>
      </div>
      <!-- [STOP FEATURE] Start and Stop buttons side by side -->
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
        <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → New Project → paste script → Deploy as Web App (Anyone) → copy URL.</span>
      </div>
      <div style="position:relative;margin-bottom:14px">
        <button onclick="unlockSettings()" class="btn btn-ghost btn-unlock" style="position:absolute;top:8px;right:60px;font-size:11px;padding:5px 10px;z-index:1"><i class="fa-solid fa-lock"></i> Unlock</button>
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
      getOrCreateSheet("Qualified_Leads",["business_name","address","phone","rating","review_count","website","email","maps_url","keyword","personalization_line","email_sent"]);
      getOrCreateSheet("Logs",["timestamp","action","details"]);
    } else if (action === "log") { var s=ss.getSheetByName("Logs"); if(s) s.appendRow([data.timestamp,data.action,data.details]); }
    else if (action === "add_keyword") { var s=ss.getSheetByName("Generated_Keywords"); if(s) s.appendRow([data.keyword,data.source_seed,data.status]); }
    else if (action === "add_scraped") { var s=ss.getSheetByName("Scraped_Businesses"); if(s) s.appendRow([data.business_name,data.address,data.phone,data.rating,data.review_count,data.website,data.maps_url,data.keyword,data.status]); }
    else if (action === "add_email_lead") { var s=ss.getSheetByName("Email_Leads"); if(s) s.appendRow([data.business_name,data.website,data.email,data.source_page,data.status]); }
    else if (action === "add_qualified") { var s=ss.getSheetByName("Qualified_Leads"); if(s) s.appendRow([data.business_name,data.address,data.phone,data.rating,data.review_count,data.website,data.email,data.maps_url,data.keyword,data.personalization_line,data.email_sent]); }
    else if (action === "update_config") { var s=ss.getSheetByName("Config"); if(s){s.clearContents();s.appendRow(["keyword_seed","location","target_leads","min_rating","max_rating","email_required","status"]);s.appendRow([data.keyword_seed,data.location,data.target_leads,data.min_rating,data.max_rating,data.email_required,data.status]);} }
    else if (action === "update_email_sent") { var s=ss.getSheetByName("Qualified_Leads"); if(s){var v=s.getDataRange().getValues();for(var i=1;i<v.length;i++){if(v[i][6]===data.email){s.getRange(i+1,10).setValue(data.personalization_line);s.getRange(i+1,11).setValue("yes");break;}}} }
    return ContentService.createTextOutput(JSON.stringify({status:"success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(e) { return ContentService.createTextOutput(JSON.stringify({status:"error",message:e.toString()})).setMimeType(ContentService.MimeType.JSON); }
  finally { lock.releaseLock(); }
}
function doGet(e) { return ContentService.createTextOutput(JSON.stringify({status:"active"})).setMimeType(ContentService.MimeType.JSON); }</textarea>
      </div>
      <div class="form-group" style="margin-bottom:12px">
        <label>🔗 Database Web App URL</label>
        <input id="db-webhook-url" class="inp" placeholder="Locked - Requires PIN" disabled>
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
        <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → paste code → Deploy as Web App (Anyone) → copy URL.</span>
      </div>
      <div style="position:relative;margin-bottom:14px">
        <button onclick="unlockSettings()" class="btn btn-ghost btn-unlock" style="position:absolute;top:8px;right:8px;font-size:11px;padding:5px 10px;z-index:1"><i class="fa-solid fa-lock"></i> Unlock</button>
        <textarea readonly class="inp" style="font-family:monospace;font-size:11px;height:110px;resize:none;color:var(--blue)">
function doPost(e) {
  try {
    var data = JSON.parse(e.postData.contents);
    MailApp.sendEmail({ to: data.to, subject: data.subject, htmlBody: data.body });
    return ContentService.createTextOutput(JSON.stringify({"status":"success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(err) {
    return ContentService.createTextOutput(JSON.stringify({"status":"error","message":err.toString()})).setMimeType(ContentService.MimeType.JSON);
  }
}</textarea>
      </div>
      <div class="form-group" style="margin-bottom:12px">
        <label>🔗 Email Web App URL</label>
        <input id="webhook-url" class="inp" placeholder="Locked - Requires PIN" disabled>
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
// [REFRESH FIX] State is persisted in sessionStorage so
// that on reload the UI can restore to the last known state.
// We use sessionStorage (not localStorage) so state resets
// when the browser tab is fully closed, which is the correct UX.
// ════════════════════════════════════════════════════
let jid = null, templates = [], historyData = [], tableShown = false;
let pollTimer = null;

// [PROBLEM 3] PIN Lock System for Settings
function unlockSettings() {
    let pin = prompt("Enter PIN to unlock settings:");
    if (pin === "0123") {
        document.getElementById('webhook-url').disabled = false;
        document.getElementById('db-webhook-url').disabled = false;
        document.querySelectorAll('.btn-unlock').forEach(b => {
            b.innerHTML = '<i class="fa-solid fa-lock-open"></i> Unlocked';
            b.style.color = 'var(--green)';
        });
        alert("Settings unlocked successfully.");
    } else {
        alert("Incorrect PIN.");
    }
}

// [REFRESH FIX] On load: restore persisted state BEFORE anything else
window.onload = async () => {
  document.getElementById('webhook-url').value     = localStorage.getItem('webhook_url')     || '';
  document.getElementById('db-webhook-url').value  = localStorage.getItem('db_webhook_url')  || '';
  templates   = JSON.parse(localStorage.getItem('templates')  || '[]');
  historyData = JSON.parse(localStorage.getItem('history')    || '[]');
  renderTemplates(); renderHistory();

  // [REFRESH FIX] Ask backend if there's an active/recent job
  try {
    const r = await fetch('/api/global_status');
    const d = await r.json();
    if (d.job_id && d.status && d.status !== 'not_found') {
      jid = d.job_id;
      // Restore leads data if available
      if (d.leads && d.leads.length) {
        updStats(d.leads);
        showPV(d.leads);
        tableShown = true;
      }
      // Restore progress UI
      const target = d.count || 0;
      if (d.status === 'scraping' || d.status === 'sending_emails') {
        // Job still running — resume polling
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
  } catch (e) {
    // No active job or server not ready — that's fine
  }
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

function saveWebhook()   { localStorage.setItem('webhook_url',    document.getElementById('webhook-url').value.trim());    alert('Email webhook saved!'); }
function saveDBWebhook() { localStorage.setItem('db_webhook_url', document.getElementById('db-webhook-url').value.trim()); alert('Database webhook saved!'); }
function copyDBScript()  { const el=document.getElementById('db-script-code'); el.select(); document.execCommand('copy'); alert('Script copied!'); }

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

// [STOP FEATURE] Update button/pill UI based on running state
function setRunningUI(running) {
  const pill     = document.getElementById('run-status-pill');
  const pillTxt  = document.getElementById('run-status-text');
  const btnRun   = document.getElementById('btn-run');
  const btnStop  = document.getElementById('btn-stop');

  if (running) {
    pill.className    = 'run-pill running';
    pillTxt.textContent = 'Running';
    btnRun.disabled   = true;
    btnStop.disabled  = false;
  } else {
    pill.className    = 'run-pill stopped';
    pillTxt.textContent = 'Idle';
    btnRun.disabled   = false;
    btnStop.disabled  = true;
  }
}

function setSt(msg, state='load', pct=null) {
  document.getElementById('sbox').classList.remove('hidden');
  document.getElementById('sdet').textContent = msg;
  const ic=document.getElementById('si'), txt=document.getElementById('stxt');
  const iconMap = {
    load:  ['fa-circle-notch spin','var(--accent)',   'Scraping Engine Running…'],
    email: ['fa-paper-plane blink', 'var(--green)',   'Sending Emails…'],
    done:  ['fa-circle-check',      'var(--green)',   'Completed!'],
    stopped: ['fa-stop-circle',     'var(--ink3)',    'Stopped by User'],
    err:   ['fa-circle-xmark',      'var(--red)',     'Error Occurred'],
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
    <span class="debug-chip chip-blue" title="Total businesses scraped from all sources">Scraped: ${stats.scraped_total||0}</span>
    <span class="debug-chip chip-amber" title="Businesses passing rating filter">After filter: ${stats.after_rating_filter||0}</span>
    <span class="debug-chip chip-green" title="Emails successfully extracted">Emails: ${stats.emails_found||0}</span>
    <span class="debug-chip chip-red" title="Duplicates detected and skipped">Dupes: ${stats.duplicates_skipped||0}</span>
    <span class="debug-chip chip-purple" title="Keywords scraped so far">Keywords: ${stats.keywords_used||0}</span>
    <span class="debug-chip chip-red" title="Errors encountered">Errors: ${stats.errors||0}</span>
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
  const keys = Object.keys(leads[0]).filter(k=>k!=='Maps_Link');
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

  setSt(`Starting scrape for: ${kw} in ${loc}...`, 'load', 2);
  document.getElementById('dlbtn').classList.add('hidden');
  document.getElementById('pvbox').classList.add('hidden');
  document.getElementById('debug-stats').innerHTML = '';
  tableShown = false;

  // [STOP FEATURE] Update UI to running state
  setRunningUI(true);

  const payload = {
    location: loc, keyword: kw, max_leads: count,
    max_rating:      document.getElementById('m-rating').value.trim() || null,
    webhook_url:     webhook,
    db_webhook_url:  db_webhook,
    templates:       templates,
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

// [STOP FEATURE] Stop button handler — calls /api/stop/<job_id>
async function stopJob() {
  if (!jid) return;
  try {
    document.getElementById('btn-stop').disabled = true;
    document.getElementById('btn-stop').innerHTML = '<i class="fa-solid fa-spinner spin"></i> Stopping…';
    await fetch('/api/stop/' + jid, { method: 'POST' });
    setSt('Stop signal sent — waiting for current operation to finish…', 'load', null);
  } catch(e) {
    console.error('Stop failed:', e);
  }
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
        // [STOP FEATURE] Restore idle UI when done
        setRunningUI(false);
        if(d2.leads){ updStats(d2.leads); showPV(d2.leads); }
        setSt(d2.status_text||'Done!','done',100);
        document.getElementById('dlbtn').classList.remove('hidden');

      } else if(d2.status==='stopped') {
        // [STOP FEATURE] Handle stopped state gracefully
        setRunningUI(false);
        if(d2.leads){ updStats(d2.leads); showPV(d2.leads); }
        setSt(d2.status_text||'Stopped by user.','stopped',100);
        if(d2.leads && d2.leads.length) document.getElementById('dlbtn').classList.remove('hidden');
        // Reset stop button label
        document.getElementById('btn-stop').innerHTML = '<i class="fa-solid fa-stop"></i> Stop';

      } else if(d2.status==='error') {
        setRunningUI(false);
        setSt(d2.error||'Unknown error','err');

      } else {
        pollTimer = setTimeout(poll, 2500);
      }
    } catch(e) {
      pollTimer = setTimeout(poll, 2500);
    }
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
        f"[API] New job {job_id}: "
        f"keyword='{data.get('keyword')}' "
        f"location='{data.get('location')}' "
        f"target={data.get('max_leads')} "
        f"max_rating={data.get('max_rating')}"
    )

    # [STOP FEATURE] Create a fresh stop event for this job (not set = run normally)
    job_stop_flags[job_id] = threading.Event()

    # [REFRESH FIX] Track the latest job so /api/global_status can return it
    latest_job_id = job_id

    t = threading.Thread(target=run_job_thread, args=(job_id, data))
    t.daemon = True
    t.start()
    return jsonify({'job_id': job_id})


# [STOP FEATURE] New endpoint: POST /api/stop/<job_id>
# Sets the stop flag for the job — all loops will check this and break gracefully.
@flask_app.route('/api/stop/<job_id>', methods=['POST'])
def stop_job(job_id):
    flag = job_stop_flags.get(job_id)
    if flag:
        flag.set()
        logger.info(f"[API] 🛑 Stop requested for job {job_id}")
        return jsonify({'status': 'stop_requested', 'job_id': job_id})
    return jsonify({'status': 'not_found', 'job_id': job_id}), 404


@flask_app.route('/api/status/<job_id>')
def status(job_id):
    job = jobs.get(job_id, {'status': 'not_found'})
    out = dict(job)
    if out.get('status') in ['sending_emails', 'done', 'scraping', 'stopped']:
        out['leads'] = job.get('leads', [])
    return jsonify(out)


# [REFRESH FIX] New endpoint: GET /api/global_status
# Returns the latest job's full status so the frontend can restore state on reload.
@flask_app.route('/api/global_status')
def global_status():
    global latest_job_id
    if not latest_job_id or latest_job_id not in jobs:
        return jsonify({'status': 'not_found', 'job_id': None})

    job = jobs[latest_job_id]
    out = dict(job)
    out['job_id'] = latest_job_id
    # Always include leads so frontend can restore table
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
#   TELEGRAM BOT  (PRESERVED WITH 1-BY-1 UPDATE)
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
        "✅ Scrapes main keyword FIRST\n"
        "✅ Keywords generated ONLY after initial scrape\n"
        "✅ Worst-rated businesses first\n"
        "✅ Deduplication active\n"
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
        except:
            pass

    m_scraper  = GoogleMapsScraper()
    e_lib      = DeepEmailExtractor()
    kw_engine  = AdvancedKeywordEngine()
    dedup      = DeduplicationStore()

    used_keywords    = set()
    pending_keywords = [base_keyword]
    final_leads = []

    # [PROBLEM 2] STRICT 1-BY-1 KEYWORD LOOP FOR TELEGRAM
    while len(final_leads) < max_leads:
        if not pending_keywords:
            new_kw = kw_engine.generate_single_keyword(base_keyword, location, used_keywords)
            if new_kw:
                pending_keywords.append(new_kw)
            else:
                break

        current_kw = pending_keywords.pop(0)
        used_keywords.add(current_kw.lower())
        raw_leads = m_scraper.fetch_batch(current_kw, location)

        for lead in raw_leads:
            if len(final_leads) >= max_leads: break

            if max_rating_float is not None and lead['Rating'] != "N/A":
                try:
                    if float(lead['Rating']) > max_rating_float: continue
                except: pass

            # [PROBLEM 1] WEBSITE EXTRACT PIPELINE FOR BOT
            website = lead['Website']
            if not m_scraper.is_valid_website(website): website = "N/A"

            if website == "N/A" and lead.get('Maps_Link') != "N/A":
                website = m_scraper.fetch_website_from_details(lead['Maps_Link'])

            if website == "N/A":
                website = m_scraper.find_website_via_search(lead['Name'], location)
                
            lead['Website'] = website
            if website == "N/A": continue

            # [PROBLEM 5] DEDUPLICATION
            if dedup.is_duplicate(lead['Name'], location, website, ""): continue
            
            extracted_email = e_lib.get_email(website)
            if extracted_email == "N/A": continue
            
            if dedup.is_duplicate(lead['Name'], location, website, extracted_email): continue
            dedup.register(lead['Name'], location, website, extracted_email)

            lead['Email'] = extracted_email
            final_leads.append(lead)

    return final_leads

async def background_bot_task(chat_id, message_id, data, bot):
    try:
        await bot.edit_message_text(
            chat_id=chat_id, message_id=message_id,
            text="⏳ *Scraping now...*\n_Worst-rated businesses first. Keywords generated after initial scrape._",
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
    if TELEGRAM_TOKEN:
        threading.Thread(target=run_telegram_bot, daemon=True).start()
        logger.info("[BOOT] Telegram bot started")
    port = int(os.environ.get("PORT", 10000))
    logger.info(f"[BOOT] Flask starting on port {port}")
    flask_app.run(host='0.0.0.0', port=port)

