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
#   ROTATING HEADERS
# ════════════════════════════════════════════════════
HEADERS_LIST = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/122.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/121.0.0.0 Safari/537.36",
    "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/120.0.0.0 Safari/537.36",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:123.0) Gecko/20100101 Firefox/123.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_3) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.3 Safari/605.1.15",
]

def get_headers():
    return {
        "User-Agent": random.choice(HEADERS_LIST),
        "Accept-Language": "en-US,en;q=0.9",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Referer": "https://www.google.com/",
        "DNT": "1",
        "Connection": "keep-alive",
        "Upgrade-Insecure-Requests": "1",
    }

# ════════════════════════════════════════════════════
#   GOOGLE SHEETS DB WRAPPER (UNCHANGED)
# ════════════════════════════════════════════════════
class GoogleSheetsDB:
    def __init__(self, webhook_url):
        self.url = webhook_url

    def _post_async(self, payload):
        try:
            requests.post(self.url, json=payload, timeout=15)
        except Exception as e:
            logger.debug(f"DB post failed silently: {e}")

    def send_action(self, action, data):
        if not self.url: return
        payload = {"action": action, "data": data}
        threading.Thread(target=self._post_async, args=(payload,), daemon=True).start()

    def log(self, action, details):
        self.send_action("log", {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "action": action,
            "details": details
        })

# ════════════════════════════════════════════════════
#   DEDUPLICATION STORE
# ════════════════════════════════════════════════════
class DeduplicationStore:
    """
    Thread-safe store tracking seen business names, websites, and emails.
    A lead is a duplicate if ANY of the three keys match an existing record.
    """
    def __init__(self):
        self._lock = threading.Lock()
        self._names:   set = set()
        self._websites: set = set()
        self._emails:  set = set()
        self._total_skipped = 0

    def _norm(self, val: str) -> str:
        """Normalise a string key for comparison."""
        if not val or val == "N/A":
            return ""
        return re.sub(r'\s+', ' ', val.strip().lower())

    def _norm_url(self, url: str) -> str:
        if not url or url == "N/A":
            return ""
        try:
            parsed = urllib.parse.urlparse(url.lower().strip())
            # strip www. and trailing slash for comparison
            host = parsed.netloc.replace("www.", "")
            return host + parsed.path.rstrip("/")
        except:
            return url.lower().strip()

    def is_duplicate(self, name: str, website: str, email: str) -> bool:
        norm_name    = self._norm(name)
        norm_website = self._norm_url(website)
        norm_email   = self._norm(email)
        with self._lock:
            if norm_name    and norm_name    in self._names:    return True
            if norm_website and norm_website in self._websites: return True
            if norm_email   and norm_email   in self._emails:   return True
        return False

    def register(self, name: str, website: str, email: str):
        norm_name    = self._norm(name)
        norm_website = self._norm_url(website)
        norm_email   = self._norm(email)
        with self._lock:
            if norm_name:    self._names.add(norm_name)
            if norm_website: self._websites.add(norm_website)
            if norm_email:   self._emails.add(norm_email)

    def mark_skipped(self):
        with self._lock:
            self._total_skipped += 1

    @property
    def skipped(self):
        with self._lock:
            return self._total_skipped

# ════════════════════════════════════════════════════
#   ADVANCED KEYWORD ENGINE  (PRESERVED + IMPROVED)
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
                logger.debug(f"Autosuggest failed for '{term}': {e}")
            time.sleep(0.3)
        logger.info(f"[KEYWORDS] Autosuggest returned {len(results)} suggestions for '{keyword}'")
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
        logger.info(f"[KEYWORDS] Expansion produced {len(results)} variants for '{base_kw}'")
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
            logger.info(f"[KEYWORDS] AI generated {len(combined)} keywords total")
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
        # Guarantee minimum 100
        if len(final) < 100:
            for p in self.COMMERCIAL_PREFIXES:
                final.append(f"{p} {base_kw}")
        final = list(set(final))
        logger.info(f"[KEYWORDS] Full pool: {len(final)} unique keywords for '{base_kw}'")
        return final


# ════════════════════════════════════════════════════
#   FIXED GOOGLE MAPS SCRAPER
# ════════════════════════════════════════════════════
class GoogleMapsScraper:
    """
    Fixed scraper with:
    - Retry logic (3 attempts per offset)
    - Improved selector coverage
    - Correct rating extraction
    - Low-rating first sorting
    - Website fallback via Google search
    """

    MAX_RETRIES = 3
    RETRY_DELAY = 2  # seconds

    def _fetch_offset(self, query: str, start: int) -> list:
        url = f"https://www.google.com/search?q={query}&tbm=lcl&start={start}&num=20&hl=en&gl=us"
        for attempt in range(1, self.MAX_RETRIES + 1):
            try:
                res = requests.get(url, headers=get_headers(), timeout=12, verify=False)
                if res.status_code != 200:
                    logger.warning(f"[SCRAPE] HTTP {res.status_code} at offset {start} (attempt {attempt})")
                    time.sleep(self.RETRY_DELAY * attempt)
                    continue
                soup = BeautifulSoup(res.text, 'html.parser')

                # Extended selector list for better coverage
                blocks = soup.select(
                    'div.VkpGBb, div.rllt__details, div.uMdZh, '
                    'div.cXedhc, div.lqhpac, div[data-cid], '
                    'div.rl_tit, li.rllt__list-item'
                )

                if not blocks:
                    # Fallback: try generic local result blocks
                    blocks = soup.select('div[class*="rllt"], div[class*="VkpGBb"]')

                batch = []
                for block in blocks:
                    text_content = block.get_text(separator=' ', strip=True)

                    # ── Name ──
                    name_el = block.select_one(
                        'div[role="heading"], .dbg0pd, span.OSrXXb, '
                        '.rllt__details div:first-child, [class*="tit"]'
                    )
                    name = name_el.get_text(strip=True) if name_el else "N/A"
                    if name == "N/A" or len(name) < 3:
                        continue

                    # ── Rating — FIXED: extract correctly ──
                    # Pattern: digit.digit followed by optional space and review count
                    rating = "N/A"
                    rating_match = re.search(r'\b([1-5][\.,]\d)\b', text_content)
                    if rating_match:
                        rating = rating_match.group(1).replace(',', '.')
                    # Validate range
                    if rating != "N/A":
                        try:
                            r_val = float(rating)
                            if not (1.0 <= r_val <= 5.0):
                                rating = "N/A"
                        except:
                            rating = "N/A"

                    # ── Review count ──
                    review_count = "0"
                    rc_match = re.search(r'\((\d{1,6})\)', text_content)
                    if rc_match:
                        review_count = rc_match.group(1)

                    # ── Phone ──
                    phone = "N/A"
                    ph = re.search(
                        r'(\+?1?\s*[\-\.]?\(?\d{3}\)?[\s\-\.]?\d{3}[\s\-\.]?\d{4})',
                        text_content
                    )
                    if ph:
                        phone = ph.group(0).strip()

                    # ── Website ──
                    website = "N/A"
                    for a in block.select('a[href]'):
                        href = a.get('href', '')
                        if '/url?q=' in href:
                            clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                            if 'google' not in clean.lower() and clean.startswith('http'):
                                website = clean
                                break
                        elif href.startswith('http') and 'google' not in href.lower():
                            website = href
                            break

                    maps_link = (
                        f"https://www.google.com/maps/search/"
                        f"{urllib.parse.quote_plus(name)}"
                    )

                    batch.append({
                        "Name":        name,
                        "Phone":       phone,
                        "Website":     website,
                        "Rating":      rating,
                        "ReviewCount": review_count,
                        "Address":     "",        # filled at call site
                        "Category":    "",        # filled at call site
                        "Maps_Link":   maps_link,
                    })

                logger.info(f"[SCRAPE] offset={start} → {len(batch)} businesses extracted")
                return batch

            except requests.exceptions.RequestException as e:
                logger.warning(f"[SCRAPE] Request error offset={start} attempt={attempt}: {e}")
                time.sleep(self.RETRY_DELAY * attempt)
            except Exception as e:
                logger.error(f"[SCRAPE] Unexpected error offset={start}: {e}")
                break

        return []

    def fetch_batch(self, keyword: str, location: str) -> list:
        query = urllib.parse.quote_plus(f"{keyword} {location}")
        all_leads = []

        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
            futures = {
                executor.submit(self._fetch_offset, query, start): start
                for start in [0, 20, 40, 60, 80]
            }
            for future in concurrent.futures.as_completed(futures):
                try:
                    batch = future.result()
                    for lead in batch:
                        lead["Address"]  = location
                        lead["Category"] = keyword
                    all_leads.extend(batch)
                except Exception as e:
                    logger.error(f"[SCRAPE] Thread error: {e}")

        # ── Deduplicate within this batch by name ──
        seen_in_batch = set()
        unique_leads = []
        for lead in all_leads:
            key = lead["Name"].strip().lower()
            if key not in seen_in_batch:
                seen_in_batch.add(key)
                unique_leads.append(lead)

        # ── Sort: bad ratings first (ascending), then N/A at end ──
        def sort_key(lead):
            try:
                return float(lead["Rating"])
            except:
                return 6.0   # N/A pushed to the end

        unique_leads.sort(key=sort_key)

        logger.info(
            f"[SCRAPE] '{keyword}' in '{location}': "
            f"{len(all_leads)} raw → {len(unique_leads)} unique after batch dedup"
        )
        return unique_leads

    def find_website_via_search(self, business_name: str, location: str) -> str:
        """Fallback Google search to find an official website."""
        query = urllib.parse.quote_plus(f'"{business_name}" {location} official website')
        try:
            url = f"https://www.google.com/search?q={query}&num=5&hl=en"
            res = requests.get(url, headers=get_headers(), timeout=8, verify=False)
            soup = BeautifulSoup(res.text, 'html.parser')
            blacklist = ('google', 'facebook', 'yelp', 'tripadvisor',
                         'instagram', 'twitter', 'linkedin', 'youtube')
            for a in soup.select('a[href]'):
                href = a.get('href', '')
                if '/url?q=' in href:
                    clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                    if (clean.startswith('http') and
                            not any(b in clean.lower() for b in blacklist)):
                        return clean
        except Exception as e:
            logger.debug(f"[WEBSITE-SEARCH] failed for '{business_name}': {e}")
        return "N/A"


# ════════════════════════════════════════════════════
#   DEEP EMAIL EXTRACTOR  (PRESERVED + IMPROVED)
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
        # Standard regex
        emails.update(re.findall(self.email_regex, html))
        # Obfuscated [at] / (dot) patterns
        for ob in re.findall(
            r'[a-zA-Z0-9._%+\-]+\s*[\[\(]at[\]\)]\s*[a-zA-Z0-9.\-]+\s*[\[\(]dot[\]\)]\s*[a-zA-Z]{2,}',
            html, re.IGNORECASE
        ):
            cleaned = (ob.replace('[at]', '@').replace('(at)', '@')
                         .replace('[dot]', '.').replace('(dot)', '.').replace(' ', ''))
            if '@' in cleaned:
                emails.add(cleaned.lower())
        # mailto links
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
            logger.debug(f"[EMAIL] crawl failed for {url}: {e}")
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
            # Step 1: Homepage
            html = self.crawl_page(url)
            if html:
                visited.add(url)
                emails = self.extract_from_html(html)
                if emails:
                    logger.debug(f"[EMAIL] Found on homepage: {emails[0]}")
                    return emails[0]

                # Step 2: Internal contact/about pages found via links
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

            # Step 3: Try common paths directly
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
#   AI KEYWORD GENERATOR (ORIGINAL — PRESERVED)
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
#   MASTER JOB RUNNER  (FIXED RATING FILTER + DEDUP)
# ════════════════════════════════════════════════════
keyword_engine = AdvancedKeywordEngine()

def run_job_thread(job_id: str, data: dict):
    try:
        location    = data.get('location', '').strip()
        base_keyword = data.get('keyword', '').strip()
        max_leads   = min(int(data.get('max_leads', 10)), 200)
        max_rating  = data.get('max_rating')        # may be None / empty string
        webhook_url    = data.get('webhook_url', '')
        db_webhook_url = data.get('db_webhook_url', '')
        templates      = data.get('templates', [])

        # Normalise max_rating
        max_rating_float = None
        if max_rating:
            try:
                max_rating_float = float(str(max_rating).replace(',', '.'))
                logger.info(f"[JOB] Rating filter: rating <= {max_rating_float}")
            except:
                logger.warning(f"[JOB] Invalid max_rating '{max_rating}', ignoring filter")

        maps_scraper = GoogleMapsScraper()
        email_lib    = DeepEmailExtractor()
        db           = GoogleSheetsDB(db_webhook_url)
        dedup        = DeduplicationStore()

        jobs[job_id] = {
            'status': 'scraping',
            'count': 0,
            'leads': [],
            'emails_sent': 0,
            'total_to_send': 0,
            'status_text': 'Starting AI Keyword Generation...',
            'stats': {
                'scraped_total': 0,
                'after_rating_filter': 0,
                'duplicates_skipped': 0,
                'emails_found': 0,
                'errors': 0,
            }
        }

        if db_webhook_url:
            db.send_action("init", {})
            db.send_action("update_config", {
                "keyword_seed": base_keyword, "location": location,
                "target_leads": max_leads, "min_rating": "",
                "max_rating": max_rating or "", "email_required": "true",
                "status": "running"
            })
            db.log("System Start", f"Job for '{base_keyword}' in '{location}'")

        used_keywords   = set()
        pending_keywords = [base_keyword]

        # ─── PHASE 1: SCRAPE ──────────────────────────────────
        while len(jobs[job_id]['leads']) < max_leads:

            # Expand keyword pool when exhausted
            if not pending_keywords:
                jobs[job_id]['status_text'] = f"Generating 100+ new keywords for '{base_keyword}'..."
                new_kws = keyword_engine.generate_full_pool(base_keyword, location, used_keywords)
                random.shuffle(new_kws)
                pending_keywords.extend(new_kws)
                for kw in new_kws:
                    db.send_action("add_keyword", {
                        "keyword": kw, "source_seed": base_keyword, "status": "pending"
                    })

            current_kw = pending_keywords.pop(0)
            used_keywords.add(current_kw.lower())

            jobs[job_id]['status_text'] = f"Searching: {current_kw}..."
            raw_leads = maps_scraper.fetch_batch(current_kw, location)

            if not raw_leads:
                logger.info(f"[JOB] No results for keyword '{current_kw}'")
                continue

            jobs[job_id]['stats']['scraped_total'] += len(raw_leads)
            logger.info(f"[JOB] '{current_kw}' → {len(raw_leads)} businesses scraped")

            for lead in raw_leads:
                if len(jobs[job_id]['leads']) >= max_leads:
                    break

                # ── Save raw to DB regardless of filters ──
                db.send_action("add_scraped", {
                    "business_name": lead['Name'], "address": lead['Address'],
                    "phone": lead['Phone'], "rating": lead['Rating'],
                    "review_count": lead.get('ReviewCount', 'N/A'),
                    "website": lead['Website'], "keyword": current_kw, "status": "scraped"
                })

                # ── RATING FILTER (FIXED) ──────────────────────────
                # Include business only when rating <= max_rating_float
                if max_rating_float is not None and lead['Rating'] != "N/A":
                    try:
                        r_val = float(lead['Rating'])
                        if r_val > max_rating_float:
                            logger.debug(
                                f"[FILTER] Skipped '{lead['Name']}' rating={r_val} > max={max_rating_float}"
                            )
                            continue
                        else:
                            logger.debug(
                                f"[FILTER] Accepted '{lead['Name']}' rating={r_val} <= max={max_rating_float}"
                            )
                    except ValueError:
                        logger.debug(f"[FILTER] Could not parse rating '{lead['Rating']}' for '{lead['Name']}'")

                jobs[job_id]['stats']['after_rating_filter'] += 1

                # ── WEBSITE RESOLUTION (3-stage) ───────────────────
                website = lead['Website']
                if website == "N/A":
                    jobs[job_id]['status_text'] = f"Finding website for: {lead['Name']}..."
                    website = maps_scraper.find_website_via_search(lead['Name'], location)
                    lead['Website'] = website
                    if website != "N/A":
                        logger.info(f"[WEBSITE] Found via search for '{lead['Name']}': {website}")

                if website == "N/A":
                    logger.debug(f"[WEBSITE] No website found for '{lead['Name']}', skipping")
                    continue

                # ── DEDUPLICATION CHECK (pre-email) ────────────────
                if dedup.is_duplicate(lead['Name'], website, ""):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] Pre-email duplicate skipped: '{lead['Name']}'")
                    continue

                # ── EMAIL EXTRACTION ───────────────────────────────
                jobs[job_id]['status_text'] = f"Extracting email from: {lead['Name']}..."
                extracted_email = email_lib.get_email(website)

                if extracted_email == "N/A":
                    logger.debug(f"[EMAIL] No email found for '{lead['Name']}' at {website}")
                    continue

                jobs[job_id]['stats']['emails_found'] += 1

                # ── DEDUPLICATION CHECK (post-email) ───────────────
                if dedup.is_duplicate(lead['Name'], website, extracted_email):
                    dedup.mark_skipped()
                    jobs[job_id]['stats']['duplicates_skipped'] = dedup.skipped
                    logger.info(f"[DEDUP] Post-email duplicate skipped: '{lead['Name']}' / {extracted_email}")
                    continue

                # ── REGISTER IN DEDUP STORE ────────────────────────
                dedup.register(lead['Name'], website, extracted_email)

                # ── SAVE TO DB ─────────────────────────────────────
                db.send_action("add_email_lead", {
                    "business_name": lead['Name'], "website": website,
                    "email": extracted_email, "source_page": website, "status": "qualified"
                })
                db.send_action("add_qualified", {
                    "business_name": lead['Name'], "email": extracted_email,
                    "website": website, "rating": lead['Rating'],
                    "keyword": current_kw, "personalization_line": "Pending AI...",
                    "email_sent": "no"
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
                    f"(skipped dupes: {dedup.skipped})"
                )

            time.sleep(random.uniform(0.8, 1.8))

        # ── Final stats log ──
        s = jobs[job_id]['stats']
        logger.info(
            f"[JOB] Scraping complete — "
            f"scraped={s['scraped_total']}, "
            f"after_filter={s['after_rating_filter']}, "
            f"emails={s['emails_found']}, "
            f"duplicates_skipped={s['duplicates_skipped']}, "
            f"final_leads={len(jobs[job_id]['leads'])}"
        )
        db.send_action("update_config", {
            "keyword_seed": base_keyword, "location": location,
            "target_leads": max_leads, "min_rating": "",
            "max_rating": max_rating or "", "email_required": "true", "status": "stopped"
        })
        db.log("Scraping Done", f"Qualified: {len(jobs[job_id]['leads'])}")

        final_leads = jobs[job_id]['leads']

        # ─── PHASE 2: EMAIL SENDING ───────────────────────────
        if webhook_url and templates and final_leads:
            jobs[job_id]['status'] = 'sending_emails'
            jobs[job_id]['total_to_send'] = len(final_leads)
            emails_sent = 0

            for lead in final_leads:
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
                    logger.info(f"[EMAIL] Sent to {lead['Email']}")
                except Exception as e:
                    jobs[job_id]['stats']['errors'] += 1
                    logger.error(f"[EMAIL] Failed to send to {lead['Email']}: {e}")

                if emails_sent < len(final_leads):
                    delay = random.randint(60, 120)
                    for i in range(delay, 0, -1):
                        jobs[job_id]['status_text'] = (
                            f"Anti-spam cooldown: {i}s before next email..."
                        )
                        time.sleep(1)

        jobs[job_id]['status'] = 'done'
        jobs[job_id]['status_text'] = '✅ Process completed successfully!'
        db.log("Job Complete", "All tasks finished.")

    except Exception as e:
        logger.error(f"[JOB] Fatal error in job {job_id}: {e}", exc_info=True)
        jobs[job_id] = {'status': 'error', 'error': str(e)}


# ════════════════════════════════════════════════════
#   FLASK APP + REDESIGNED UI
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
/* ── Reset & Base ── */
*,*::before,*::after{box-sizing:border-box;margin:0;padding:0}
:root{
  --bg:       #f5f4f0;
  --surface:  #ffffff;
  --surface2: #f0efe9;
  --border:   #e2e0d8;
  --ink:      #1a1916;
  --ink2:     #6b6860;
  --ink3:     #a09e97;
  --accent:   #d4522a;
  --accent-h: #b8431f;
  --green:    #1e8a5e;
  --amber:    #c9820a;
  --red:      #c0392b;
  --blue:     #2962a8;
  --shadow:   0 1px 3px rgba(0,0,0,.07), 0 4px 16px rgba(0,0,0,.05);
  --radius:   10px;
}
html{font-size:16px}
body{
  background:var(--bg);
  color:var(--ink);
  font-family:'Outfit',system-ui,sans-serif;
  min-height:100vh;
  -webkit-font-smoothing:antialiased;
}
/* ── Typography ── */
h1,h2,h3,.syne{font-family:'Syne',sans-serif}
/* ── Layout ── */
.container{max-width:900px;margin:0 auto;padding:0 16px}
/* ── Nav ── */
.nav{
  background:var(--surface);
  border-bottom:1px solid var(--border);
  position:sticky;top:0;z-index:40;
}
.nav-inner{
  display:flex;align-items:center;justify-content:space-between;
  padding:14px 16px;max-width:900px;margin:0 auto;
}
.nav-brand{display:flex;align-items:center;gap:10px}
.nav-logo{
  width:34px;height:34px;background:var(--accent);border-radius:8px;
  display:flex;align-items:center;justify-content:center;color:#fff;font-size:15px;
  flex-shrink:0;
}
.nav-title{font-family:'Syne',sans-serif;font-size:16px;font-weight:700;letter-spacing:-.01em}
.nav-title span{color:var(--accent)}
.nav-sub{font-size:11px;color:var(--ink3);font-weight:400;margin-top:1px}
/* ── Stats Row ── */
.stats-row{
  display:grid;
  grid-template-columns:repeat(4,1fr);
  gap:10px;margin:20px 0;
}
@media(max-width:600px){.stats-row{grid-template-columns:repeat(2,1fr)}}
.stat-card{
  background:var(--surface);border:1px solid var(--border);
  border-radius:var(--radius);padding:14px 16px;
  box-shadow:var(--shadow);
}
.stat-val{font-family:'Syne',sans-serif;font-size:26px;font-weight:700;line-height:1}
.stat-lbl{font-size:11px;color:var(--ink3);margin-top:4px;font-weight:500;text-transform:uppercase;letter-spacing:.04em}
.stat-dot{width:7px;height:7px;border-radius:50%;display:inline-block;margin-right:5px}
/* ── Tabs ── */
.tab-bar{
  display:flex;gap:4px;overflow-x:auto;padding-bottom:1px;
  border-bottom:2px solid var(--border);margin-bottom:20px;
  -webkit-overflow-scrolling:touch;scrollbar-width:none;
}
.tab-bar::-webkit-scrollbar{display:none}
.tab-btn{
  background:none;border:none;padding:9px 14px;font-size:13px;font-weight:600;
  color:var(--ink3);cursor:pointer;white-space:nowrap;border-bottom:2px solid transparent;
  margin-bottom:-2px;transition:color .15s,border-color .15s;font-family:'Outfit',sans-serif;
  border-radius:6px 6px 0 0;
}
.tab-btn:hover{color:var(--ink)}
.tab-btn.active{color:var(--accent);border-bottom-color:var(--accent)}
/* ── Cards ── */
.card{
  background:var(--surface);border:1px solid var(--border);
  border-radius:var(--radius);padding:20px;
  box-shadow:var(--shadow);margin-bottom:16px;
}
.card-title{
  font-family:'Syne',sans-serif;font-size:14px;font-weight:700;
  display:flex;align-items:center;gap:8px;margin-bottom:16px;
}
.card-title i{color:var(--accent);width:16px;text-align:center}
/* ── Form Elements ── */
.form-grid{display:grid;grid-template-columns:1fr 1fr;gap:12px}
@media(max-width:560px){.form-grid{grid-template-columns:1fr}}
.form-group{display:flex;flex-direction:column;gap:5px}
label{font-size:12px;font-weight:600;color:var(--ink2);letter-spacing:.01em;text-transform:uppercase}
.inp{
  background:var(--bg);border:1.5px solid var(--border);
  color:var(--ink);border-radius:8px;padding:10px 13px;font-size:14px;
  width:100%;font-family:'Outfit',sans-serif;transition:border .15s,box-shadow .15s;outline:none;
}
.inp:focus{border-color:var(--accent);box-shadow:0 0 0 3px rgba(212,82,42,.1)}
.inp::placeholder{color:var(--ink3)}
/* ── Buttons ── */
.btn{
  display:inline-flex;align-items:center;justify-content:center;gap:8px;
  border:none;border-radius:8px;font-weight:600;font-size:14px;
  cursor:pointer;transition:all .15s;font-family:'Outfit',sans-serif;
  padding:11px 20px;white-space:nowrap;
}
.btn:disabled{opacity:.4;cursor:not-allowed;pointer-events:none}
.btn-primary{background:var(--accent);color:#fff}
.btn-primary:hover{background:var(--accent-h);transform:translateY(-1px);box-shadow:0 4px 14px rgba(212,82,42,.3)}
.btn-success{background:var(--green);color:#fff}
.btn-success:hover{filter:brightness(1.1);transform:translateY(-1px)}
.btn-neutral{background:var(--surface2);color:var(--ink);border:1.5px solid var(--border)}
.btn-neutral:hover{border-color:var(--ink2)}
.btn-ghost{background:none;color:var(--ink3);border:1.5px solid var(--border);font-size:12px;padding:7px 13px}
.btn-ghost:hover{color:var(--red);border-color:var(--red)}
.btn-full{width:100%}
/* ── Status / Progress ── */
.status-card{padding:16px;border-radius:var(--radius);border:1.5px solid var(--border);background:var(--surface)}
.status-header{display:flex;align-items:center;gap:10px;margin-bottom:12px;flex-wrap:wrap}
.status-icon{font-size:18px;flex-shrink:0}
.status-label{font-family:'Syne',sans-serif;font-size:14px;font-weight:700}
.progress-bar{height:4px;background:var(--surface2);border-radius:99px;overflow:hidden;margin-bottom:10px}
.progress-fill{height:100%;border-radius:99px;background:var(--accent);transition:width .5s ease}
.status-detail{font-size:12px;color:var(--ink3);font-family:'Outfit',monospace;background:var(--surface2);padding:10px 13px;border-radius:7px;min-height:36px;word-break:break-all;line-height:1.5}
/* ── Stats debug row ── */
.debug-stats{display:flex;flex-wrap:wrap;gap:8px;margin-top:10px}
.debug-chip{font-size:11px;padding:3px 9px;border-radius:99px;font-weight:600}
.chip-blue{background:rgba(41,98,168,.1);color:var(--blue)}
.chip-green{background:rgba(30,138,94,.1);color:var(--green)}
.chip-amber{background:rgba(201,130,10,.1);color:var(--amber)}
.chip-red{background:rgba(192,57,43,.1);color:var(--red)}
/* ── Table ── */
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
/* ── Divider ── */
.divider{height:1px;background:var(--border);margin:16px 0}
/* ── Notice box ── */
.notice{border-radius:8px;padding:10px 13px;font-size:12px;font-weight:500;margin-bottom:12px;display:flex;gap:8px;align-items:flex-start}
.notice i{margin-top:1px;flex-shrink:0}
.notice-warn{background:rgba(201,130,10,.08);border:1px solid rgba(201,130,10,.2);color:#7a4f00}
.notice-info{background:rgba(41,98,168,.07);border:1px solid rgba(41,98,168,.15);color:#183d6d}
/* ── Template items ── */
.tmpl-item{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px;position:relative}
.tmpl-name{font-family:'Syne',sans-serif;font-size:13px;font-weight:700;margin-bottom:3px}
.tmpl-sub{font-size:12px;color:var(--blue);margin-bottom:4px}
.tmpl-body{font-size:11px;color:var(--ink3);overflow:hidden;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical}
.tmpl-del{position:absolute;top:10px;right:10px;background:none;border:none;color:var(--ink3);cursor:pointer;font-size:13px;padding:4px}
.tmpl-del:hover{color:var(--red)}
/* ── History ── */
.hist-item{background:var(--surface2);border:1px solid var(--border);border-radius:8px;padding:12px 14px}
/* ── Animations ── */
.spin{animation:spin 1s linear infinite}
.blink{animation:bl 1.3s ease infinite}
@keyframes spin{to{transform:rotate(360deg)}}
@keyframes bl{0%,100%{opacity:1}50%{opacity:.3}}
.fade-in{animation:fi .25s ease}
@keyframes fi{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:translateY(0)}}
/* ── Utility ── */
.hidden{display:none!important}
.flex{display:flex}.items-center{align-items:center}.gap-2{gap:8px}.gap-3{gap:12px}
.justify-between{justify-content:space-between}.flex-1{flex:1}.mt-2{margin-top:8px}.mt-3{margin-top:12px}
.text-sm{font-size:12px}.text-xs{font-size:11px}.text-muted{color:var(--ink3)}
.font-bold{font-weight:700}.text-accent{color:var(--accent)}
.space-y > * + *{margin-top:10px}
/* ── Mobile tweaks ── */
@media(max-width:480px){
  .card{padding:14px}
  .btn{padding:10px 16px;font-size:13px}
  .stat-val{font-size:22px}
  .nav-title{font-size:14px}
}
</style>
</head>
<body>

<!-- NAV -->
<nav class="nav">
  <div class="nav-inner">
    <div class="nav-brand">
      <div class="nav-logo"><i class="fa-solid fa-bolt"></i></div>
      <div>
        <div class="nav-title">Lead<span>Gen</span> Pro</div>
        <div class="nav-sub">Scrape · Filter · Email</div>
      </div>
    </div>
    <div class="text-xs text-muted" id="job-badge" style="display:none">
      <span class="badge badge-warn blink" id="running-badge">● RUNNING</span>
    </div>
  </div>
</nav>

<div class="container" style="padding-top:20px;padding-bottom:40px">

  <!-- STATS -->
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

  <!-- TABS -->
  <div class="tab-bar">
    <button class="tab-btn active" id="tab-search"    onclick="showTab('search')"><i class="fa-solid fa-magnifying-glass"></i> Search</button>
    <button class="tab-btn"        id="tab-database"  onclick="showTab('database')"><i class="fa-solid fa-database"></i> Database</button>
    <button class="tab-btn"        id="tab-connect"   onclick="showTab('connect')"><i class="fa-solid fa-paper-plane"></i> Email</button>
    <button class="tab-btn"        id="tab-templates" onclick="showTab('templates')"><i class="fa-solid fa-file-lines"></i> Templates</button>
    <button class="tab-btn"        id="tab-history"   onclick="showTab('history')"><i class="fa-solid fa-clock-rotate-left"></i> History</button>
  </div>

  <!-- ═══ SEARCH PANE ═══ -->
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
        <span><b>Strict mode:</b> Only leads with a valid email are counted. AI auto-expands keywords until your target is hit. Rating filter keeps businesses ≤ max rating.</span>
      </div>

      <button onclick="startJob()" id="btn-run" class="btn btn-primary btn-full mt-2" style="margin-top:12px">
        <i class="fa-solid fa-play"></i>Start Scraping
      </button>
    </div>

    <!-- STATUS -->
    <div id="sbox" class="hidden card fade-in">
      <div class="status-header">
        <i id="si" class="fa-solid fa-circle-notch spin status-icon" style="color:var(--accent)"></i>
        <span id="stxt" class="status-label">Processing...</span>
      </div>
      <div class="progress-bar"><div class="progress-fill" id="sbar" style="width:0%"></div></div>
      <div id="sdet" class="status-detail">Initialising...</div>

      <!-- Debug stats chips -->
      <div class="debug-stats" id="debug-stats"></div>

      <button id="dlbtn" onclick="doDL()" class="btn btn-success btn-full mt-3 hidden">
        <i class="fa-solid fa-download"></i>Download Leads CSV
      </button>
    </div>

    <!-- PREVIEW TABLE -->
    <div id="pvbox" class="hidden card fade-in">
      <div class="flex items-center justify-between" style="margin-bottom:14px">
        <div class="card-title" style="margin-bottom:0"><i class="fa-solid fa-table-cells"></i>Preview <span id="pvcnt" class="text-muted" style="font-weight:400;font-size:12px"></span></div>
        <button onclick="doDL()" class="btn btn-neutral" style="font-size:12px;padding:7px 13px"><i class="fa-solid fa-download"></i> CSV</button>
      </div>
      <div class="table-wrap">
        <table>
          <thead><tr id="th"></tr></thead>
          <tbody id="tb"></tbody>
        </table>
      </div>
    </div>

  </div><!-- /pane-search -->

  <!-- ═══ DATABASE PANE ═══ -->
  <div id="pane-database" class="hidden fade-in">
    <div class="card">
      <div class="card-title"><i class="fa-solid fa-database"></i>Connect Google Sheets Database</div>
      <div class="notice notice-info">
        <i class="fa-solid fa-circle-info"></i>
        <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → New Project → paste script → Deploy as Web App (Anyone) → copy URL.</span>
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
      getOrCreateSheet("Scraped_Businesses",["business_name","address","phone","rating","review_count","website","keyword","status"]);
      getOrCreateSheet("Email_Leads",["business_name","website","email","source_page","status"]);
      getOrCreateSheet("Qualified_Leads",["business_name","email","website","rating","keyword","personalization_line","email_sent"]);
      getOrCreateSheet("Logs",["timestamp","action","details"]);
    } else if (action === "log") { var s=ss.getSheetByName("Logs"); if(s) s.appendRow([data.timestamp,data.action,data.details]); }
    else if (action === "add_keyword") { var s=ss.getSheetByName("Generated_Keywords"); if(s) s.appendRow([data.keyword,data.source_seed,data.status]); }
    else if (action === "add_scraped") { var s=ss.getSheetByName("Scraped_Businesses"); if(s) s.appendRow([data.business_name,data.address,data.phone,data.rating,data.review_count,data.website,data.keyword,data.status]); }
    else if (action === "add_email_lead") { var s=ss.getSheetByName("Email_Leads"); if(s) s.appendRow([data.business_name,data.website,data.email,data.source_page,data.status]); }
    else if (action === "add_qualified") { var s=ss.getSheetByName("Qualified_Leads"); if(s) s.appendRow([data.business_name,data.email,data.website,data.rating,data.keyword,data.personalization_line,data.email_sent]); }
    else if (action === "update_config") { var s=ss.getSheetByName("Config"); if(s){s.clearContents();s.appendRow(["keyword_seed","location","target_leads","min_rating","max_rating","email_required","status"]);s.appendRow([data.keyword_seed,data.location,data.target_leads,data.min_rating,data.max_rating,data.email_required,data.status]);} }
    else if (action === "update_email_sent") { var s=ss.getSheetByName("Qualified_Leads"); if(s){var v=s.getDataRange().getValues();for(var i=1;i<v.length;i++){if(v[i][1]===data.email){s.getRange(i+1,6).setValue(data.personalization_line);s.getRange(i+1,7).setValue("yes");break;}}} }
    return ContentService.createTextOutput(JSON.stringify({status:"success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(e) { return ContentService.createTextOutput(JSON.stringify({status:"error",message:e.toString()})).setMimeType(ContentService.MimeType.JSON); }
  finally { lock.releaseLock(); }
}
function doGet(e) { return ContentService.createTextOutput(JSON.stringify({status:"active"})).setMimeType(ContentService.MimeType.JSON); }</textarea>
      </div>
      <div class="form-group" style="margin-bottom:12px">
        <label>🔗 Database Web App URL</label>
        <input id="db-webhook-url" class="inp" placeholder="https://script.google.com/macros/s/AKfycb.../exec">
      </div>
      <button onclick="saveDBWebhook()" class="btn btn-primary btn-full"><i class="fa-solid fa-link"></i>Connect Database</button>
    </div>
  </div>

  <!-- ═══ EMAIL PANE ═══ -->
  <div id="pane-connect" class="hidden fade-in">
    <div class="card">
      <div class="card-title"><i class="fa-solid fa-paper-plane"></i>Gmail Sender Setup</div>
      <div class="notice notice-info">
        <i class="fa-solid fa-circle-info"></i>
        <span>Go to <a href="https://script.google.com" target="_blank" style="color:var(--blue)">script.google.com</a> → paste code → Deploy as Web App (Anyone) → copy URL.</span>
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
      <div class="form-group" style="margin-bottom:12px">
        <label>🔗 Email Web App URL</label>
        <input id="webhook-url" class="inp" placeholder="https://script.google.com/macros/s/AKfycb.../exec">
      </div>
      <button onclick="saveWebhook()" class="btn btn-success btn-full"><i class="fa-solid fa-save"></i>Save Email Webhook</button>
    </div>
  </div>

  <!-- ═══ TEMPLATES PANE ═══ -->
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

  <!-- ═══ HISTORY PANE ═══ -->
  <div id="pane-history" class="hidden fade-in">
    <div class="card">
      <div class="flex items-center justify-between" style="margin-bottom:14px">
        <div class="card-title" style="margin-bottom:0"><i class="fa-solid fa-clock-rotate-left"></i>History</div>
        <button onclick="clearHistory()" class="btn btn-ghost"><i class="fa-solid fa-trash"></i> Clear</button>
      </div>
      <div id="h-list" class="space-y"></div>
    </div>
  </div>

</div><!-- /container -->

<script>
let jid=null, templates=[], historyData=[], tableShown=false, lastStats={};

window.onload = () => {
  document.getElementById('webhook-url').value     = localStorage.getItem('webhook_url')     || '';
  document.getElementById('db-webhook-url').value  = localStorage.getItem('db_webhook_url')  || '';
  templates    = JSON.parse(localStorage.getItem('templates')  || '[]');
  historyData  = JSON.parse(localStorage.getItem('history')    || '[]');
  renderTemplates(); renderHistory();
};

/* ── Tabs ── */
const TABS = ['search','database','connect','templates','history'];
function showTab(t) {
  TABS.forEach(x => {
    document.getElementById('pane-'+x).classList.add('hidden');
    document.getElementById('tab-'+x).classList.remove('active');
  });
  document.getElementById('pane-'+t).classList.remove('hidden');
  document.getElementById('tab-'+t).classList.add('active');
}

/* ── Webhooks ── */
function saveWebhook()   { localStorage.setItem('webhook_url',    document.getElementById('webhook-url').value.trim());    alert('Email webhook saved!'); }
function saveDBWebhook() { localStorage.setItem('db_webhook_url', document.getElementById('db-webhook-url').value.trim()); alert('Database webhook saved!'); }
function copyDBScript()  { const el=document.getElementById('db-script-code'); el.select(); document.execCommand('copy'); alert('Script copied!'); }

/* ── Templates ── */
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

/* ── History ── */
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

/* ── Status helper ── */
function setSt(msg, state='load', pct=null) {
  document.getElementById('sbox').classList.remove('hidden');
  document.getElementById('sdet').textContent = msg;
  const ic=document.getElementById('si'), txt=document.getElementById('stxt');
  const iconMap = {
    load:  ['fa-circle-notch spin','var(--accent)',   'Scraping Engine Running…'],
    email: ['fa-paper-plane blink', 'var(--green)',   'Sending Emails…'],
    done:  ['fa-circle-check',      'var(--green)',   'Completed!'],
    err:   ['fa-circle-xmark',      'var(--red)',     'Error Occurred'],
  };
  const [iconCls,col,label] = iconMap[state] || iconMap.load;
  ic.className = `fa-solid ${iconCls} status-icon`;
  ic.style.color = col;
  txt.textContent = label;
  if(pct!=null) document.getElementById('sbar').style.width = Math.min(100,pct)+'%';
  // Running badge
  const badge=document.getElementById('job-badge');
  if(state==='load'||state==='email'){ badge.style.display=''; }
  else { badge.style.display='none'; }
}

/* ── Debug chips ── */
function renderDebugStats(stats) {
  if(!stats) return;
  const el = document.getElementById('debug-stats');
  el.innerHTML = `
    <span class="debug-chip chip-blue">Scraped: ${stats.scraped_total||0}</span>
    <span class="debug-chip chip-amber">After filter: ${stats.after_rating_filter||0}</span>
    <span class="debug-chip chip-green">Emails: ${stats.emails_found||0}</span>
    <span class="debug-chip chip-red">Dupes skipped: ${stats.duplicates_skipped||0}</span>
    <span class="debug-chip chip-red">Errors: ${stats.errors||0}</span>
  `;
}

/* ── Stats counters ── */
function updStats(leads) {
  document.getElementById('st-leads').textContent  = leads.length;
  document.getElementById('st-emails').textContent = leads.filter(l=>l.Email&&l.Email!='N/A').length;
  document.getElementById('st-phones').textContent = leads.filter(l=>l.Phone&&l.Phone!='N/A').length;
  document.getElementById('st-webs').textContent   = leads.filter(l=>l.Website&&l.Website!='N/A').length;
}

/* ── Preview table ── */
function showPV(leads) {
  if(!leads?.length) return;
  document.getElementById('pvbox').classList.remove('hidden');
  document.getElementById('pvcnt').textContent = `(${leads.length} total · showing top 10)`;
  const keys = Object.keys(leads[0]).filter(k=>k!=='Maps_Link');
  document.getElementById('th').innerHTML = keys.map(k=>`<th>${k}</th>`).join('');
  document.getElementById('tb').innerHTML = leads.slice(0,10).map(l=>
    `<tr>${keys.map(k=>{
      const v=(l[k]||'N/A').toString();
      const cls = v==='N/A' ? 'badge-na'
                : k==='Email'  ? 'badge-ok'
                : k==='Rating' ? 'badge-warn'
                : k==='Phone'  ? 'badge-info'
                : '';
      const disp = v.length>40 ? v.substring(0,40)+'…' : v;
      return `<td>${cls?`<span class="badge ${cls}">${disp}</span>`:disp}</td>`;
    }).join('')}</tr>`
  ).join('');
}

/* ── Start job ── */
async function startJob() {
  const loc   = document.getElementById('m-loc').value.trim();
  const kw    = document.getElementById('m-kw').value.trim();
  let   count = Math.min(parseInt(document.getElementById('m-count').value)||10, 200);
  if(!loc||!kw) return alert('Location and Keyword are required!');
  const webhook    = localStorage.getItem('webhook_url')    || '';
  const db_webhook = localStorage.getItem('db_webhook_url') || '';

  setSt('Initialising…', 'load', 2);
  document.getElementById('dlbtn').classList.add('hidden');
  document.getElementById('pvbox').classList.add('hidden');
  document.getElementById('debug-stats').innerHTML = '';
  document.getElementById('btn-run').disabled = true;
  tableShown = false;

  const payload = {
    location: loc, keyword: kw, max_leads: count,
    max_rating:   document.getElementById('m-rating').value.trim() || null,
    webhook_url:  webhook,
    db_webhook_url: db_webhook,
    templates: templates,
  };

  try {
    const r = await fetch('/api/scrape',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});
    const d = await r.json();
    if(d.error){ setSt(d.error,'err'); document.getElementById('btn-run').disabled=false; return; }
    jid = d.job_id;
    historyData.unshift({loc,kw,target:count,date:new Date().toLocaleString()});
    localStorage.setItem('history',JSON.stringify(historyData)); renderHistory();
    startPolling(count);
  } catch(e) {
    setSt('Could not connect to server.','err');
    document.getElementById('btn-run').disabled=false;
  }
}

/* ── Polling ── */
function startPolling(target) {
  const poll = async () => {
    try {
      const r2 = await fetch('/api/status/'+jid);
      const d2 = await r2.json();
      if(d2.stats) renderDebugStats(d2.stats);
      if(d2.status==='scraping') {
        const pct = Math.max(3, (d2.count / target) * 95);
        setSt(d2.status_text||'Scraping…', 'load', pct);
        if(d2.leads?.length){ updStats(d2.leads); if(!tableShown){showPV(d2.leads);tableShown=true;} }
        setTimeout(poll, 2500);
      } else if(d2.status==='sending_emails') {
        if(!tableShown&&d2.leads){ updStats(d2.leads); showPV(d2.leads); tableShown=true; }
        document.getElementById('dlbtn').classList.remove('hidden');
        const pct = d2.total_to_send>0 ? (d2.emails_sent/d2.total_to_send)*100 : 50;
        setSt(d2.status_text||'Sending…','email',pct);
        setTimeout(poll, 2500);
      } else if(d2.status==='done') {
        document.getElementById('btn-run').disabled=false;
        if(d2.leads){ updStats(d2.leads); showPV(d2.leads); }
        setSt(d2.status_text||'Done!','done',100);
        document.getElementById('dlbtn').classList.remove('hidden');
      } else if(d2.status==='error') {
        document.getElementById('btn-run').disabled=false;
        setSt(d2.error||'Unknown error','err');
      } else {
        setTimeout(poll, 2500);
      }
    } catch(e) { setTimeout(poll, 2500); }
  };
  setTimeout(poll, 1500);
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
    data = request.json
    job_id = str(uuid.uuid4())[:8]
    logger.info(f"[API] New job {job_id}: keyword='{data.get('keyword')}' loc='{data.get('location')}' target={data.get('max_leads')} max_rating={data.get('max_rating')}")
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
    out = io.StringIO()
    writer = csv.DictWriter(out, fieldnames=leads[0].keys())
    writer.writeheader()
    writer.writerows(leads)
    out.seek(0)
    return send_file(
        io.BytesIO(out.getvalue().encode('utf-8-sig')),
        mimetype='text/csv',
        as_attachment=True,
        download_name='Target_Leads.csv'
    )


# ════════════════════════════════════════════════════
#   TELEGRAM BOT  (PRESERVED)
# ════════════════════════════════════════════════════
def to_csv(leads):
    tmp = tempfile.NamedTemporaryFile(mode='w', suffix='.csv', delete=False, encoding='utf-8-sig', newline='')
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
        "👋 *LeadGen Pro Bot*\n\n✅ Strict Valid Emails Only\n✅ Auto AI Keyword Expansion\n✅ Deduplication Active\n✅ Rating Filter Fixed\n✅ Max Limit: 200",
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
    await update.message.reply_text("🔢 Enter Target Number of Valid Emails (Max 200):")
    return M_COUNT

async def m_count(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    count = int(update.message.text) if update.message.text.isdigit() else 10
    if count > 200: count = 200
    uid = update.message.from_user.id
    bot_store[uid]['count'] = count
    await update.message.reply_text("⭐ Max Rating Filter? (Type 'skip' to ignore, e.g. 3.5):")
    return M_RATING

async def m_rating(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    txt = update.message.text.lower()
    uid = update.message.from_user.id
    bot_store[uid]['rating'] = None if txt == 'skip' else txt
    data = bot_store[uid]
    summary = (
        f"📋 *Target Config*\n📍 {data['loc']}\n🔍 {data['kw']}\n"
        f"🔢 {data['count']} valid emails\n⭐ Max Rating: {data.get('rating') or 'None'}\n\nStart?"
    )
    kb = [[InlineKeyboardButton("✅ Start", callback_data="start_scrape")]]
    await update.message.reply_text(summary, parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(kb))
    return ConversationHandler.END

def run_bot_scrape_fast(data: dict) -> list:
    location    = data['loc']
    base_keyword = data['kw']
    max_leads   = data['count']
    max_rating  = data.get('rating')

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
    final_leads      = []

    while len(final_leads) < max_leads:
        if not pending_keywords:
            new_kws = kw_engine.generate_full_pool(base_keyword, location, used_keywords)
            random.shuffle(new_kws)
            pending_keywords.extend(new_kws)

        current_kw = pending_keywords.pop(0)
        used_keywords.add(current_kw.lower())
        raw_leads = m_scraper.fetch_batch(current_kw, location)

        for lead in raw_leads:
            if len(final_leads) >= max_leads: break

            # Rating filter
            if max_rating_float is not None and lead['Rating'] != "N/A":
                try:
                    if float(lead['Rating']) > max_rating_float: continue
                except: pass

            # Website resolution
            website = lead['Website']
            if website == "N/A":
                website = m_scraper.find_website_via_search(lead['Name'], location)
                lead['Website'] = website
            if website == "N/A": continue

            # Pre-email dedup
            if dedup.is_duplicate(lead['Name'], website, ""): continue

            extracted_email = e_lib.get_email(website)
            if extracted_email == "N/A": continue

            # Post-email dedup
            if dedup.is_duplicate(lead['Name'], website, extracted_email): continue
            dedup.register(lead['Name'], website, extracted_email)

            lead['Email'] = extracted_email
            final_leads.append(lead)

    return final_leads

async def background_bot_task(chat_id, message_id, data, bot):
    try:
        await bot.edit_message_text(
            chat_id=chat_id, message_id=message_id,
            text="⏳ *Scraping with AI keywords...*\n_Deduplication active. Rating filter applied._",
            parse_mode='Markdown'
        )
        loop = asyncio.get_event_loop()
        final_leads = await loop.run_in_executor(None, run_bot_scrape_fast, data)
        if not final_leads:
            await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="😔 No results found.")
            return
        path = to_csv(final_leads)
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="✅ Done! Sending file...")
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
        logger.info("Telegram bot started")
    port = int(os.environ.get("PORT", 10000))
    logger.info(f"Flask starting on port {port}")
    flask_app.run(host='0.0.0.0', port=port)
