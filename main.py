import os, csv, asyncio, tempfile, threading, io, uuid, re, time, json, urllib.parse, random
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

# Suppress SSL warnings for cleaner logs and slightly faster requests
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
load_dotenv()

# ==========================================
# ⚙️ CONFIGURATION
# ==========================================
TELEGRAM_TOKEN = os.getenv("TELEGRAM_BOT_TOKEN")
GROQ_API_KEY = os.getenv("GROQ_API_KEY")

def get_headers():
    HEADERS_LIST = [
        "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 Chrome/120.0.0.0 Safari/537.36",
        "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_15_7) AppleWebKit/537.36 Chrome/119.0.0.0 Safari/537.36",
        "Mozilla/5.0 (X11; Linux x86_64) AppleWebKit/537.36 Chrome/118.0.0.0 Safari/537.36",
    ]
    return {
        "User-Agent": random.choice(HEADERS_LIST),
        "Accept-Language": "en-US,en;q=0.9",
        "Accept": "text/html,application/xhtml+xml,application/xml;q=0.9,image/webp,*/*;q=0.8",
        "Referer": "https://www.google.com/",
    }

# ══════════════════════════════════════════════
#   [NEW] GOOGLE SHEETS ASYNC DATABASE WRAPPER
# ══════════════════════════════════════════════
class GoogleSheetsDB:
    """Handles all database operations asynchronously so it doesn't slow down the scraper."""
    def __init__(self, webhook_url):
        self.url = webhook_url

    def _post_async(self, payload):
        try:
            requests.post(self.url, json=payload, timeout=15)
        except Exception as e:
            pass # Fail silently in background to prevent crashing

    def send_action(self, action, data):
        if not self.url: return
        payload = {"action": action, "data": data}
        # Fire and forget thread
        threading.Thread(target=self._post_async, args=(payload,), daemon=True).start()

    def log(self, action, details):
        self.send_action("log", {
            "timestamp": time.strftime("%Y-%m-%d %H:%M:%S"),
            "action": action,
            "details": details
        })

# ══════════════════════════════════════════════
#   1. SUPER FAST PURE PYTHON SCRAPER
# ══════════════════════════════════════════════
class GoogleMapsScraper:
    def fetch_batch(self, keyword, location):
        query = urllib.parse.quote_plus(f"{keyword} in {location}")
        all_leads = []
        
        def get_offset(start):
            url = f"https://www.google.com/search?q={query}&tbm=lcl&start={start}&num=20&hl=en"
            try:
                res = requests.get(url, headers=get_headers(), timeout=10)
                soup = BeautifulSoup(res.text, 'html.parser')
                blocks = soup.select('div.VkpGBb, div.rllt__details, div.uMdZh, div.cXedhc')
                batch = []
                
                for block in blocks:
                    text_content = block.get_text(separator=' ', strip=True)
                    
                    name_el = block.select_one('div[role="heading"], .dbg0pd, span.OSrXXb')
                    name = name_el.get_text(strip=True) if name_el else "N/A"
                    if name == "N/A" or len(name) < 3: continue
                    
                    rating_match = re.search(r'(\d[\.,]\d)\s*[\(\d]', text_content)
                    rating = rating_match.group(1).replace(',', '.') if rating_match else "N/A"
                    
                    ph = re.search(r'(\+?\d{1,3}[\s\-\(\)]?\d{3,4}[\s\-\(\)]?\d{3,4}[\s\-\(\)]?\d{3,4})', text_content)
                    phone = ph.group(0).strip() if ph else "N/A"
                    
                    website = "N/A"
                    for a in block.select('a[href]'):
                        href = a['href']
                        if '/url?q=' in href:
                            clean = urllib.parse.unquote(href.split('/url?q=')[1].split('&')[0])
                            if 'google' not in clean.lower() and clean.startswith('http'):
                                website = clean; break
                        elif href.startswith('http') and 'google' not in href.lower():
                            website = href; break
                            
                    batch.append({
                        "Name": name,
                        "Phone": phone,
                        "Website": website,
                        "Rating": rating,
                        "Address": location,
                        "Category": keyword,
                        "Maps_Link": f"https://www.google.com/maps/search/{urllib.parse.quote_plus(name + ' ' + location)}"
                    })
                return batch
            except Exception:
                return []

        with concurrent.futures.ThreadPoolExecutor(max_workers=5) as executor:
            results = executor.map(get_offset, [0, 20, 40, 60, 80])
            for res in results:
                all_leads.extend(res)
                
        return all_leads

# ══════════════════════════════════════════════
#   2. DEEP EMAIL EXTRACTOR
# ══════════════════════════════════════════════
class DeepEmailExtractor:
    def __init__(self):
        self.email_regex = r'[a-zA-Z0-9._%+\-]+@[a-zA-Z0-9.\-]+\.[a-zA-Z]{2,}'
        self.bad_keywords = ['example', 'domain', 'sentry', '@2x', '.png', '.jpg', '.jpeg', '.gif', 'wixpress', 'bootstrap', 'rating']

    def is_valid_email(self, email):
        email = email.lower()
        return not any(bad in email for bad in self.bad_keywords)

    def get_email(self, url):
        if not url or url == "N/A": return "N/A"
        if not url.startswith('http'): url = 'http://' + url
        
        visited_urls = set()
        
        try:
            r = requests.get(url, headers=get_headers(), timeout=6, verify=False)
            visited_urls.add(url)
            
            emails = list(set(re.findall(self.email_regex, r.text)))
            valid_emails = [e for e in emails if self.is_valid_email(e)]
            if valid_emails: return valid_emails[0]
            
            soup = BeautifulSoup(r.text, 'html.parser')
            internal_links = []
            for a in soup.select('a[href]'):
                href = a.get('href', '').lower()
                if any(kw in href for kw in ['contact', 'about', 'support', 'help']):
                    full_link = urllib.parse.urljoin(url, a['href'])
                    if full_link not in visited_urls and full_link.startswith('http'):
                        internal_links.append(full_link)
            
            for link in list(set(internal_links))[:3]:
                try:
                    r2 = requests.get(link, headers=get_headers(), timeout=6, verify=False)
                    visited_urls.add(link)
                    emails2 = list(set(re.findall(self.email_regex, r2.text)))
                    valid_emails2 = [e for e in emails2 if self.is_valid_email(e)]
                    if valid_emails2: return valid_emails2[0]
                except:
                    continue
                    
        except: pass
        return "N/A"

# ══════════════════════════════════════════════
#   3. AI KEYWORD GENERATOR & PERSONALIZER
# ══════════════════════════════════════════════
def generate_ai_keywords(base_kw, location, used_kws):
    fallback = [f"best {base_kw}", f"top {base_kw}", f"{base_kw} services", f"affordable {base_kw}", f"{base_kw} agency", f"{base_kw} near me", f"{base_kw} company", f"{base_kw} experts"]
    if not GROQ_API_KEY: return fallback
    try:
        client = Groq(api_key=GROQ_API_KEY)
        # UPGRADED: Now asks for 100+ keywords to ensure massive pool
        prompt = f"I am searching for '{base_kw}' in '{location}'. Used keywords: {list(used_kws)}. Generate 100 NEW, highly related search terms/categories. Return ONLY a comma-separated list."
        res = client.chat.completions.create(
            messages=[{"role": "user", "content": prompt}],
            model="llama3-8b-8192",
            temperature=0.7,
        )
        text = res.choices[0].message.content
        new_kws = [k.strip() for k in text.split(',') if k.strip() and k.strip().lower() not in used_kws]
        return new_kws if new_kws else fallback
    except:
        return fallback

def personalize_email(lead_name, niche, template_subject, template_body, rating):
    if not GROQ_API_KEY: return template_subject, template_body, ""
    try:
        client = Groq(api_key=GROQ_API_KEY)
        # UPGRADED: Now generates a specific personalization line based on rating/niche
        prompt = f"""
        You are an expert cold email copywriter. Personalize this email for a business.
        Business Name: {lead_name}
        Niche: {niche}
        Current Rating: {rating} (If below 4.0, mention helping them improve it. If high, compliment it).
        Original Subject: {template_subject}
        Original Body: {template_body}
        
        Return ONLY a valid JSON object with keys:
        "subject" (personalized subject),
        "body" (personalized HTML body),
        "personalization_line" (A single, highly personalized opening sentence based on their business and rating).
        """
        res = client.chat.completions.create(
            messages=[{"role": "user", "content": prompt}],
            model="llama3-8b-8192",
            temperature=0.5,
        )
        content = res.choices[0].message.content
        json_match = re.search(r'\{.*\}', content, re.DOTALL)
        if json_match:
            data = json.loads(json_match.group(0))
            return data.get("subject", template_subject), data.get("body", template_body), data.get("personalization_line", "")
        return template_subject, template_body, ""
    except Exception as e:
        return template_subject, template_body, ""

# ══════════════════════════════════════════════
#   4. MASTER EXECUTION THREAD (Scrape + DB + Email)
# ══════════════════════════════════════════════
def run_job_thread(job_id, data):
    try:
        location = data.get('location')
        base_keyword = data.get('keyword')
        max_leads = min(int(data.get('max_leads', 10)), 200)
        max_rating = data.get('max_rating')
        webhook_url = data.get('webhook_url')
        db_webhook_url = data.get('db_webhook_url') # NEW: DB Webhook
        templates = data.get('templates', [])
        
        maps_scraper = GoogleMapsScraper()
        email_lib = DeepEmailExtractor()
        db = GoogleSheetsDB(db_webhook_url)
        
        jobs[job_id] = {'status': 'scraping', 'count': 0, 'leads': [], 'status_text': 'Starting AI Keyword Generation...'}
        
        # [DB] Initialize Sheets & Config
        if db_webhook_url:
            db.send_action("init", {})
            db.send_action("update_config", {
                "keyword_seed": base_keyword, "location": location, "target_leads": max_leads,
                "min_rating": "", "max_rating": max_rating or "", "email_required": "true", "status": "running"
            })
            db.log("System Start", f"Started job for {base_keyword} in {location}")

        seen_names = set()
        used_keywords = set()
        pending_keywords = [base_keyword]
        
        # --- PHASE 1: STRICT SCRAPING (UNTIL TARGET HIT) ---
        while len(jobs[job_id]['leads']) < max_leads:
            
            if not pending_keywords:
                jobs[job_id]['status_text'] = f"Generating 100+ new keywords for '{base_keyword}'..."
                new_kws = generate_ai_keywords(base_keyword, location, used_keywords)
                pending_keywords.extend(new_kws)
                
                # [DB] Save generated keywords
                for kw in new_kws:
                    db.send_action("add_keyword", {"keyword": kw, "source_seed": base_keyword, "status": "pending"})
                
            current_kw = pending_keywords.pop(0)
            used_keywords.add(current_kw.lower())
            
            jobs[job_id]['status_text'] = f"Searching Google Maps for: {current_kw}..."
            raw_leads = maps_scraper.fetch_batch(current_kw, location)
            
            if not raw_leads:
                continue 
            
            for lead in raw_leads:
                if len(jobs[job_id]['leads']) >= max_leads:
                    break # Target Hit!
                    
                if lead['Name'] in seen_names:
                    continue
                
                # [DB] Save raw scraped business
                db.send_action("add_scraped", {
                    "business_name": lead['Name'], "address": lead['Address'], "phone": lead['Phone'],
                    "rating": lead['Rating'], "review_count": "N/A", "website": lead['Website'],
                    "keyword": current_kw, "status": "scraped"
                })

                # Apply Rating Filter
                if max_rating and lead['Rating'] != "N/A":
                    try:
                        if float(lead['Rating']) > float(max_rating): continue
                    except: pass

                if lead['Website'] == "N/A":
                    continue 
                    
                jobs[job_id]['status_text'] = f"Deep searching email for: {lead['Name']}..."
                extracted_email = email_lib.get_email(lead['Website'])
                
                if extracted_email == "N/A":
                    continue 
                
                # [DB] Save Email Lead
                db.send_action("add_email_lead", {
                    "business_name": lead['Name'], "website": lead['Website'],
                    "email": extracted_email, "source_page": lead['Website'], "status": "qualified"
                })
                
                # [DB] Move to Qualified Leads
                db.send_action("add_qualified", {
                    "business_name": lead['Name'], "email": extracted_email, "website": lead['Website'],
                    "rating": lead['Rating'], "keyword": current_kw, "personalization_line": "Pending AI...", "email_sent": "no"
                })

                lead['Email'] = extracted_email
                seen_names.add(lead['Name'])
                jobs[job_id]['leads'].append(lead)
                jobs[job_id]['count'] = len(jobs[job_id]['leads'])
                
                jobs[job_id]['status_text'] = f"🎯 Found {jobs[job_id]['count']}/{max_leads} valid emails! (Latest: {lead['Email']})"
                
            time.sleep(1)
            
        final_leads = jobs[job_id]['leads']
        
        # [DB] Update Config to Stopped
        db.send_action("update_config", {
            "keyword_seed": base_keyword, "location": location, "target_leads": max_leads,
            "min_rating": "", "max_rating": max_rating or "", "email_required": "true", "status": "stopped"
        })
        db.log("Scraping Stopped", f"Target reached. Total qualified: {len(final_leads)}")
        
        # --- PHASE 2: AUTOMATED EMAIL SENDING ---
        if webhook_url and templates and len(final_leads) > 0:
            jobs[job_id]['status'] = 'sending_emails'
            jobs[job_id]['total_to_send'] = len(final_leads)
            emails_sent = 0
            
            for lead in final_leads:
                jobs[job_id]['status_text'] = f"Sending personalized email {emails_sent+1}/{jobs[job_id]['total_to_send']} to {lead['Email']}..."
                
                template = random.choice(templates)
                # UPGRADED: Now generates personalization line
                p_subject, p_body, p_line = personalize_email(lead['Name'], base_keyword, template['subject'], template['body'], lead['Rating'])
                
                payload = {"to": lead['Email'], "subject": p_subject, "body": p_body}
                try:
                    requests.post(webhook_url, json=payload, timeout=10)
                    emails_sent += 1
                    jobs[job_id]['emails_sent'] = emails_sent
                    
                    # [DB] Update Email Sent Status & Personalization Line
                    db.send_action("update_email_sent", {"email": lead['Email'], "personalization_line": p_line})
                    db.log("Email Sent", f"Sent to {lead['Email']}")
                except Exception as e:
                    print(f"Failed to send email to {lead['Email']}: {e}")
                
                if emails_sent < jobs[job_id]['total_to_send']:
                    delay = random.randint(60, 120)
                    for i in range(delay, 0, -1):
                        jobs[job_id]['status_text'] = f"Anti-Spam: Waiting {i}s before sending next email..."
                        time.sleep(1)
        
        # --- FINISHED ---
        jobs[job_id]['status'] = 'done'
        jobs[job_id]['status_text'] = 'Process Completed Successfully!'
        db.log("Job Complete", "All tasks finished successfully.")
        
    except Exception as e:
        jobs[job_id] = {'status': 'error', 'error': str(e)}
        if 'db' in locals(): db.log("Error", str(e))

# ══════════════════════════════════════════════
#   FLASK DASHBOARD & API
# ══════════════════════════════════════════════
flask_app = Flask(__name__)
jobs = {}

HTML_TEMPLATE = r"""<!DOCTYPE html>
<html lang="en">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>LeadGen Pro | Auto Emailer & DB</title>
<script src="https://cdn.tailwindcss.com"></script>
<link rel="stylesheet" href="https://cdnjs.cloudflare.com/ajax/libs/font-awesome/6.5.0/css/all.min.css">
<style>
*{box-sizing:border-box}
body{background:#060b18;color:#cbd5e1;font-family:'Inter',system-ui,sans-serif;min-height:100vh}
.card{background:rgba(15,23,42,0.85);border:1px solid rgba(99,102,241,0.12);border-radius:16px}
.card-hover{transition:all .2s}
.card-hover:hover{border-color:rgba(99,102,241,0.35);transform:translateY(-2px)}
.btn-p{background:linear-gradient(135deg,#4f46e5,#7c3aed);color:#fff;font-weight:600;cursor:pointer;transition:all .2s;border:none}
.btn-p:hover{filter:brightness(1.12);transform:translateY(-1px);box-shadow:0 6px 20px rgba(79,70,229,0.4)}
.btn-p:disabled{opacity:.45;cursor:not-allowed;transform:none;filter:none}
.btn-g{background:linear-gradient(135deg,#059669,#0d9488);color:#fff;font-weight:600;cursor:pointer;transition:all .2s;border:none}
.btn-g:hover{filter:brightness(1.12);transform:translateY(-1px);box-shadow:0 6px 20px rgba(5,150,105,0.4)}
.btn-b{background:linear-gradient(135deg,#2563eb,#3b82f6);color:#fff;font-weight:600;cursor:pointer;transition:all .2s;border:none}
.btn-b:hover{filter:brightness(1.12);transform:translateY(-1px);box-shadow:0 6px 20px rgba(37,99,235,0.4)}
.inp{background:#0f172a;border:1px solid #1e293b;color:#e2e8f0;border-radius:10px;padding:11px 15px;font-size:13px;width:100%;transition:border .2s;outline:none}
.inp:focus{border-color:#4f46e5;box-shadow:0 0 0 3px rgba(79,70,229,0.12)}
.tab{border-radius:9px;padding:9px 18px;font-size:12px;font-weight:600;cursor:pointer;transition:all .2s;border:1px solid transparent;color:#64748b;background:transparent}
.tab.on{background:linear-gradient(135deg,#4f46e5,#7c3aed);color:#fff;box-shadow:0 3px 12px rgba(79,70,229,0.35)}
.tab:not(.on):hover{background:rgba(79,70,229,0.08);color:#a5b4fc}
.prog{height:4px;background:#1e293b;border-radius:99px;overflow:hidden}
.prog-fill{height:100%;border-radius:99px;background:linear-gradient(90deg,#4f46e5,#7c3aed);transition:width .6s ease}
.pill{padding:1px 7px;border-radius:6px;font-size:11px;font-weight:600;display:inline-block}
.pg{background:rgba(5,150,105,0.12);color:#34d399}
.pr{background:rgba(239,68,68,0.09);color:#f87171}
.pb{background:rgba(59,130,246,0.1);color:#60a5fa}
.spin{animation:spin 1s linear infinite}
@keyframes spin{to{transform:rotate(360deg)}}
.fade{animation:fd .25s ease}
@keyframes fd{from{opacity:0;transform:translateY(6px)}to{opacity:1;transform:translateY(0)}}
.blink{animation:bl 1.4s infinite}
@keyframes bl{0%,100%{opacity:1}50%{opacity:.25}}
::-webkit-scrollbar{width:6px}::-webkit-scrollbar-thumb{background:#334155;border-radius:3px}
</style>
</head>
<body>

<nav style="background:rgba(6,11,24,.96);border-bottom:1px solid rgba(99,102,241,0.1);backdrop-filter:blur(10px)" class="sticky top-0 z-40 px-4 py-3 flex items-center justify-between">
  <div class="flex items-center gap-3">
    <div class="btn-p w-9 h-9 rounded-xl flex items-center justify-center text-sm shadow-lg"><i class="fa-solid fa-bolt"></i></div>
    <div>
      <div class="font-bold text-white text-sm">LeadGen Pro <span class="text-indigo-400">Auto</span></div>
      <div class="text-xs text-slate-500">Scrape, Store & Send Personalized Emails</div>
    </div>
  </div>
</nav>

<div class="max-w-5xl mx-auto px-4 py-6">

  <!-- STATS -->
  <div class="grid grid-cols-2 md:grid-cols-4 gap-3 mb-6">
    <div class="card card-hover p-4 fade"><div class="text-2xl font-bold text-white" id="st">0</div><div class="text-xs text-slate-500 mt-1 flex items-center gap-1"><i class="fa-solid fa-users text-indigo-400 text-xs"></i>Valid Leads</div></div>
    <div class="card card-hover p-4 fade"><div class="text-2xl font-bold text-emerald-400" id="se">0</div><div class="text-xs text-slate-500 mt-1 flex items-center gap-1"><i class="fa-solid fa-envelope text-emerald-400 text-xs"></i>Emails Found</div></div>
    <div class="card card-hover p-4 fade"><div class="text-2xl font-bold text-sky-400" id="sp">0</div><div class="text-xs text-slate-500 mt-1 flex items-center gap-1"><i class="fa-solid fa-phone text-sky-400 text-xs"></i>Phones</div></div>
    <div class="card card-hover p-4 fade"><div class="text-2xl font-bold text-violet-400" id="sw">0</div><div class="text-xs text-slate-500 mt-1 flex items-center gap-1"><i class="fa-solid fa-globe text-violet-400 text-xs"></i>Websites</div></div>
  </div>

  <!-- TABS -->
  <div class="flex gap-2 mb-5 overflow-x-auto pb-1">
    <button class="tab on" id="tab-search" onclick="showTab('search')"><i class="fa-solid fa-search mr-1.5"></i>Search & Run</button>
    <button class="tab" id="tab-database" onclick="showTab('database')"><i class="fa-solid fa-database mr-1.5"></i>Connect Database</button>
    <button class="tab" id="tab-connect" onclick="showTab('connect')"><i class="fa-solid fa-paper-plane mr-1.5"></i>Connect Email</button>
    <button class="tab" id="tab-templates" onclick="showTab('templates')"><i class="fa-solid fa-envelope-open-text mr-1.5"></i>Templates</button>
    <button class="tab" id="tab-history" onclick="showTab('history')"><i class="fa-solid fa-history mr-1.5"></i>History</button>
  </div>

  <!-- SEARCH PANE -->
  <div id="pane-search" class="fade">
    <div class="card p-6 mb-4">
      <h2 class="font-bold text-white text-sm mb-5 flex items-center gap-2">
        <span class="btn-p w-7 h-7 rounded-lg flex items-center justify-center text-xs"><i class="fa-solid fa-crosshairs"></i></span>
        Target Parameters
      </h2>
      <div class="grid grid-cols-1 sm:grid-cols-2 gap-4 mb-5">
        <div><label class="text-xs text-slate-500 mb-1.5 block">📍 Location *</label><input id="m-loc" class="inp" placeholder="e.g. New York"></div>
        <div><label class="text-xs text-slate-500 mb-1.5 block">🔍 Keyword *</label><input id="m-kw" class="inp" placeholder="e.g. dentist"></div>
        <div><label class="text-xs text-slate-500 mb-1.5 block">🔢 Exact Target (Max 200)</label><input id="m-count" type="number" max="200" value="10" class="inp"></div>
        <div><label class="text-xs text-slate-500 mb-1.5 block">⭐ Max Rating (Optional - For Bad Reviews)</label><input id="m-rating" type="number" step="0.1" class="inp" placeholder="e.g. 3.5"></div>
      </div>
      <div class="p-3 mb-4 rounded-xl text-xs" style="background:rgba(239,68,68,0.07);border:1px solid rgba(239,68,68,0.2);color:#f87171">
        <i class="fa-solid fa-shield-halved mr-1"></i> <b>Strict Mode:</b> Only leads with valid emails are counted. AI will auto-expand keywords until target is reached.
      </div>
      <button onclick="startJob()" id="btn-run" class="btn-p w-full py-3 rounded-xl text-sm"><i class="fa-solid fa-play mr-2"></i>Start Scraping & Automation</button>
    </div>

    <!-- STATUS -->
    <div id="sbox" class="hidden card p-5 mb-4 fade">
      <div class="flex items-center gap-3 mb-3">
        <i id="si" class="fa-solid fa-circle-notch spin text-indigo-400 text-xl"></i>
        <span id="stxt" class="font-semibold text-white text-sm">Processing...</span>
      </div>
      <div class="prog mb-2"><div class="prog-fill" id="sbar" style="width:0%"></div></div>
      <div id="sdet" class="text-xs text-slate-400 mb-3 font-mono bg-slate-900 p-2 rounded"></div>
      <button id="dlbtn" onclick="doDL()" class="hidden btn-g w-full py-3 rounded-xl text-sm"><i class="fa-solid fa-download mr-2"></i>Download Leads CSV</button>
    </div>

    <!-- PREVIEW TABLE -->
    <div id="pvbox" class="hidden card p-5 fade">
      <div class="flex items-center justify-between mb-4">
        <h3 class="font-bold text-white text-sm flex items-center gap-2">
          <i class="fa-solid fa-table-cells text-indigo-400 text-xs"></i>
          Preview <span id="pvcnt" class="text-slate-500 font-normal text-xs"></span>
        </h3>
        <button onclick="doDL()" class="btn-g px-4 py-2 rounded-lg text-xs">
          <i class="fa-solid fa-download mr-1"></i>CSV
        </button>
      </div>
      <div class="overflow-x-auto">
        <table class="w-full text-xs border-collapse">
          <thead><tr id="th" class="text-slate-500"></tr></thead>
          <tbody id="tb"></tbody>
        </table>
      </div>
    </div>
  </div>

  <!-- [NEW] DATABASE PANE -->
  <div id="pane-database" class="hidden fade">
    <div class="card p-6">
      <h2 class="font-bold text-white text-sm mb-4"><i class="fa-solid fa-database text-blue-400 mr-2"></i>Connect Google Sheets Database</h2>
      <p class="text-xs text-slate-400 mb-4 leading-relaxed">
        Store all generated keywords, scraped businesses, emails, and logs automatically in Google Sheets.<br>
        1. Go to <a href="https://script.google.com" target="_blank" class="text-blue-400 underline">script.google.com</a> and create a New Project.<br>
        2. Copy and paste the script below.<br>
        3. Click <b>Deploy > New Deployment</b>. Select type <b>Web app</b>.<br>
        4. Set "Who has access" to <b>Anyone</b>. Click Deploy and copy the Web App URL.
      </p>
      
      <div class="relative mb-5">
        <button onclick="copyScript()" class="absolute top-2 right-2 bg-slate-800 hover:bg-slate-700 text-white text-xs py-1 px-3 rounded border border-slate-600 transition-colors z-10">Copy Script</button>
        <textarea id="db-script-code" readonly class="inp font-mono text-xs h-48" style="color:#93c5fd">
function doPost(e) {
  var lock = LockService.getScriptLock();
  lock.tryLock(10000);
  try {
    var payload = JSON.parse(e.postData.contents);
    var action = payload.action;
    var data = payload.data;
    var ss = SpreadsheetApp.getActiveSpreadsheet();

    function getOrCreateSheet(name, headers) {
      var sheet = ss.getSheetByName(name);
      if (!sheet) {
        sheet = ss.insertSheet(name);
        sheet.appendRow(headers);
        sheet.getRange(1, 1, 1, headers.length).setFontWeight("bold");
      }
      return sheet;
    }

    if (action === "init") {
      getOrCreateSheet("Config", ["keyword_seed", "location", "target_leads", "min_rating", "max_rating", "email_required", "status"]);
      getOrCreateSheet("Generated_Keywords", ["keyword", "source_seed", "status"]);
      getOrCreateSheet("Scraped_Businesses", ["business_name", "address", "phone", "rating", "review_count", "website", "keyword", "status"]);
      getOrCreateSheet("Email_Leads", ["business_name", "website", "email", "source_page", "status"]);
      getOrCreateSheet("Qualified_Leads", ["business_name", "email", "website", "rating", "keyword", "personalization_line", "email_sent"]);
      getOrCreateSheet("Logs", ["timestamp", "action", "details"]);
      return ContentService.createTextOutput(JSON.stringify({status: "success"})).setMimeType(ContentService.MimeType.JSON);
    }

    if (action === "log") {
      var sheet = ss.getSheetByName("Logs");
      if(sheet) sheet.appendRow([data.timestamp, data.action, data.details]);
    }
    else if (action === "add_keyword") {
      var sheet = ss.getSheetByName("Generated_Keywords");
      if(sheet) sheet.appendRow([data.keyword, data.source_seed, data.status]);
    }
    else if (action === "add_scraped") {
      var sheet = ss.getSheetByName("Scraped_Businesses");
      if(sheet) sheet.appendRow([data.business_name, data.address, data.phone, data.rating, data.review_count, data.website, data.keyword, data.status]);
    }
    else if (action === "add_email_lead") {
      var sheet = ss.getSheetByName("Email_Leads");
      if(sheet) sheet.appendRow([data.business_name, data.website, data.email, data.source_page, data.status]);
    }
    else if (action === "add_qualified") {
      var sheet = ss.getSheetByName("Qualified_Leads");
      if(sheet) sheet.appendRow([data.business_name, data.email, data.website, data.rating, data.keyword, data.personalization_line, data.email_sent]);
    }
    else if (action === "update_config") {
       var sheet = ss.getSheetByName("Config");
       if(sheet) {
         sheet.clearContents();
         sheet.appendRow(["keyword_seed", "location", "target_leads", "min_rating", "max_rating", "email_required", "status"]);
         sheet.appendRow([data.keyword_seed, data.location, data.target_leads, data.min_rating, data.max_rating, data.email_required, data.status]);
       }
    }
    else if (action === "update_email_sent") {
       var sheet = ss.getSheetByName("Qualified_Leads");
       if(sheet) {
         var dataRange = sheet.getDataRange();
         var values = dataRange.getValues();
         for (var i = 1; i < values.length; i++) {
           if (values[i][1] === data.email) { 
             sheet.getRange(i + 1, 6).setValue(data.personalization_line);
             sheet.getRange(i + 1, 7).setValue("yes");
             break;
           }
         }
       }
    }
    return ContentService.createTextOutput(JSON.stringify({status: "success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(e) {
    return ContentService.createTextOutput(JSON.stringify({status: "error", message: e.toString()})).setMimeType(ContentService.MimeType.JSON);
  } finally {
    lock.releaseLock();
  }
}
function doGet(e) {
  return ContentService.createTextOutput(JSON.stringify({status: "active", message: "Database Connected"})).setMimeType(ContentService.MimeType.JSON);
}</textarea>
      </div>
      
      <label class="text-xs text-slate-500 mb-1.5 block">🔗 Paste Database Web App URL Here:</label>
      <input id="db-webhook-url" class="inp mb-4" placeholder="https://script.google.com/macros/s/AKfycb.../exec">
      <button onclick="saveDBWebhook()" class="btn-b w-full py-2.5 rounded-xl text-sm"><i class="fa-solid fa-link mr-2"></i>Connect Database</button>
    </div>
  </div>

  <!-- CONNECT EMAIL PANE -->
  <div id="pane-connect" class="hidden fade">
    <div class="card p-6">
      <h2 class="font-bold text-white text-sm mb-4"><i class="fa-solid fa-paper-plane text-emerald-400 mr-2"></i>Google Apps Script Setup (Email Sender)</h2>
      <p class="text-xs text-slate-400 mb-4 leading-relaxed">To send emails automatically from your Gmail, follow these steps:<br>1. Go to <a href="https://script.google.com" target="_blank" class="text-emerald-400 underline">script.google.com</a> and create a New Project.<br>2. Paste the code below.<br>3. Click <b>Deploy > New Deployment</b>. Select type <b>Web app</b>.<br>4. Set "Who has access" to <b>Anyone</b>. Click Deploy and copy the Web App URL.</p>
      
      <div class="relative mb-5">
        <textarea readonly class="inp font-mono text-xs h-32" style="color:#a5b4fc">
function doPost(e) {
  try {
    var data = JSON.parse(e.postData.contents);
    MailApp.sendEmail({
      to: data.to,
      subject: data.subject,
      htmlBody: data.body
    });
    return ContentService.createTextOutput(JSON.stringify({"status": "success"})).setMimeType(ContentService.MimeType.JSON);
  } catch(err) {
    return ContentService.createTextOutput(JSON.stringify({"status": "error", "message": err.toString()})).setMimeType(ContentService.MimeType.JSON);
  }
}</textarea>
      </div>
      
      <label class="text-xs text-slate-500 mb-1.5 block">🔗 Paste Email Web App URL Here:</label>
      <input id="webhook-url" class="inp mb-4" placeholder="https://script.google.com/macros/s/AKfycb.../exec">
      <button onclick="saveWebhook()" class="btn-g w-full py-2.5 rounded-xl text-sm"><i class="fa-solid fa-save mr-2"></i>Save Email Connection</button>
    </div>
  </div>

  <!-- TEMPLATES PANE -->
  <div id="pane-templates" class="hidden fade">
    <div class="card p-6 mb-4">
      <h2 class="font-bold text-white text-sm mb-4"><i class="fa-solid fa-plus text-indigo-400 mr-2"></i>Add New Template</h2>
      <input id="t-name" class="inp mb-3" placeholder="Template Name (e.g. SEO Pitch)">
      <input id="t-sub" class="inp mb-3" placeholder="Subject (AI will personalize this)">
      <textarea id="t-body" class="inp mb-3 h-24" placeholder="Email Body (HTML allowed. AI will personalize this based on lead info)"></textarea>
      <button onclick="addTemplate()" class="btn-p w-full py-2.5 rounded-xl text-sm"><i class="fa-solid fa-plus mr-2"></i>Add Template</button>
    </div>
    <div class="card p-6">
      <h2 class="font-bold text-white text-sm mb-4"><i class="fa-solid fa-list text-indigo-400 mr-2"></i>Saved Templates</h2>
      <div id="t-list" class="space-y-3"></div>
    </div>
  </div>

  <!-- HISTORY PANE -->
  <div id="pane-history" class="hidden fade">
    <div class="card p-6">
      <div class="flex justify-between items-center mb-4">
        <h2 class="font-bold text-white text-sm"><i class="fa-solid fa-history text-indigo-400 mr-2"></i>Task History</h2>
        <button onclick="clearHistory()" class="text-xs text-red-400"><i class="fa-solid fa-trash"></i> Clear</button>
      </div>
      <div id="h-list" class="space-y-3"></div>
    </div>
  </div>

</div>

<script>
let jid=null, templates=[], historyData=[], tableShown=false;

window.onload=()=>{
  document.getElementById('webhook-url').value = localStorage.getItem('webhook_url') || '';
  document.getElementById('db-webhook-url').value = localStorage.getItem('db_webhook_url') || '';
  templates = JSON.parse(localStorage.getItem('templates') || '[]');
  historyData = JSON.parse(localStorage.getItem('history') || '[]');
  renderTemplates();
  renderHistory();
};

function showTab(t){
  ['search','database','connect','templates','history'].forEach(x=>{
    document.getElementById('pane-'+x).classList.add('hidden');
    document.getElementById('tab-'+x).classList.remove('on');
  });
  document.getElementById('pane-'+t).classList.remove('hidden');
  document.getElementById('tab-'+t).classList.add('on');
}

function copyScript() {
  const code = document.getElementById('db-script-code');
  code.select();
  document.execCommand('copy');
  alert("Database Script Copied!");
}

function saveWebhook(){
  localStorage.setItem('webhook_url', document.getElementById('webhook-url').value.trim());
  alert("Email Webhook Saved Successfully!");
}

function saveDBWebhook(){
  localStorage.setItem('db_webhook_url', document.getElementById('db-webhook-url').value.trim());
  alert("Database Webhook Saved Successfully!");
}

function addTemplate(){
  const n = document.getElementById('t-name').value.trim();
  const s = document.getElementById('t-sub').value.trim();
  const b = document.getElementById('t-body').value.trim();
  if(!n || !s || !b) return alert("Fill all fields!");
  templates.push({name: n, subject: s, body: b});
  localStorage.setItem('templates', JSON.stringify(templates));
  document.getElementById('t-name').value=''; document.getElementById('t-sub').value=''; document.getElementById('t-body').value='';
  renderTemplates();
}

function delTemplate(i){ templates.splice(i,1); localStorage.setItem('templates', JSON.stringify(templates)); renderTemplates(); }

function renderTemplates(){
  const el = document.getElementById('t-list');
  if(!templates.length) return el.innerHTML = '<div class="text-xs text-slate-500 text-center">No templates added.</div>';
  el.innerHTML = templates.map((t,i)=>`
    <div class="p-4 rounded-xl bg-slate-800/50 border border-slate-700 relative">
      <button onclick="delTemplate(${i})" class="absolute top-3 right-3 text-red-400 hover:text-red-300"><i class="fa-solid fa-trash"></i></button>
      <div class="font-bold text-sm text-white mb-1">${t.name}</div>
      <div class="text-xs text-indigo-300 mb-2">Sub: ${t.subject}</div>
      <div class="text-xs text-slate-400 line-clamp-2">${t.body.replace(/</g,'&lt;')}</div>
    </div>`).join('');
}

function renderHistory(){
  const el = document.getElementById('h-list');
  if(!historyData.length) return el.innerHTML = '<div class="text-xs text-slate-500 text-center">No history.</div>';
  el.innerHTML = historyData.map(h=>`
    <div class="p-3 rounded-xl bg-slate-800/50 border border-slate-700">
      <div class="text-sm font-bold text-white">${h.loc} - ${h.kw}</div>
      <div class="text-xs text-slate-400 mt-1">Target: ${h.target} | Date: ${h.date}</div>
    </div>`).join('');
}
function clearHistory(){ historyData=[]; localStorage.removeItem('history'); renderHistory(); }

function setSt(msg, state='load', pct=null){
  document.getElementById('sbox').classList.remove('hidden');
  document.getElementById('sdet').textContent = msg;
  const ic = document.getElementById('si');
  const txt = document.getElementById('stxt');
  
  if(state==='load'){ ic.className='fa-solid fa-circle-notch spin text-indigo-400 text-xl'; txt.textContent='Scraping Engine Running...'; }
  else if(state==='email'){ ic.className='fa-solid fa-paper-plane blink text-sky-400 text-xl'; txt.textContent='Automation: Sending Emails...'; }
  else if(state==='done'){ ic.className='fa-solid fa-circle-check text-emerald-400 text-xl'; txt.textContent='Task Completed!'; }
  else { ic.className='fa-solid fa-circle-xmark text-red-400 text-xl'; txt.textContent='Error Occurred!'; }
  
  if(pct!=null) document.getElementById('sbar').style.width=pct+'%';
}

function updStats(leads){
  document.getElementById('st').textContent=leads.length;
  document.getElementById('se').textContent=leads.length; 
  document.getElementById('sp').textContent=leads.filter(l=>l.Phone&&l.Phone!='N/A').length;
  document.getElementById('sw').textContent=leads.filter(l=>l.Website&&l.Website!='N/A').length;
}

function showPV(leads){
  if(!leads || !leads.length) return;
  document.getElementById('pvbox').classList.remove('hidden');
  document.getElementById('pvcnt').textContent='('+leads.length+' total, top 10)';
  const keys=Object.keys(leads[0]);
  document.getElementById('th').innerHTML=keys.map(k=>`<th class="px-3 py-2 text-left text-slate-500 font-medium whitespace-nowrap" style="border-bottom:1px solid rgba(255,255,255,0.05)">${k}</th>`).join('');
  document.getElementById('tb').innerHTML=leads.slice(0,10).map(l=>
    `<tr style="border-bottom:1px solid rgba(255,255,255,0.04)">${keys.map(k=>{
      const v=(l[k]||'N/A').toString();
      const cls=v==='N/A'?'pr':k==='Email'?'pg':k==='Phone'?'pb':'';
      return `<td class="px-3 py-2.5 text-slate-300 max-w-xs whitespace-nowrap overflow-hidden text-ellipsis">${cls?`<span class="pill ${cls}">${v}</span>`:v}</td>`;
    }).join('')}</tr>`
  ).join('');
}

async function startJob(){
  const loc=document.getElementById('m-loc').value.trim();
  const kw=document.getElementById('m-kw').value.trim();
  let count=parseInt(document.getElementById('m-count').value)||10;
  if(count > 200) count = 200;
  
  if(!loc||!kw) return alert('Location & Keyword required!');
  
  const webhook = document.getElementById('webhook-url').value.trim();
  const db_webhook = document.getElementById('db-webhook-url').value.trim();
  
  if(!db_webhook) alert("Notice: Database Webhook is missing. Data will not be saved to Google Sheets.");
  if(!webhook && templates.length > 0) alert("Warning: Email Webhook URL is missing. Emails will NOT be sent.");
  if(webhook && templates.length === 0) alert("Warning: No templates added. Emails will NOT be sent.");

  setSt('Initializing AI Search Engine...','load',5);
  document.getElementById('dlbtn').classList.add('hidden');
  document.getElementById('pvbox').classList.add('hidden');
  document.getElementById('btn-run').disabled=true;
  tableShown = false;

  const payload = {
    location: loc, keyword: kw, max_leads: count,
    max_rating: document.getElementById('m-rating').value || null,
    webhook_url: webhook, db_webhook_url: db_webhook, templates: templates
  };

  try {
      const r = await fetch('/api/scrape',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload)});
      const d = await r.json();
      if(d.error){ setSt(d.error,'err'); document.getElementById('btn-run').disabled=false; return; }
      jid = d.job_id;

      historyData.unshift({loc: loc, kw: kw, target: count, date: new Date().toLocaleString()});
      localStorage.setItem('history', JSON.stringify(historyData)); renderHistory();

      const poll = async()=>{
        try {
            const r2 = await fetch('/api/status/'+jid); 
            const d2 = await r2.json();
            
            if(d2.status==='scraping'){
                setSt(d2.status_text, 'load', Math.max(5, (d2.count/count)*100));
                if(d2.leads && d2.leads.length > 0) {
                    updStats(d2.leads);
                    if(!tableShown) { showPV(d2.leads); tableShown=true; }
                }
                setTimeout(poll, 3000);
            }
            else if(d2.status==='sending_emails'){
                if(!tableShown && d2.leads) {
                    updStats(d2.leads); showPV(d2.leads); tableShown = true;
                }
                document.getElementById('dlbtn').classList.remove('hidden');
                let emailPct = d2.total_to_send > 0 ? (d2.emails_sent / d2.total_to_send) * 100 : 100;
                setSt(d2.status_text, 'email', Math.max(5, emailPct));
                setTimeout(poll, 3000);
            }
            else if(d2.status==='done'){
              document.getElementById('btn-run').disabled=false;
              if(d2.leads) { updStats(d2.leads); showPV(d2.leads); }
              setSt(d2.status_text, 'done', 100);
              document.getElementById('dlbtn').classList.remove('hidden');
            } 
            else if(d2.status==='error'){
              document.getElementById('btn-run').disabled=false;
              setSt(d2.error, 'err');
            }
            else {
              setTimeout(poll, 3000);
            }
        } catch(e) {
            setTimeout(poll, 3000);
        }
      };
      setTimeout(poll, 2000);
  } catch(e) {
      setSt('Failed to connect to server.','err');
      document.getElementById('btn-run').disabled=false;
  }
}

function doDL(){ if(jid) window.location='/api/download/'+jid; }
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
    if not job or job.get('status') not in ['done', 'sending_emails']: return "Not ready", 400
    leads = job.get('leads', [])
    if not leads: return "No leads found", 404
    
    out = io.StringIO()
    writer = csv.DictWriter(out, fieldnames=leads[0].keys())
    writer.writeheader()
    writer.writerows(leads)
    out.seek(0)
    return send_file(io.BytesIO(out.getvalue().encode('utf-8-sig')), mimetype='text/csv', as_attachment=True, download_name='Target_Leads.csv')

# ══════════════════════════════════════════════
#   TELEGRAM BOT
# ══════════════════════════════════════════════
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
    await update.message.reply_text("👋 *LeadGen Pro Bot*\n\n✅ Strict Valid Emails Only\n✅ Auto AI Keyword Expansion\n✅ Max Limit: 200\n\n_Note: For Email Automation, please use the Web Dashboard._", parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(kb))

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
    txt_summary = f"📋 *Target Guarantee*\n📍 Loc: {data['loc']}\n🔍 Kw: {data['kw']}\n🔢 Target: {data['count']} Valid Emails\n⭐ Max Rating: {data.get('rating') or 'None'}\n\nStart Scraping?"
    kb = [[InlineKeyboardButton("✅ Start", callback_data="start_scrape")]]
    await update.message.reply_text(txt_summary, parse_mode='Markdown', reply_markup=InlineKeyboardMarkup(kb))
    return ConversationHandler.END

def run_bot_scrape_fast(data):
    location = data['loc']
    base_keyword = data['kw']
    max_leads = data['count']
    max_rating = data.get('rating')
    
    maps_scraper = GoogleMapsScraper()
    email_lib = DeepEmailExtractor()
    
    seen_names = set()
    used_keywords = set()
    pending_keywords = [base_keyword]
    final_leads = []
    
    while len(final_leads) < max_leads:
        if not pending_keywords:
            new_kws = generate_ai_keywords(base_keyword, location, used_keywords)
            pending_keywords.extend(new_kws)
            
        current_kw = pending_keywords.pop(0)
        used_keywords.add(current_kw.lower())
        
        raw_leads = maps_scraper.fetch_batch(current_kw, location)
        
        for lead in raw_leads:
            if len(final_leads) >= max_leads: break
            if lead['Name'] in seen_names: continue
            
            if max_rating and lead['Rating'] != "N/A":
                try:
                    if float(lead['Rating']) > float(max_rating): continue
                except: pass
                
            if lead['Website'] == "N/A": continue
                
            extracted_email = email_lib.get_email(lead['Website'])
            if extracted_email == "N/A": continue
            
            lead['Email'] = extracted_email
            seen_names.add(lead['Name'])
            final_leads.append(lead)
            
    return final_leads

async def background_bot_task(chat_id, message_id, data, bot):
    try:
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="⏳ *Fast Scraping & Deep Email Extraction running...*\n_AI will auto-expand keywords until target is reached._", parse_mode='Markdown')
        
        loop = asyncio.get_event_loop()
        final_leads = await loop.run_in_executor(None, run_bot_scrape_fast, data)
        
        if not final_leads:
            await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="😔 No results found.")
            return

        path = to_csv(final_leads)
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text="✅ Done! Sending file...")
        with open(path, 'rb') as f:
            await bot.send_document(
                chat_id=chat_id, document=f, filename=f"Target_Leads.csv",
                caption=f"🎯 *Target Reached!*\n📊 Total Valid Emails: {len(final_leads)}", parse_mode='Markdown'
            )
        os.unlink(path)
    except Exception as e:
        await bot.edit_message_text(chat_id=chat_id, message_id=message_id, text=f"❌ Error: `{e}`", parse_mode='Markdown')

async def execute_scrape(update: Update, ctx: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    await q.answer()
    uid = q.from_user.id
    data = bot_store.get(uid)
    
    msg = await q.edit_message_text("⏳ *Initializing background task...*", parse_mode='Markdown')
    asyncio.create_task(background_bot_task(q.message.chat_id, msg.message_id, data, ctx.bot))

def run_telegram_bot():
    loop = asyncio.new_event_loop()
    asyncio.set_event_loop(loop)
    app = Application.builder().token(TELEGRAM_TOKEN).build()
    
    conv = ConversationHandler(
        entry_points=[CallbackQueryHandler(handle_mode, pattern="^start_manual$")],
        states={
            M_LOC: [MessageHandler(filters.TEXT & ~filters.COMMAND, m_loc)],
            M_KW: [MessageHandler(filters.TEXT & ~filters.COMMAND, m_kw)],
            M_COUNT: [MessageHandler(filters.TEXT & ~filters.COMMAND, m_count)],
            M_RATING: [MessageHandler(filters.TEXT & ~filters.COMMAND, m_rating)]
        },
        fallbacks=[],
        per_message=False,
    )
    app.add_handler(CommandHandler("start", start))
    app.add_handler(conv)
    app.add_handler(CallbackQueryHandler(execute_scrape, pattern="^start_scrape$"))
    
    app.run_polling(allowed_updates=Update.ALL_TYPES, drop_pending_updates=True)

if __name__ == "__main__":
    if TELEGRAM_TOKEN:
        threading.Thread(target=run_telegram_bot, daemon=True).start()
    port = int(os.environ.get("PORT", 10000))
    flask_app.run(host='0.0.0.0', port=port)

