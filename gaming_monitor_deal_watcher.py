#!/usr/bin/env python3
"""
Gaming Monitor Deal Watcher
Finds monitor deals that meet your rules and alerts you on Discord (and/or ntfy):
  - 27 inches or bigger
  - 120Hz or faster
  - QHD (1440p) or better (4K and ultrawide flagged)
  - HDR support
  - $215 or less
Every alert shows a 1-10 monitor score (resolution + refresh rate + size + ultrawide + price;
any 4K monitor at 160Hz+ is a 10).

Sources
  1. Best Buy official Products API (free key: https://developer.bestbuy.com)
  2. Slickdeals RSS searches (covers Amazon, Newegg, Walmart, Dell, Micro Center...)
     Only posts from the last 24 hours are kept, using the post's own timestamp.

A spec the title SHOWS that breaks a rule gets the listing skipped.
A spec the title doesn't mention can't be checked, so the alert lists it under
"Verify before buying". Every listing alerts ONCE (remembered in seen_monitor_deals.json).

Usage
  python gaming_monitor_deal_watcher.py             # runs forever
  python gaming_monitor_deal_watcher.py --once      # single check, then exit
  python gaming_monitor_deal_watcher.py --test      # send a sample alert
  python gaming_monitor_deal_watcher.py --backtest  # audit old + current listings (sends nothing)
  python gaming_monitor_deal_watcher.py --backtest --send   # same, and post matches to Discord

Settings (environment variables, all optional)
  MAX_PRICE=215  MAX_AGE_HOURS=24  CHECK_MINUTES=15
  BESTBUY_API_KEY=...  NTFY_TOPIC=...  DISCORD_WEBHOOK=...
"""
import html
import json
import os
import re
import sys
import time
import urllib.parse
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
from pathlib import Path

# ---- your rules
MAX_PRICE = float(os.getenv("MAX_PRICE", "215"))
MIN_PRICE = 60.0          # ignore tiny numbers like "$25 off" or accessories
MIN_INCHES = 27
MIN_HZ = 120
MAX_AGE_HOURS = float(os.getenv("MAX_AGE_HOURS", "24"))
CHECK_MINUTES = float(os.getenv("CHECK_MINUTES", "15"))
BESTBUY_API_KEY = os.getenv("BESTBUY_API_KEY", "")
NTFY_TOPIC = os.getenv("NTFY_TOPIC", "")
DISCORD_WEBHOOK = os.getenv("DISCORD_WEBHOOK", "")
STATE_FILE = Path(__file__).with_name("seen_monitor_deals.json")
STATE_KEEP_DAYS = 45
UA = {"User-Agent": "Mozilla/5.0 (compatible; GamingMonitorDealWatcher/1.0)"}

# ---- regexes
SIZE_RE = re.compile(r"(?<![\d.])(\d{2}(?:\.\d)?)\s?(?:\"|”|″|-?\s?in(?:ch(?:es)?)?\b)", re.I)
HZ_RE = re.compile(r"(?<![\d.])(\d{2,3})\s?-?\s?Hz\b", re.I)
RES_4K_RE = re.compile(r"\b4K\b|\bUHD\b|3840\s?[x×*]\s?2160|\b2160p\b|\b5K\b|5120\s?[x×*]\s?2880|\b8K\b", re.I)
RES_QHD_RE = re.compile(
    r"\bQHD\b|\bWQHD\b|\bUWQHD\b|\bDQHD\b|\bWQXGA\b|\b1440p\b|2560\s?[x×*]\s?1440|3440\s?[x×*]\s?1440|5120\s?[x×*]\s?1440", re.I)
RES_FHD_RE = re.compile(r"\bFHD\b|\bWFHD\b|\b1080p\b|1920\s?[x×*]\s?1080|2560\s?[x×*]\s?1080|Full\s?HD", re.I)
ULTRAWIDE_RE = re.compile(r"ultra-?wide|\bUWQHD\b|3440\s?[x×*]\s?1440|5120\s?[x×*]\s?1440|\b21:9\b|\b32:9\b", re.I)
HDR_RE = re.compile(r"\bHDR\b|HDR\s?10|DisplayHDR|HDR\s?(?:400|600|1000|1400)|Dolby Vision", re.I)
NO_HDR_RE = re.compile(r"\b(?:no|non|without)[- ]HDR\b", re.I)
PANEL_RES = [("OLED", re.compile(r"\bOLED\b", re.I), 10.0), ("Mini-LED", re.compile(r"mini[- ]?LED", re.I), 9.0),
             ("IPS", re.compile(r"\bIPS\b", re.I), 8.5), ("VA", re.compile(r"\bVA\b", re.I), 7.5),
             ("TN", re.compile(r"\bTN\b", re.I), 5.5)]
EXCLUDE_RE = re.compile(
    r"\bTVs?\b|television|projector|laptop|notebook|portable|travel|"
    r"\b(?:desk|wall|monitor|display)\s+(?:desk\s+)?(?:mount|arm|stand|riser)\b|\bmonitor arm\b|"
    r"\bcable\b|adapter|webcam|keyboard|\bmouse\b|headset|"
    r"\bRTX\b|Ryzen|Core i[3579]|Intel Core|prebuilt|gaming pc|\btower\b|graphics card",
    re.I,
)
MONITOR_RE = re.compile(
    r"monitor|\bdisplay\b|ultrawide|odyssey|ultragear|optix|rog swift|predator x|alienware aw|aorus|"
    r"\bxg\d{3}|\bvg\d{3}|\baw\d{4}", re.I)
REFURB_RE = re.compile(r"refurb|renewed|open[- ]box|\bused\b|recertified|certified", re.I)
INSTORE_ONLY_RE = re.compile(r"in[- ]store only|store pickup only|pickup only|in[- ]store pickup only|in[- ]store exclusive", re.I)
FREE_SHIP_RE = re.compile(r"free (?:shipping|s/h|delivery)|ships free", re.I)
PRICE_RE = re.compile(r"\$\s?(\d{1,3}(?:,\d{3})+(?:\.\d{2})?|\d+(?:\.\d{2})?)")
EXPIRED_RE = re.compile(r"this deal has expired|deal has expired|expired deal", re.I)

SLICKDEALS_QUERIES = [
    "gaming monitor 1440p", "gaming monitor 4k", "qhd gaming monitor", "4k 144hz monitor",
    "27 inch 165hz monitor", "27 inch 144hz monitor", "27 inch 180hz monitor", "240hz monitor",
    "32 inch 4k monitor", "32 inch 1440p monitor", "curved gaming monitor",
    "ultrawide gaming monitor", "34 inch ultrawide monitor",
]
BESTBUY_KEYWORDS = ["1440p", "qhd", "4k", "uhd", "144hz", "165hz", "180hz", "240hz", "ultrawide", "27", "32", "34"]


def http_get(url, timeout=20):
    req = urllib.request.Request(url, headers=UA)
    with urllib.request.urlopen(req, timeout=timeout) as r:
        return r.read()


# ------------------------------------------------------------ title parsing
def first_price(text):
    """Selling price from a deal title. Skips '$20 off' / 'save $30' / gift-card amounts,
    ignores numbers under MIN_PRICE, and takes the lowest left ('$129 (was $229)' -> 129)."""
    prices = []
    for m in PRICE_RE.finditer(text):
        after = text[m.end():m.end() + 14].lower()
        before = text[max(0, m.start() - 14):m.start()].lower()
        if re.match(r"\s*(\+\s*)?(off|savings|rebate|gift|credit|back|cash ?back|discount|coupon|shipping)", after):
            continue
        if re.search(r"(save|saving|savings|extra|up to|take|get|minus|w/|with|off)\s*$", before):
            continue
        val = float(m.group(1).replace(",", ""))
        if val >= MIN_PRICE:
            prices.append(val)
    return min(prices) if prices else None


def parse_size(t):
    for m in SIZE_RE.finditer(t):
        v = float(m.group(1))
        if 17 <= v <= 60:
            return v
    return None


def parse_hz(t):
    vals = [int(m.group(1)) for m in HZ_RE.finditer(t) if 24 <= int(m.group(1)) <= 540]
    return max(vals) if vals else None


def parse_res(t):
    """'4K', 'QHD', 'FHD' or None."""
    if RES_4K_RE.search(t):
        return "4K"
    if RES_QHD_RE.search(t):
        return "QHD"
    if RES_FHD_RE.search(t):
        return "FHD"
    return None


def parse_panel(t):
    for name, rx, score in PANEL_RES:
        if rx.search(t):
            return name, score
    return None


def parse_hdr(t):
    """None = HDR not mentioned. ('NO', 0) = title says no HDR. Otherwise (label, score)."""
    if NO_HDR_RE.search(t):
        return ("NO", 0.0)
    if not HDR_RE.search(t):
        return None
    for level, sc in ((1400, 10.0), (1000, 10.0), (600, 9.0), (400, 7.5)):
        if re.search(rf"HDR\s?{level}\b", t, re.I):
            return (f"DisplayHDR {level}", sc)
    return ("HDR", 5.5)   # HDR named without a certified level: usually basic HDR support


def age_text(posted):
    if not posted:
        return ""
    mins = int((datetime.now(timezone.utc) - posted).total_seconds() // 60)
    return f"posted {mins} min ago" if mins < 90 else f"posted {mins // 60}h ago"


def looks_like_match(title):
    """A monitor (not a TV, mount, PC bundle...) with at least some monitor evidence."""
    if EXCLUDE_RE.search(title):
        return False
    if MONITOR_RE.search(title):
        return True
    return sum(x is not None for x in (parse_size(title), parse_hz(title), parse_res(title))) >= 2


def check_requirements(t):
    """Returns (fails, unknown): rules the title breaks, and rules it doesn't let us check."""
    fails, unknown = [], []
    size, hz, res = parse_size(t), parse_hz(t), parse_res(t)
    if size is None:
        unknown.append(f'screen size (needs {MIN_INCHES}"+)')
    elif size < MIN_INCHES:
        fails.append(f'{size:g}" screen')
    if hz is None:
        unknown.append(f"refresh rate (needs {MIN_HZ}Hz+)")
    elif hz < MIN_HZ:
        fails.append(f"{hz}Hz")
    if res is None:
        unknown.append("resolution (needs QHD+)")
    elif res == "FHD":
        fails.append("1080p resolution")
    hdr = parse_hdr(t)
    if hdr and hdr[0] == "NO":
        fails.append("no HDR")
    elif hdr is None:
        unknown.append("HDR support (needs HDR)")
    if not parse_panel(t):
        unknown.append("panel type (IPS/VA/OLED)")
    return fails, unknown


# ------------------------------------------------------------------ scoring
def rate_monitor(title, price=None):
    """1-10 score from resolution, refresh rate, size, ultrawide and PRICE.
    Special rule: any 4K monitor at 160Hz or higher is a 10/10."""
    size, hz, res = parse_size(title), parse_hz(title), parse_res(title)
    hdr = parse_hdr(title)
    ultra = bool(ULTRAWIDE_RE.search(title))
    # resolution: 4K only edges out 1440p (it isn't a big boost on its own)
    res_s = {"4K": 9.0, "QHD": 8.0}.get(res, 5.0)                 # unknown -> can't confirm the main rule
    if res == "4K" and re.search(r"\b5K\b|\b8K\b|5120\s?[x×*]\s?2880", title, re.I):
        res_s = 10.0
    # refresh rate
    if hz is None:
        hz_s = 5.0
    else:
        hz_s = next(sc for lim, sc in ((360, 10), (240, 9.5), (180, 8.5), (165, 8.0), (144, 7.0), (120, 6.0), (0, 2.0)) if hz >= lim)
    # screen size and ultrawide shape (ultrawide is a bonus, never required)
    size_s = 6.0 if size is None else 10.0 if size >= 34 else 8.5 if size >= 31 else 7.5 if size >= 28 else 7.0
    wide_s = 10.0 if ultra else 7.0
    # price: $100 or less = 10, sliding to 6 at the $215 cap
    if price is None:
        value_s = 7.0
    elif price <= 100:
        value_s = 10.0
    else:
        value_s = max(5.0, 10.0 - (price - 100) * (4.0 / (MAX_PRICE - 100)))
    score = 0.30 * res_s + 0.30 * hz_s + 0.15 * size_s + 0.10 * wide_s + 0.15 * value_s
    perfect = res == "4K" and hz is not None and hz >= 160
    score = 10.0 if perfect else round(min(10.0, score), 1)
    panel = parse_panel(title)
    found = []
    if size:
        found.append(f'{size:g}"')
    if res:
        found.append({"4K": "4K UHD", "QHD": "QHD / 1440p"}.get(res, res))
    if hz:
        found.append(f"{hz}Hz")
    if panel:
        found.append(panel[0])
    if hdr and hdr[0] != "NO":
        found.append(hdr[0])
    if ultra:
        found.append("ultrawide")
    return {"score": score, "parts": {"res": res_s, "hz": hz_s, "size": size_s, "wide": wide_s, "price": value_s},
            "found": found, "is4k": res == "4K", "ultra": ultra, "perfect": perfect, "hdr_basic": bool(hdr and hdr[0] == "HDR")}


def rating_lines(r):
    p = r["parts"]
    lines = [f"**Monitor score: {r['score']}/10**" + (" 🏆 4K at 160Hz+ = perfect" if r["perfect"] else "") +
             f"  (resolution {p['res']:.1f} · refresh {p['hz']:.1f} · size {p['size']:.1f} · "
             f"ultrawide {p['wide']:.1f} · price {p['price']:.1f})"]
    if r["found"]:
        lines.append("Specs read from title: " + ", ".join(r["found"]))
    if r.get("hdr_basic"):
        lines.append("ℹ️ HDR is listed without a DisplayHDR level, which often means basic HDR support. DisplayHDR 400+ is the real minimum.")
    lines.append("(Score weighs resolution, refresh rate, size, ultrawide and price. Any 4K at 160Hz+ is a 10. "
                 "Unlisted resolution or refresh scores low. It doesn't measure brand quality or color accuracy.)")
    return lines


# ---------------------------------------------------------------- Best Buy
def fetch_bestbuy():
    if not BESTBUY_API_KEY:
        return []
    deals, skipped_ship = [], 0
    for kw in BESTBUY_KEYWORDS:
        q = f"(search=gaming&search=monitor&search={kw}&salePrice<={MAX_PRICE:.0f}&onlineAvailability=true)"
        url = ("https://api.bestbuy.com/v1/products" + urllib.parse.quote(q, safe="=&()<>") + "?" +
               urllib.parse.urlencode({"apiKey": BESTBUY_API_KEY, "format": "json",
                                       "show": "sku,name,salePrice,regularPrice,url,homeDelivery,orderable,freeShipping,shippingCost",
                                       "pageSize": 50}))
        try:
            data = json.loads(http_get(url))
        except Exception as e:
            print(f"[Best Buy] '{kw}' lookup failed: {e}")
            continue
        for p in data.get("products", []):
            if p.get("homeDelivery") is False or p.get("orderable") not in (None, "Available"):
                skipped_ship += 1
                continue
            if p.get("freeShipping"):
                ship = "🚚 Ships to you - FREE shipping"
            elif p.get("shippingCost") is not None:
                ship = f"🚚 Ships to you - shipping ${float(p['shippingCost']):,.0f}"
            else:
                ship = "🚚 Ships to you"
            deals.append({"id": f"bby-{p['sku']}", "source": "Best Buy", "title": p["name"],
                          "price": p["salePrice"], "was": p.get("regularPrice"), "url": p["url"],
                          "posted": None, "ship": ship, "rank": 0})
        time.sleep(0.3)
    print(f"[Best Buy] {len(deals)} shippable listings kept, {skipped_ship} dropped (no home delivery / not orderable)")
    return deals


# -------------------------------------------------------------- Slickdeals
def fetch_slickdeals(max_age_hours=MAX_AGE_HOURS, keep_unpriced=False):
    deals, now = [], datetime.now(timezone.utc)
    for q in SLICKDEALS_QUERIES:
        url = "https://slickdeals.net/newsearch.php?" + urllib.parse.urlencode({"q": q, "searchin": "first", "rss": "1"})
        try:
            root = ET.fromstring(http_get(url))
        except Exception as e:
            print(f"[Slickdeals] '{q}' failed: {e}")
            continue
        for item in root.iter("item"):
            title = (item.findtext("title") or "").strip()
            link = (item.findtext("link") or "").strip()
            price, price_note = first_price(title), None
            if price is None:
                desc = re.sub(r"<[^>]+>", " ", html.unescape(item.findtext("description") or ""))
                m = re.search(r"(?:on sale for|sale price|priced at|now|for|only)[:\s]*\$\s?(\d{1,3}(?:,\d{3})+(?:\.\d{2})?|\d+(?:\.\d{2})?)", desc, re.I)
                if m:
                    price = float(m.group(1).replace(",", ""))
                    price_note = "💲 Price taken from the post text, not the title - confirm it on the page"
            if price is None and not keep_unpriced:
                continue
            try:
                posted = parsedate_to_datetime(item.findtext("pubDate") or "")
                if posted.tzinfo is None:
                    posted = posted.replace(tzinfo=timezone.utc)
            except Exception:
                if max_age_hours is not None:
                    continue
                posted = None
            if max_age_hours is not None and not (0 <= (now - posted).total_seconds() <= max_age_hours * 3600):
                continue
            if INSTORE_ONLY_RE.search(title):
                continue
            m = re.search(r"/f/(\d+)", link)
            free = bool(FREE_SHIP_RE.search(title))
            deals.append({"id": "sd-" + (m.group(1) if m else (item.findtext("guid") or link)),
                          "source": "Slickdeals", "title": title, "price": price, "was": None,
                          "url": link, "posted": posted, "note": price_note,
                          "ship": "🚚 Free shipping (per post title)" if free else "🚚 Shipping not confirmed - check the page",
                          "rank": 1 if free else 2})
        time.sleep(0.5)
    return deals


def slickdeals_expired(url):
    try:
        page = http_get(url, timeout=15).decode("utf-8", "ignore")
    except Exception:
        return False
    return bool(EXPIRED_RE.search(page))


# ------------------------------------------------------------------- core
def load_state():
    try:
        state = json.loads(STATE_FILE.read_text())
    except Exception:
        return {}
    now = time.time()
    for v in state.values():
        v.setdefault("t", now)
    return {k: v for k, v in state.items() if now - v["t"] < STATE_KEEP_DAYS * 86400}


def save_state(state):
    STATE_FILE.write_text(json.dumps(state, indent=2))


def notify(deal):
    was = f" (was ${deal['was']:,.0f})" if deal.get("was") else ""
    r = deal.get("rating")
    lines = [f"[{deal['source']}] ${deal['price']:,.0f}{was}", deal["title"]]
    if deal.get("prefix"):
        lines.insert(0, deal["prefix"])
    if r and r["is4k"]:
        lines.insert(1 if deal.get("prefix") else 0, "🌟 **4K MONITOR** 🌟")
    if r and r["ultra"]:
        lines.insert(1 if deal.get("prefix") else 0, "↔️ **ULTRAWIDE** ↔️")
    if deal.get("ship"):
        lines.append(deal["ship"])
    if REFURB_RE.search(deal["title"]):
        lines.append("♻️ Refurbished / open-box - check the warranty and return policy")
    if deal.get("posted"):
        lines.append(age_text(deal["posted"]) + " - may sell out or end soon")
    if r:
        lines += rating_lines(r)
    if deal.get("verify"):
        lines.append("🔎 Verify before buying: " + ", ".join(deal["verify"]))
    if deal.get("note"):
        lines.append(deal["note"])
    lines.append(deal["url"])
    msg = "\n".join(lines)[:1900]
    print("\n🖥️ NEW DEAL\n" + msg + "\n")
    if NTFY_TOPIC:
        try:
            req = urllib.request.Request(f"https://ntfy.sh/{NTFY_TOPIC}", data=msg.encode("utf-8"),
                                         headers={"Title": "Monitor deal", "Click": deal["url"], **UA})
            urllib.request.urlopen(req, timeout=15)
        except Exception as e:
            print(f"[ntfy] failed: {e}")
    if DISCORD_WEBHOOK:
        try:
            req = urllib.request.Request(DISCORD_WEBHOOK, data=json.dumps({"content": msg}).encode("utf-8"),
                                         headers={"Content-Type": "application/json", **UA})
            urllib.request.urlopen(req, timeout=15)
        except Exception as e:
            print(f"[Discord] failed: {e}")


def evaluate(title, price):
    """Same checks a live run applies. Returns (would_alert, reason, verify_list)."""
    if not looks_like_match(title):
        return False, "not a qualifying monitor", []
    if price is None:
        return False, "no price found in title or post text", []
    if price > MAX_PRICE or price < MIN_PRICE:
        return False, f"price ${price:,.0f} outside ${MIN_PRICE:,.0f}-${MAX_PRICE:,.0f}", []
    fails, unknown = check_requirements(title)
    if fails:
        return False, "broke a rule: " + ", ".join(fails), unknown
    return True, "meets your rules", unknown


def check_once():
    state = load_state()
    candidates = fetch_bestbuy() + fetch_slickdeals()
    # confirmed shipping first; highest score first within that
    candidates.sort(key=lambda d: (d.get("rank", 2), -rate_monitor(d["title"], d.get("price"))["score"]))
    seen_this_run, new = set(), 0
    drops = {"not a qualifying monitor": 0, "price outside range": 0, "broke a rule": 0}
    for d in candidates:
        if d["id"] in seen_this_run:
            continue
        seen_this_run.add(d["id"])
        if not looks_like_match(d["title"]):
            drops["not a qualifying monitor"] += 1
            continue
        if d["price"] is None or d["price"] > MAX_PRICE or d["price"] < MIN_PRICE:
            drops["price outside range"] += 1
            continue
        if d["id"] in state:
            continue
        fails, unknown = check_requirements(d["title"])
        if fails:
            drops["broke a rule"] += 1
            print(f"  skipped ({', '.join(fails)}): {d['title'][:90]}")
            continue
        d["verify"] = unknown
        entry = {"price": d["price"], "title": d["title"], "t": time.time()}
        if d["source"] == "Slickdeals" and slickdeals_expired(d["url"]):
            state[d["id"]] = entry
            continue
        d["rating"] = rate_monitor(d["title"], d["price"])
        notify(d)
        state[d["id"]] = entry
        save_state(state)
        new += 1
    save_state(state)
    print(f"{time.strftime('%H:%M:%S')} checked {len(seen_this_run)} listings, {new} new deal(s). "
          f"Dropped: {drops['not a qualifying monitor']} not a qualifying monitor, "
          f"{drops['price outside range']} price, {drops['broke a rule']} broke a rule.")


# ---------------------------------------------------------------- backtest
SELF_CHECK_CASES = [
    ('Samsung 27" Odyssey G5 QHD 1440p 165Hz HDR10 Curved Gaming Monitor', 189, True),
    ('LG 32" UltraGear 4K UHD 144Hz IPS DisplayHDR 400 Gaming Monitor', 209, True),
    ('MSI 27" 4K 160Hz Rapid IPS HDR Gaming Monitor (Refurbished)', 199, True),
    ('Acer 34" UWQHD 3440x1440 165Hz VA HDR400 Ultrawide Gaming Monitor', 179, True),
    ('27" gaming monitor 165Hz', 119, True),                                   # size/res/HDR partly unknown -> verify
    ('Samsung 27" QHD 165Hz IPS Gaming Monitor', 169, True),                    # no HDR mentioned -> verify
    ('Sceptre 27" QHD 165Hz Gaming Monitor (No HDR)', 129, False),              # says no HDR
    ('AOC 27" 1080p 240Hz Gaming Monitor', 99, False),                          # 1080p
    ('Acer 24.5" QHD 180Hz Gaming Monitor', 119, False),                        # too small
    ('KOORUI 27" QHD 100Hz IPS Monitor', 109, False),                           # under 120Hz
    ('Gigabyte 27" QHD 165Hz IPS HDR Gaming Monitor', 239, False),              # over price
    ('Samsung 43" 4K 144Hz Smart TV', 149, False),                              # TV
    ('VIVO Dual Monitor Desk Mount fits 13 to 32 inch screens', 79, False),     # accessory
    ('ASUS ROG Strix RTX 5070 gaming PC with 27" monitor 165Hz QHD', 129, False),  # PC bundle
]


def backtest():
    out = ["# Monitor backtest report", "",
           "Nothing is saved, and your 'already seen' list is untouched. Old posts are included on purpose.", "",
           "## 1. Built-in self-check (works even if the internet feeds are empty)", ""]
    bad = 0
    for title, price, expect in SELF_CHECK_CASES:
        got, reason, _ = evaluate(title, price)
        bad += got != expect
        out.append(f"- {'✅' if got == expect else '❌ WRONG'} expected {'ALERT' if expect else 'SKIP '}, got "
                   f"{'ALERT' if got else 'SKIP '} ({reason}): {title[:75]}")
    out += ["", f"**Self-check: {len(SELF_CHECK_CASES) - bad}/{len(SELF_CHECK_CASES)} correct.**", "",
            "## 2. Real listings (recent AND older, expired included)", ""]
    deals = fetch_bestbuy() + fetch_slickdeals(max_age_hours=None, keep_unpriced=True)
    seen, alerts, drops = set(), [], {}
    for d in deals:
        if d["id"] in seen:
            continue
        seen.add(d["id"])
        ok, reason, unknown = evaluate(d["title"], d["price"])
        if ok:
            alerts.append((d, unknown))
        else:
            drops.setdefault(reason.split(":")[0].split(" $")[0], []).append((d, reason))
    out.append(f"Scanned **{len(seen)}** listings (Best Buy shows today's listings; Slickdeals includes whatever "
               f"older posts its search feed returns). **{len(alerts)}** would have alerted.")
    out += ["", f"### ✅ Would alert ({len(alerts)})", ""]
    for d, unknown in alerts:
        r = rate_monitor(d["title"], d["price"])
        old = ""
        if d.get("posted") and (datetime.now(timezone.utc) - d["posted"]).total_seconds() > MAX_AGE_HOURS * 3600:
            old = f" ⏳ older than {MAX_AGE_HOURS:g}h, so a live run would skip it"
        out.append(f"- **${d['price']:,.0f}** [{d['source']}, {age_text(d.get('posted')) or 'Best Buy listing'}]{old}"
                   f"{' 🌟4K' if r['is4k'] else ''}  \n  {d['title'][:110]}  \n  score {r['score']}/10"
                   + (f"; verify: {', '.join(unknown)}" if unknown else "") + f"  \n  {d['url']}")
    send = os.getenv("BACKTEST_SEND", "").lower() in ("1", "true", "yes") or "--send" in sys.argv
    if send:
        out += ["", "### 📨 Discord test"]
        if not (DISCORD_WEBHOOK or NTFY_TOPIC):
            out.append("⚠️ No DISCORD_WEBHOOK (or NTFY_TOPIC) is set, so nothing could be sent.")
        else:
            limit = int(os.getenv("BACKTEST_MAX_ALERTS", "8"))
            banner = "🧪 BACKTEST - old listing sent only to test your alerts; it may have expired"
            batch = sorted(alerts, key=lambda a: (a[0].get("rank", 2), -rate_monitor(a[0]["title"], a[0]["price"])["score"]))[:limit]
            for d, unknown in batch:
                d.update(rating=rate_monitor(d["title"], d["price"]), verify=unknown, prefix=banner)
                notify(d)
                time.sleep(1.5)
            if batch:
                out.append(f"Sent **{len(batch)}** of {len(alerts)} qualifying listings (cap {limit}). Check your Discord channel.")
            else:
                t = 'LG 32" UltraGear 4K UHD 144Hz IPS DisplayHDR 400 Gaming Monitor'
                notify({"source": "Test (sample alert)", "title": t, "price": 199, "was": 279, "url": "https://example.com",
                        "rating": rate_monitor(t, 199), "prefix": banner, "verify": check_requirements(t)[1]})
                out.append("No real listings qualified, so one built-in SAMPLE alert was sent instead. Check your Discord channel.")
    out += ["", "### ❌ Dropped"]
    for group, items in sorted(drops.items(), key=lambda kv: -len(kv[1])):
        out += ["", f"**{group}: {len(items)}**"]
        for d, reason in items[:12]:
            out.append(f"- {reason} | {('$%.0f' % d['price']) if d['price'] else 'no price'} | {d['title'][:90]}")
        if len(items) > 12:
            out.append(f"- ...and {len(items) - 12} more")
    report = "\n".join(out)
    print(report)
    Path(__file__).with_name("monitor_backtest_report.md").write_text(report)
    summary = os.getenv("GITHUB_STEP_SUMMARY")
    if summary:
        with open(summary, "a", encoding="utf-8") as f:
            f.write(report + "\n")


def main():
    if "--test" in sys.argv:
        t = 'LG 32" UltraGear 4K UHD 144Hz IPS DisplayHDR 400 Gaming Monitor'
        notify({"source": "Test (sample alert)", "title": t, "price": 199, "was": 279, "url": "https://example.com",
                "ship": "🚚 Ships to you - FREE shipping", "rating": rate_monitor(t, 199), "verify": check_requirements(t)[1]})
        return
    if "--backtest" in sys.argv:
        backtest()
        return
    if "--once" in sys.argv:
        check_once()
        return
    print(f"Watching for 27\"+ / 120Hz+ / QHD+ / HDR monitors <= ${MAX_PRICE:,.0f} every {CHECK_MINUTES:g} min. Ctrl+C to stop.")
    while True:
        try:
            check_once()
        except Exception as e:
            print(f"Check failed: {e}")
        time.sleep(CHECK_MINUTES * 60)


if __name__ == "__main__":
    main()
