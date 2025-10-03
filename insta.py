#!/usr/bin/env python3
# file: instagram_checker_adaptive.py
# -*- coding: utf-8 -*-
"""
سكربت متقدّم لتوليد وفحص يوزرات إنستجرام رباعية بشكل تكيفي (Adaptive).
يحفظ الحالة، يدير توليد دفعات في الخلفية، يدور User-Agent، ويتعامل مع أخطاء الشبكة.
"""

import os
import json
import random
import string
import time
import requests
import glob
import threading
import logging
import signal
from typing import Set, Dict

# -------------------- إعدادات أساسية --------------------
BATCH_DIR = "batches"
PROCESSED_DIR = "processed"
LOGS_DIR = "logs"

STATE_FILE = "state.json"
PATTERNS_STATS_FILE = "patterns_stats.json"

CHECKED_FILE = "checked_usernames.txt"
AVAILABLE_FILE = "available_usernames.txt"
ERRORS_PENDING = os.path.join(BATCH_DIR, "errors_pending.txt")
PROCESSED_ERRORS = os.path.join(PROCESSED_DIR, "errors.txt")
LAST_CHECKED = os.path.join(PROCESSED_DIR, "last_checked.txt")

BATCH_SIZE = 1000
USERNAME_LENGTH = 4            # ثابت كما طلبت
MAX_ACTIVE_BATCHES = 3

REQUEST_TIMEOUT = 7

# التأخيرات (كما طلبت)
DELAY_BASE_MIN = 2.5
DELAY_BASE_MAX = 4.5

# -------------------- User-Agents (12 وكيل حديث) --------------------
USER_AGENTS = [
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.6533.73 Safari/537.36",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_4_0) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.6533.73 Safari/537.36",
    "Mozilla/5.0 (Linux; Android 14; Pixel 7 Pro) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.6533.73 Mobile Safari/537.36",
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) CriOS/127.0.6533.73 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64; rv:127.0) Gecko/20100101 Firefox/127.0",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14.4; rv:127.0) Gecko/20100101 Firefox/127.0",
    "Mozilla/5.0 (Android 14; Mobile; rv:127.0) Gecko/127.0 Firefox/127.0",
    "Mozilla/5.0 (iPhone; CPU iPhone OS 17_0 like Mac OS X) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Mobile/15E148 Safari/604.1",
    "Mozilla/5.0 (Macintosh; Intel Mac OS X 14_4) AppleWebKit/605.1.15 (KHTML, like Gecko) Version/17.0 Safari/605.1.15",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.6533.73 Safari/537.36 Edg/127.0.2651.61",
    "Mozilla/5.0 (Linux; Android 14; Pixel 7 Pro) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/127.0.6533.73 Mobile Safari/537.36 EdgA/127.0.2651.61",
    "Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/126.0.0.0 Safari/537.36"
]

# -------------------- proxies (اختياري) --------------------
USE_PROXY = False
PROXIES = {
    "http": "socks5h://127.0.0.1:9050",
    "https": "socks5h://127.0.0.1:9050"
}

# -------------------- patterns و base weights --------------------
# نعرّف الأنماط التي سنجربها ومقدار الوزن الابتدائي (base_weight)
# علامات: L = letter (a-z), D = digit (0-9), '.' و '_' تظهر كفاصل حسب النمط
# تعديل: خفض وزن الأنماط الشائعة (LDDD, LLDD, DDDD) إلى 1 بناءً على تجارب سابقة (مثل Reddit/Quora: مشغولة بنسبة عالية)
# الحفاظ على الأوزان العالية للنادرة لزيادة فرصة التوفر
PATTERNS = {
    "LDDD": {"template": ["L", "D", "D", "D"], "base_weight": 1},  # شائعة، مشغولة غالباً
    "LLDD": {"template": ["L", "L", "D", "D"], "base_weight": 1},  # شائعة، مشغولة غالباً
    "DDDD": {"template": ["D", "D", "D", "D"], "base_weight": 1},  # شائعة جداً، مشغولة
    "L_DD": {"template": ["L", "_", "D", "D"], "base_weight": 4},   # underscore increases chance
    "L.LD": {"template": ["L", ".", "L", "D"], "base_weight": 4},   # dot in middle
    "RZRD": {"template": ["R", "D", "R", "D"], "base_weight": 5}    # rare-letter pattern
}
# ملاحظة: 'R' تعني حرف نادر (مثل q,z,x,v,j,k,y,w)

PATTERNS_STATS_DEFAULT = {
    # each pattern -> {"tries": 0, "successes": 0}
}

# -------------------- ملفات ومزامنة --------------------
generation_lock = threading.Lock()
excluded_lock = threading.Lock()  # تحسين: قفل لـ excluded
generation_threads = {}
SHOULD_STOP = False

# ================== logging ==================
os.makedirs(LOGS_DIR, exist_ok=True)
log_filename = os.path.join(LOGS_DIR, time.strftime("run_%Y%m%d_%H%M%S.log"))
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s [%(levelname)s] %(message)s",
    handlers=[logging.FileHandler(log_filename, encoding="utf-8"), logging.StreamHandler()]
)
logger = logging.getLogger(__name__)
logger.info("بدأ التشغيل. سجل محفوظ في: %s", log_filename)

# ================== إشارة الإيقاف النظيف ==================
def handle_sigint(sig, frame):
    global SHOULD_STOP
    SHOULD_STOP = True
    logger.info("استلمت إشارة إيقاف (SIGINT). سأنهي التشغيل بأمان بعد المهمة الحالية...")
signal.signal(signal.SIGINT, handle_sigint)

# -------------------- دوال ملفات ومجلدات --------------------
def ensure_dirs_and_files():
    os.makedirs(BATCH_DIR, exist_ok=True)
    os.makedirs(PROCESSED_DIR, exist_ok=True)
    os.makedirs(LOGS_DIR, exist_ok=True)
    # إنشاء ملفات إن لم تكن موجودة
    for p in (CHECKED_FILE, AVAILABLE_FILE, ERRORS_PENDING, PROCESSED_ERRORS, STATE_FILE, PATTERNS_STATS_FILE, LAST_CHECKED):
        if not os.path.exists(p):
            with open(p, "w", encoding="utf-8") as f:
                if p == PATTERNS_STATS_FILE:
                    json.dump({}, f)

def load_state():
    if not os.path.exists(STATE_FILE) or os.path.getsize(STATE_FILE) == 0:
        return {"current_batch": 1, "current_index": 0, "total_checks": 0}
    with open(STATE_FILE, "r", encoding="utf-8") as f:
        return json.load(f)

def save_state(state: dict):
    with open(STATE_FILE, "w", encoding="utf-8") as f:
        json.dump(state, f)

def read_lines_set(path: str) -> Set[str]:
    if not os.path.exists(path):
        return set()
    with open(path, "r", encoding="utf-8") as f:
        return set(line.strip() for line in f if line.strip())

def append_line(path: str, line: str):
    with open(path, "a", encoding="utf-8") as f:
        f.write(line + "\n")

def overwrite_file(path: str, lines):
    with open(path, "w", encoding="utf-8") as f:
        if lines:
            f.write("\n".join(lines) + "\n")
        else:
            f.write("")

# -------------------- نماذج توليد الحروف --------------------
LETTERS = string.ascii_lowercase
DIGITS = string.digits
RARE_LETTERS = list("zqxvjkyw")  # قائمة أحرف نادرة مقترحة

def valid_username_candidate(u: str) -> bool:
    """التحقّق من قواعدك: لا يبدأ/ينتهي بـ '.'، لا '..'، فقط أحرف/أرقام/._"""
    if not u:
        return False
    allowed = set(string.ascii_lowercase + string.digits + "._")
    if any(ch not in allowed for ch in u):
        return False
    if u.startswith(".") or u.endswith("."):
        return False
    if ".." in u:
        return False
    return True

def generate_from_pattern(pattern_key: str) -> str:
    """يعطي اسمًا بحسب قالب pattern - تحسين: حلقة بدلاً من recursion"""
    tpl = PATTERNS[pattern_key]["template"]
    attempts = 0
    while attempts < 10:  # حد أقصى للسلامة
        parts = []
        for token in tpl:
            if token == "L":
                parts.append(random.choice(LETTERS))
            elif token == "D":
                parts.append(random.choice(DIGITS))
            elif token == "R":
                parts.append(random.choice(RARE_LETTERS))
            elif token == ".":
                parts.append(".")
            elif token == "_":
                parts.append("_")
            else:
                parts.append(token)
        username = "".join(parts)
        if valid_username_candidate(username):
            return username
        attempts += 1
    # إذا فشل، أعد توليد بسيط
    return generate_from_pattern(random.choice(list(PATTERNS.keys())))

# -------------------- إدارة إحصاءات الأنماط --------------------
def load_patterns_stats() -> Dict[str, Dict[str, int]]:
    if not os.path.exists(PATTERNS_STATS_FILE) or os.path.getsize(PATTERNS_STATS_FILE) == 0:
        # إعداد القيم الافتراضية من base_weight
        data = {k: {"tries": 0, "successes": 0, "base_weight": PATTERNS[k]["base_weight"]} for k in PATTERNS}
        with open(PATTERNS_STATS_FILE, "w", encoding="utf-8") as f:
            json.dump(data, f)
        return data
    with open(PATTERNS_STATS_FILE, "r", encoding="utf-8") as f:
        return json.load(f)

def save_patterns_stats(stats: Dict[str, Dict[str, int]]):
    with open(PATTERNS_STATS_FILE, "w", encoding="utf-8") as f:
        json.dump(stats, f)

def compute_pattern_weights(stats: Dict[str, Dict[str, int]]) -> Dict[str, float]:
    """
    نحسب وزن كل نمط كـ base_weight * ((successes+1)/(tries+1))
    هذا يمنح أنماطًا ناجحة وزنًا أعلى.
    """
    weights = {}
    for k, v in stats.items():
        base = v.get("base_weight", PATTERNS[k]["base_weight"])
        tries = v.get("tries", 0)
        succ = v.get("successes", 0)
        ratio = (succ + 1) / (tries + 1)
        weights[k] = base * ratio
    # إذا كل الأوزان صفرية لأي سبب نعيد أوزان base بسيطة
    if sum(weights.values()) == 0:
        for k in weights:
            weights[k] = PATTERNS[k]["base_weight"]
    return weights

def choose_pattern(stats: Dict[str, Dict[str, int]]) -> str:
    """نختار نمطًا عشوائياً وفق الأوزان المحسوبة (weighted random)."""
    weights = compute_pattern_weights(stats)
    total = sum(weights.values())
    pick = random.uniform(0, total)
    upto = 0.0
    for k, w in weights.items():
        upto += w
        if pick <= upto:
            return k
    return random.choice(list(PATTERNS.keys()))

# -------------------- توليد دفعة (خلفي) مع حفظ mapping اسم->pattern --------------------
def batch_filename(batch_num: int) -> str:
    return os.path.join(BATCH_DIR, f"random_{batch_num}.txt")

def batch_meta_filename(batch_num: int) -> str:
    return os.path.join(BATCH_DIR, f"random_{batch_num}.meta.json")

def batch_complete_marker(batch_num: int) -> str:
    return os.path.join(BATCH_DIR, f"random_{batch_num}.complete")

def generate_batch_in_background(batch_num: int, excluded: Set[str], stats: Dict[str, Dict[str, int]]):
    """
    يكتب ملف الدفعة تدريجيًا في الخلفية. لكل اسم يحتفظ بنمطه في ملف .meta.json
    يضمن أن لا يتكرر الاسم عبر excluded.
    """
    fname = batch_filename(batch_num)
    meta_fname = batch_meta_filename(batch_num)
    marker = batch_complete_marker(batch_num)
    if os.path.exists(marker):
        logger.info("Batch %d already complete.", batch_num)
        return
    if os.path.exists(fname):
        logger.info("Batch %d file exists already (%s).", batch_num, fname)
        return

    def worker():
        logger.info("بدء توليد الدفعة #%d في الخلفية...", batch_num)
        written = []
        mapping = {}  # username -> pattern_key
        try:
            with open(fname, "w", encoding="utf-8") as f:
                while len(written) < BATCH_SIZE and not SHOULD_STOP:
                    # نختار نمطًا وفق الأوزان التكيفية
                    pattern_key = choose_pattern(stats)
                    # نولد اسمًا من ذلك النمط
                    u = generate_from_pattern(pattern_key)
                    with generation_lock:
                        with excluded_lock:  # تحسين: قفل excluded
                            if u in excluded or u in mapping or u in written:
                                continue
                            # نضيف للاحتلال المبكر حتى لا يولّدها خيط آخر
                            excluded.add(u)
                            mapping[u] = pattern_key
                            written.append(u)
                            f.write(u + "\n")
                            # التفريغ الفوري ليس دائماً ضروري لكن يُسهل الفاحص
                            f.flush()
                            os.fsync(f.fileno())
                    if len(written) % 100 == 0:
                        logger.info("Batch %d: كتبت %d أسماء...", batch_num, len(written))
                # بعد الانتهاء نكتب ملف الميتا (mapping)
            with open(meta_fname, "w", encoding="utf-8") as mf:
                json.dump(mapping, mf)
            # علامة الاكتمال
            with open(marker, "w", encoding="utf-8") as m:
                m.write(f"complete: {time.strftime('%Y-%m-%d %H:%M:%S')}\n")
            logger.info("انتهى توليد الدفعة #%d (ملف: %s).", batch_num, fname)
        except Exception as e:
            logger.exception("خطأ أثناء توليد الدفعة #%d: %s", batch_num, e)

    t = threading.Thread(target=worker, daemon=True)
    generation_threads[batch_num] = t
    t.start()

def ensure_three_batches_exist(start_batch: int, excluded: Set[str], stats: Dict[str, Dict[str, int]]):
    for b in range(start_batch, start_batch + MAX_ACTIVE_BATCHES):
        fname = batch_filename(b)
        marker = batch_complete_marker(b)
        if os.path.exists(marker):
            continue
        if os.path.exists(fname):
            continue
        # شغّل توليد الخلفية
        generate_batch_in_background(b, excluded, stats)

# -------------------- فحص اسم على إنستجرام --------------------
def check_username_instagram(username: str) -> (str, str):
    """
    يعيد tuple(status, info)
    status: "available", "taken", "network_error"
    info: كود الحالة أو رسالة الخطأ
    تحسين: فحص HTML للـ 200
    """
    url = f"https://www.instagram.com/{username}/"
    headers = {"User-Agent": random.choice(USER_AGENTS)}
    try:
        if USE_PROXY:
            resp = requests.get(url, headers=headers, proxies=PROXIES, timeout=REQUEST_TIMEOUT)
        else:
            resp = requests.get(url, headers=headers, timeout=REQUEST_TIMEOUT)
    except requests.RequestException as e:
        return "network_error", str(e)
    if resp.status_code == 404:
        return "available", "404"
    elif resp.status_code == 200:
        if "Sorry, this page isn't available." in resp.text or "page not found" in resp.text.lower():
            return "available", "not_found_in_html"
        else:
            return "taken", "200_with_content"
    else:
        return "taken", str(resp.status_code)

# -------------------- تأخيرات ذكية --------------------
def smart_sleep(total_checks_done: int):
    base = random.uniform(DELAY_BASE_MIN, DELAY_BASE_MAX)
    time.sleep(base)
    # فترات الراحة الإضافية كما طلبت
    if total_checks_done % 1000 == 0:
        extra = random.uniform(900, 1800)
        logger.info("توقف طويل بعد %d محاولة: %.1f دقيقة", total_checks_done, extra / 60)
        time.sleep(extra)
    elif total_checks_done % 500 == 0:
        extra = random.uniform(300, 600)
        logger.info("توقف طويل بعد %d محاولة: %.1f دقيقة", total_checks_done, extra / 60)
        time.sleep(extra)
    elif total_checks_done % 100 == 0:
        extra = random.uniform(90, 120)
        logger.info("توقف بعد %d محاولة: %.1f ثانية", total_checks_done, extra)
        time.sleep(extra)
    elif total_checks_done % 50 == 0:
        extra = random.uniform(15, 30)
        logger.info("توقف بعد %d محاولة: %.1f ثانية", total_checks_done, extra)
        time.sleep(extra)
    elif total_checks_done % 10 == 0:
        extra = random.uniform(10, 15)
        logger.info("توقف بعد %d محاولة: %.1f ثانية", total_checks_done, extra)
        time.sleep(extra)

# -------------------- معالجة الأخطاء المعلقة أولاً --------------------
def process_pending_errors(state: dict, excluded: Set[str], stats: Dict[str, Dict[str, int]]):
    if not os.path.exists(ERRORS_PENDING):
        return
    pending = [line.strip() for line in open(ERRORS_PENDING, "r", encoding="utf-8") if line.strip()]
    if not pending:
        return
    logger.info("معالجة %d يوزرنم من pending errors...", len(pending))
    remaining = []
    for u in pending:
        if SHOULD_STOP:
            remaining.append(u)
            continue
        status, info = check_username_instagram(u)
        state["total_checks"] = state.get("total_checks", 0) + 1
        overwrite_file(LAST_CHECKED, [f"current_batch: {state.get('current_batch')}",
                                     f"current_index: {state.get('current_index')}",
                                     f"current_username: {u}",
                                     f"timestamp: {time.strftime('%Y-%m-%d %H:%M:%S')}"])
        if status == "network_error":
            logger.warning("خطأ شبكي على %s — إبقاؤه في pending", u)
            remaining.append(u)
        elif status == "available":
            logger.info("(pending) متاح: %s", u)
            append_line(AVAILABLE_FILE, u)
            append_line(CHECKED_FILE, u)
            with excluded_lock:
                excluded.add(u)
            # لا نملك نمط هذا الاسم هنا (ربما مصدره يدوي) لذلك لا نحدّث الإحصاءات
        else:
            logger.info("(pending) غير متاح: %s (info=%s)", u, info)
            append_line(CHECKED_FILE, u)
            append_line(PROCESSED_ERRORS, f"{u}  # {info}")
            with excluded_lock:
                excluded.add(u)
        smart_sleep(state["total_checks"])
    overwrite_file(ERRORS_PENDING, remaining)
    logger.info("انتهت معالجة pending; متبقي: %d", len(remaining))

# -------------------- البرنامج الرئيسي --------------------
def collect_all_existing_usernames() -> Set[str]:
    with excluded_lock:  # تحسين: قفل أثناء القراءة
        s = set()
        s.update(read_lines_set(CHECKED_FILE))
        s.update(read_lines_set(AVAILABLE_FILE))
        if os.path.exists(ERRORS_PENDING):
            s.update(read_lines_set(ERRORS_PENDING))
        for path in glob.glob(os.path.join(BATCH_DIR, "random_*.txt")):
            s.update(read_lines_set(path))
        for path in glob.glob(os.path.join(PROCESSED_DIR, "random_*.txt")):
            s.update(read_lines_set(path))
        return s

def main():
    global SHOULD_STOP
    ensure_dirs_and_files()

    # تحميل الحالة والإحصاءات
    state = load_state()
    stats = load_patterns_stats()

    # استبعاد كل الأسماء الحالية لتجنّب التكرار عبر الدفعات
    excluded = collect_all_existing_usernames()
    logger.info("جمعت %d اسمًا مستبعدًا.", len(excluded))

    # تأكد من وجود ثلاث دفعات (سيُدَأ توليدهن في الخلفية حسب الحاجة)
    ensure_three_batches_exist(state.get("current_batch", 1), excluded, stats)

    # معالجة الأخطاء المعلقة أولاً
    process_pending_errors(state, excluded, stats)
    save_state(state)

    # بعد معالجة pending نعيد تجميع excluded لأنه قد تغيّر
    excluded = collect_all_existing_usernames()

    current = state.get("current_batch", 1)

    while not SHOULD_STOP:
        batch_file = batch_filename(current)
        meta_file = batch_meta_filename(current)
        marker = batch_complete_marker(current)

        # شغّل توليد الدفعة في الخلفية إذا لم تكن موجودة
        if not os.path.exists(batch_file):
            ensure_three_batches_exist(current, excluded, stats)

        # نقرأ الملف الديناميكي (حتى لو لم يكتمل)
        # نعيد قراءته بشكل متكرر بينما التوليد يجري
        while True:
            if SHOULD_STOP:
                break
            if os.path.exists(batch_file):
                with open(batch_file, "r", encoding="utf-8") as f:
                    lines = [ln.strip() for ln in f if ln.strip()]
                break
            else:
                logger.info("انتظار توليد ملف الدفعة #%d ...", current)
                time.sleep(0.5)

        total = len(lines)
        idx = state.get("current_index", 0)
        logger.info("بدء فحص الدفعة #%d — الحالي مكتوب: %d عناصر — بدء من index=%d", current, total, idx)

        # حلقة قراءة/فحص السطور المكتوبة حتى نصل لنهاية الدفعة (أو إيقاف)
        while idx < BATCH_SIZE and not SHOULD_STOP:
            # إعادة قراءة الملف كل مرة لأن التوليد قد يضيف أسطرًا
            with open(batch_file, "r", encoding="utf-8") as f:
                lines = [ln.strip() for ln in f if ln.strip()]
            total = len(lines)
            if idx >= total:
                # لم تُكتب سطر بعد؛ إذا وُجد marker وidx>=total فهذا يعني انتهى الملف فعليًا
                if os.path.exists(marker):
                    logger.info("الملف مكتمل وليس به المزيد (idx=%d total=%d).", idx, total)
   
