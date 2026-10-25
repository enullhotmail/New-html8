import os
import re
import shutil
import asyncio
import json
import base64
import zipfile
import requests
import time
import uuid
import urllib.parse
import io
import tempfile
import random
import html
from collections import Counter
from urllib.parse import urlparse, quote, unquote
from datetime import datetime
import redis.asyncio as redis
from concurrent.futures import ThreadPoolExecutor
from aiohttp import web
from telegram import Update, InlineKeyboardMarkup, InlineKeyboardButton
from telegram.ext import (
    Application,
    CommandHandler,
    MessageHandler,
    filters,
    ContextTypes,
    ConversationHandler,
    CallbackQueryHandler,
)
import logging
import warnings
warnings.filterwarnings("ignore", message=".*per_message.*", category=UserWarning)

logging.basicConfig(format='%(asctime)s - %(name)s - %(levelname)s - %(message)s', level=logging.INFO)

REDIS_URL = os.environ.get("REDIS_URL", "redis://localhost:6379")
redis_client = redis.Redis.from_url(REDIS_URL, decode_responses=True, max_connections=50)

WEB_DOMAIN = os.environ.get("WEB_DOMAIN", "http://localhost:8080").rstrip('/')
ADMIN_IDS = [int(aid.strip()) for aid in os.environ.get("ADMIN_ID", "0").split(",") if aid.strip().isdigit()]

PHONE, OTP, ASK_TAG, ASK_SEARCH = range(4)

executor = ThreadPoolExecutor(max_workers=40)

# قفل‌های سراسری برای جلوگیری از تداخل عملیات‌های سنگین و صف‌بندی چند فایل زیپ
zip_queue_lock = asyncio.Lock()
refresh_task_lock = asyncio.Lock()
heavy_task_lock = asyncio.Lock()

# متغیرهای مدیریت دریافت دسته‌ای (Batch) صدها تا هزاران فایل زیپ / لینک
batch_collection_lock = asyncio.Lock()
batch_ui_update_tasks = {}

USER_AGENTS = [
    "Mozilla/5.0 (Linux; Android 13; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/114.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 12; Pixel 6 Pro) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/112.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 11; SM-G991B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/111.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.0.0 Mobile Safari/537.36"
]

FIRST_NAMES = ["علی", "محمد", "امیر", "حسین", "رضا", "مهدی", "سجاد", "نیما", "عرفان", "پوریا", "سارا", "مریم", "فاطمه", "زهرا", "الهام", "نرگس", "یلدا", "نگار", "مهسا"]
LAST_NAMES = ["محمدی", "حسینی", "احمدی", "رضایی", "کریمی", "موسوی", "جعفری", "قاسمی", "حیدری", "صادقی", "مرادی", "رحیمی", "اکبری", "طاهری", "رستمی"]

# آدرس پیش‌فرض تهران (مطابق با استاندارد نقشه ParsiMap در Main 9)
DEFAULT_TEHRAN_ADDRESS = {
    'lat': 35.69975,
    'lng': 51.33551,
    'address': 'تهران، خیابان آزادی، پلاک ۱',
    'plaque': '1',
    'unit': '1',
    'cityId': 129
}


def clean_digits(text: str) -> str:
    """تبدیل خودکار ارقام فارسی و عربی به انگلیسی"""
    if not text:
        return ""
    return text.translate(str.maketrans('۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩', '01234567890123456789')).strip()


def format_bytes(size_bytes: int) -> str:
    """تبدیل بایت به فرمت خوانا (KB, MB, GB)"""
    if not size_bytes or size_bytes <= 0:
        return "0 B"
    for unit in ['B', 'KB', 'MB', 'GB', 'TB']:
        if size_bytes < 1024.0:
            return f"{size_bytes:.2f} {unit}"
        size_bytes /= 1024.0
    return f"{size_bytes:.2f} PB"


# ==========================================
# موتور هوشمند پردازش و نرمال‌سازی پروکسی (ادغام‌شده از Main 9)
# ==========================================
def _score_host_port(host_candidate: str, port_candidate: str) -> int:
    try:
        if not port_candidate or not port_candidate.isdigit():
            return 0
        port_num = int(port_candidate)
        if not (1 <= port_num <= 65535):
            return 0
        if not host_candidate or any(c in host_candidate for c in (' ', '@', '/', '\\', ':')):
            return 0
        if re.match(r'^\d{1,3}(\.\d{1,3}){3}$', host_candidate):
            return 3
        if '.' in host_candidate and re.match(r'^[a-zA-Z0-9._-]+$', host_candidate):
            return 2
        if re.match(r'^[a-zA-Z0-9._-]+$', host_candidate):
            return 1
        return 0
    except Exception:
        return 0


def normalize_proxy(raw_proxy: str):
    try:
        if not raw_proxy or not isinstance(raw_proxy, str):
            return None
        line = raw_proxy.strip().strip('"').strip("'").strip(',').strip()
        if not line or line.startswith('#'):
            return None

        scheme = "http"
        rest = line
        scheme_match = re.match(r'^(https?|socks5h?|socks4a?)://(.*)$', line, re.IGNORECASE)
        if scheme_match:
            scheme = scheme_match.group(1).lower()
            rest = scheme_match.group(2)

        rest = rest.strip().rstrip('/')
        if not rest or '/' in rest or '?' in rest:
            return None

        host, port, user, password = None, None, None, None

        if '@' in rest:
            left_a, right_a = rest.rsplit('@', 1)
            left_b, right_b = rest.split('@', 1)

            score_right = 0
            if ':' in right_a:
                r_h, r_p = right_a.rsplit(':', 1)
                score_right = _score_host_port(r_h, r_p)

            score_left = 0
            if ':' in left_b:
                l_h, l_p = left_b.rsplit(':', 1)
                score_left = _score_host_port(l_h, l_p)

            if score_right >= score_left and score_right > 0 and ':' in left_a:
                host, port = right_a.rsplit(':', 1)
                user, password = left_a.split(':', 1)
            elif score_left > score_right and score_left > 0 and ':' in right_b:
                host, port = left_b.rsplit(':', 1)
                user, password = right_b.split(':', 1)
            else:
                return None
        else:
            parts = rest.split(':')
            if len(parts) == 2:
                if _score_host_port(parts[0], parts[1]) > 0:
                    host, port = parts[0], parts[1]
                else:
                    return None
            elif len(parts) >= 4:
                score_first = _score_host_port(parts[0], parts[1])
                score_last = _score_host_port(parts[-2], parts[-1])

                if score_first >= score_last and score_first > 0:
                    host, port = parts[0], parts[1]
                    user = parts[2]
                    password = ':'.join(parts[3:])
                elif score_last > score_first and score_last > 0:
                    host, port = parts[-2], parts[-1]
                    user = parts[0]
                    password = ':'.join(parts[1:-2])
                else:
                    return None
            else:
                return None

        if not host or not port:
            return None

        if user is not None and password is not None:
            safe_user = quote(unquote(user.strip()), safe='')
            safe_pass = quote(unquote(password.strip()), safe='')
            return f"{scheme}://{safe_user}:{safe_pass}@{host.strip()}:{port.strip()}"
        else:
            return f"{scheme}://{host.strip()}:{port.strip()}"
    except Exception:
        return None


def is_proxy_source_url(text_line: str) -> bool:
    try:
        line = text_line.strip()
        if not line.lower().startswith(('http://', 'https://')):
            return False
        parsed = urlparse(line)
        if (parsed.path and parsed.path != '/') or parsed.query or not parsed.port:
            return True
        return False
    except Exception:
        return False


def parse_proxies_from_any_content(content: str) -> list:
    valid_proxies = []
    if not content:
        return valid_proxies

    try:
        json_data = json.loads(content)
        items = []
        if isinstance(json_data, list):
            items = json_data
        elif isinstance(json_data, dict):
            for key in ('proxies', 'data', 'result', 'list', 'items'):
                if isinstance(json_data.get(key), list):
                    items = json_data[key]
                    break

        for item in items:
            if isinstance(item, str):
                norm = normalize_proxy(item)
                if norm:
                    valid_proxies.append(norm)
            elif isinstance(item, dict):
                h = item.get('ip') or item.get('host') or item.get('server')
                p = item.get('port')
                u = item.get('username') or item.get('user')
                pw = item.get('password') or item.get('pass')
                sc = item.get('protocol') or item.get('type') or item.get('scheme') or 'http'
                if isinstance(sc, list) and sc:
                    sc = sc[0]
                if h and p:
                    raw = f"{sc}://{u}:{pw}@{h}:{p}" if (u and pw) else f"{sc}://{h}:{p}"
                    norm = normalize_proxy(raw)
                    if norm:
                        valid_proxies.append(norm)
        if valid_proxies:
            return list(dict.fromkeys(valid_proxies))
    except Exception:
        pass

    for token in re.split(r'[\r\n\s,;]+', content):
        token = token.strip()
        if not token:
            continue
        norm = normalize_proxy(token)
        if norm:
            valid_proxies.append(norm)

    return list(dict.fromkeys(valid_proxies))


def load_proxies_from_input(raw_text: str) -> list:
    extracted_proxies = []
    tokens = re.split(r'[\r\n\s]+', raw_text.strip())
    for token in tokens:
        if not token:
            continue
        if is_proxy_source_url(token):
            try:
                res = requests.get(token, timeout=15)
                if res.status_code == 200:
                    from_url = parse_proxies_from_any_content(res.text)
                    if from_url:
                        extracted_proxies.extend(from_url)
            except Exception:
                pass
        else:
            norm = normalize_proxy(token)
            if norm:
                extracted_proxies.append(norm)
    return list(dict.fromkeys(extracted_proxies))


async def get_all_existing_phones_in_db() -> set:
    """دریافت سریع تمامی شماره‌های موجود در دیتابیس برای جلوگیری از ساخت لینک تکراری"""
    existing = set()
    try:
        acc_keys = await redis_client.keys("account:*")
        for k in acc_keys:
            p = clean_digits(k.replace("account:", ""))
            if p:
                existing.add(p)

        active_keys = await redis_client.keys("phone_active_link:*")
        for k in active_keys:
            p = clean_digits(k.replace("phone_active_link:", ""))
            if p:
                existing.add(p)
    except Exception as e:
        logging.error(f"Error fetching existing phones from DB: {e}")
    return existing


def get_random_persian_name():
    return random.choice(FIRST_NAMES), random.choice(LAST_NAMES)


def mask_proxy(proxy_dict) -> str:
    if not proxy_dict or 'http' not in proxy_dict:
        return "بدون پروکسی (Direct)"
    return proxy_dict['http'].split('@')[-1]


def init_device_session(context: ContextTypes.DEFAULT_TYPE):
    """ساخت هویت دستگاه اختصاصی برای هر شماره"""
    context.user_data['device_id'] = str(uuid.uuid4())
    context.user_data['session_id'] = str(uuid.uuid4())
    context.user_data['correlation_id'] = str(uuid.uuid4())
    context.user_data['user_agent'] = random.choice(USER_AGENTS)


def get_user_headers(context: ContextTypes.DEFAULT_TYPE):
    if 'device_id' not in context.user_data or 'user_agent' not in context.user_data:
        init_device_session(context)
    return {
        'accept': 'application/json, text/plain, */*',
        'source': 'okala',
        'ui-version': '2.0',
        'origin': 'https://www.okala.com',
        'User-Agent': context.user_data['user_agent'],
        'X-User-Unique-Id': context.user_data['device_id'],
        'X-Correlation-Id': context.user_data.get('correlation_id', str(uuid.uuid4())),
        'session-id': context.user_data['session_id']
    }


def is_admin(user_id):
    return user_id in ADMIN_IDS


async def is_user_authorized(user_id: int) -> bool:
    """بررسی مجوز استفاده از ربات (الزام تایید توسط ادمین)"""
    if is_admin(user_id):
        return True
    return bool(await redis_client.sismember("authorized_users", str(user_id)))


# ==========================================
# استخراج تمام کدهای تخفیف یک اکانت و تفکیک هوشمند آن‌ها
# ==========================================
def extract_all_valid_discounts(res: dict) -> list:
    """
    استخراج تمامی کدهای تخفیف فعال یک اکانت (چه ۱ کد، چه ۲ کد یا بیشتر).
    هیچ کد تخفیف فعالی نادیده گرفته نمی‌شود.
    """
    if not isinstance(res, dict):
        return []
    raw_vouchers = res.get('data') or []
    if not isinstance(raw_vouchers, list):
        return []

    valid_list = []
    for v in raw_vouchers:
        if not isinstance(v, dict):
            continue
        if v.get('isUsed') is True or v.get('isActive') is False:
            continue

        amt = v.get('discountAmount') or 0
        pct = v.get('discountPercentage') or 0
        code_str = v.get('code') or v.get('discountCode') or 'بدون کد'
        min_order = v.get('minimumFactoreAmount') or v.get('minOrderAmount') or 0
        exp_date = str(v.get('expirationDate') or v.get('expireDate') or '-').replace('T', ' ')
        title = v.get('name') or v.get('discountName') or v.get('title') or ''

        amt_num = int(amt) if isinstance(amt, (int, float)) and amt > 0 else 0
        pct_num = int(pct) if isinstance(pct, (int, float)) and pct > 0 else 0
        min_num = int(min_order) if isinstance(min_order, (int, float)) and min_order > 0 else 0

        # اگر کد تخفیف مبلغ، درصد یا کد معتبر دارد ثبت شود
        if amt_num > 0 or pct_num > 0 or (code_str and code_str != 'بدون کد'):
            amount_toman_k = amt_num // 10000 if amt_num >= 10000 else (amt_num // 1000 if amt_num > 0 else 0)
            if amt_num > 0:
                label = f"{amount_toman_k} هزار تومانی"
                detail_val = f"{amount_toman_k} هزار تومان ({amt_num // 10:,} تومان)"
            elif pct_num > 0:
                label = f"{pct_num} درصدی"
                detail_val = f"{pct_num}% تخفیف"
            else:
                label = "سایر کدهای تخفیف"
                detail_val = "کد تخفیف فعال"

            valid_list.append({
                "code": code_str,
                "amount": amt_num,
                "amount_k": amount_toman_k,
                "percentage": pct_num,
                "min_order": min_num,
                "min_order_toman": min_num // 10 if min_num > 0 else 0,
                "expiration": exp_date,
                "title": title,
                "label": label,
                "detail_val": detail_val
            })

    valid_list.sort(key=lambda x: (x['amount'], x['percentage']), reverse=True)
    return valid_list


def parse_and_split_discounts(text_content: str):
    """
    تحلیل متن یا فایل گزارش تخفیف (پشتیبانی از اکانت‌های دارای ۱، ۲ یا چند کد تخفیف همزمان)
    و دسته‌بندی لینک‌ها بر اساس تک‌تک مبالغ تخفیف موجود در هر اکانت.
    """
    clean_text = re.sub(r'<[^>]+>', '', text_content)
    clean_text = clean_digits(clean_text)
    grouped = {}
    total_links_added = 0
    current_amounts = set()

    for line in clean_text.splitlines():
        line = line.strip()
        if not line:
            continue

        # شناسایی تمامی مبالغ ذکر شده در خطوط کد تخفیف (مثلاً: 100 هزار تومان، 150 هزار تومانی یا بیشترین مبلغ: 100)
        for m in re.finditer(r'(\d+)\s*هزار\s*تومان', line):
            val = int(m.group(1))
            if val > 0:
                current_amounts.add(val)

        amt_match = re.search(r'بیشترین مبلغ\s*:\s*(\d+)', line)
        if amt_match:
            val = int(amt_match.group(1))
            if val > 0:
                current_amounts.add(val)

        all_amts_match = re.search(r'مبالغ تخفیف\s*:\s*([\d\s,+،]+)', line)
        if all_amts_match:
            for num_s in re.findall(r'\d+', all_amts_match.group(1)):
                val = int(num_s)
                if val > 0:
                    current_amounts.add(val)

        link_match = re.search(r'(https?://[^\s]+)', line)
        if link_match and current_amounts:
            link = link_match.group(1).strip()
            for amt in sorted(current_amounts, reverse=True):
                if link not in grouped.setdefault(amt, []):
                    grouped[amt].append(link)
                    total_links_added += 1
            current_amounts.clear()

    return grouped, total_links_added


# ==========================================
# سیستم مدیریت پروکسی و API
# ==========================================
async def get_all_proxies_from_db():
    proxies_json = await redis_client.get("settings:proxies")
    if proxies_json:
        try:
            proxies = json.loads(proxies_json)
            if isinstance(proxies, list) and len(proxies) > 0:
                return proxies
        except Exception:
            pass
    return []


async def get_random_proxy_from_db():
    proxies = await get_all_proxies_from_db()
    if proxies:
        p = random.choice(proxies)
        return {"http": p, "https": p}
    return None


def get_proxy_by_index(proxies_list, idx: int):
    if proxies_list:
        p = proxies_list[idx % len(proxies_list)]
        return {"http": p, "https": p}
    return None


def decode_jwt_payload(token: str) -> dict:
    if not token or not isinstance(token, str) or '.' not in token:
        return {}
    try:
        payload = token.split('.')[1]
        payload += '=' * (-len(payload) % 4)
        decoded_bytes = base64.urlsafe_b64decode(payload)
        return json.loads(decoded_bytes)
    except Exception:
        return {}


def get_user_id_from_token(token):
    """استخراج Cerberus ID (UUID) برای API تخفیف‌ها"""
    data = decode_jwt_payload(token)
    raw_sub = data.get('sub')
    return (
        data.get('cerberusId')
        or data.get('CerberusId')
        or data.get('cerberus_id')
        or (raw_sub if isinstance(raw_sub, str) and '-' in raw_sub else None)
        or data.get('alternativeCustomerId')
        or data.get('userId')
    )


def get_numeric_customer_id_from_token(token, data_dict=None) -> int:
    """استخراج شناسه عددی مشتری (customerId / uid) برای ثبت آدرس و سبد خرید (مطابق Main 9)"""
    jwt_data = decode_jwt_payload(token)
    raw_uid = jwt_data.get('userId') or jwt_data.get('alternativeCustomerId') or jwt_data.get('sub')
    if raw_uid is not None:
        try:
            val = int(raw_uid)
            if val > 0:
                return val
        except (ValueError, TypeError):
            pass

    if isinstance(data_dict, dict):
        for origin in data_dict.get('origins', []):
            for item in origin.get('localStorage', []):
                if item.get('name') == 'user' and item.get('value'):
                    try:
                        u_obj = json.loads(urllib.parse.unquote(item['value']))
                        cid = u_obj.get('id') or u_obj.get('alternativeCustomerId')
                        if cid and int(cid) > 0:
                            return int(cid)
                    except Exception:
                        pass
                elif item.get('name') == 'persist:root' and item.get('value'):
                    try:
                        p_root = json.loads(item['value'])
                        u_outer = json.loads(p_root.get('user', '{}'))
                        u_inner = u_outer.get('user', {})
                        if isinstance(u_inner, dict):
                            cid = u_inner.get('id') or u_inner.get('alternativeCustomerId')
                            if cid and int(cid) > 0:
                                return int(cid)
                    except Exception:
                        pass
    return 0


def extract_tokens_from_json_data(data: dict):
    """استخراج دقیق access_token، refresh_token و شماره موبایل از ساختار JSON فایل زیپ یا لینک"""
    if not isinstance(data, dict):
        return None, None, None
    access_token, refresh_token, mobile = None, None, None

    for cookie in data.get('cookies', []):
        if not isinstance(cookie, dict):
            continue
        c_name = cookie.get('name')
        c_val = cookie.get('value')
        if c_name in ['tokenMS', 'token'] and c_val and not access_token:
            access_token = c_val
        elif c_name == 'refresh_token' and c_val and not refresh_token:
            refresh_token = c_val

    for origin in data.get('origins', []):
        if not isinstance(origin, dict):
            continue
        for item in origin.get('localStorage', []):
            if not isinstance(item, dict):
                continue
            i_name = item.get('name')
            i_val = item.get('value')
            if i_name == 'tokenMS' and i_val and not access_token:
                access_token = i_val
            elif i_name == 'refresh_token' and i_val and not refresh_token:
                refresh_token = i_val
            elif i_name == 'user' and i_val and not mobile:
                try:
                    u_obj = json.loads(urllib.parse.unquote(i_val))
                    mobile = u_obj.get('mobilePhone') or u_obj.get('userName')
                except Exception:
                    pass
            elif i_name == 'persist:root' and i_val and not access_token:
                try:
                    p_root = json.loads(i_val)
                    u_outer = json.loads(p_root.get('user', '{}'))
                    u_inner = u_outer.get('user', {})
                    if isinstance(u_inner, dict):
                        access_token = access_token or u_inner.get('token')
                        mobile = mobile or u_inner.get('mobilePhone')
                except Exception:
                    pass

    if not mobile and access_token:
        jwt_d = decode_jwt_payload(access_token)
        mobile = jwt_d.get('mobilePhone') or jwt_d.get('userName')

    return access_token, refresh_token, clean_digits(str(mobile)) if mobile else None


def update_tokens_in_data(data, old_acc, new_acc, old_ref, new_ref):
    """بروزرسانی کامل توکن‌ها در تمامی بخش‌های JSON لینک (کوکی‌ها، localStorage و persist:root)"""
    try:
        if isinstance(data, str):
            data = json.loads(data)
        content = json.dumps(data, ensure_ascii=False)
        if old_acc and new_acc:
            content = content.replace(old_acc, new_acc)
        if old_ref and new_ref:
            content = content.replace(old_ref, new_ref)
        updated = json.loads(content)

        if "cookies" in updated and isinstance(updated["cookies"], list):
            found_acc = False
            found_ref = False
            for c in updated["cookies"]:
                if c.get("name") in ["tokenMS", "token"] and new_acc:
                    c["value"] = new_acc
                    found_acc = True
                elif c.get("name") == "refresh_token" and new_ref:
                    c["value"] = new_ref
                    found_ref = True
            if new_acc and not found_acc:
                updated["cookies"].append({"name": "tokenMS", "value": new_acc, "domain": ".okala.com", "path": "/", "secure": True, "sameSite": "None"})
                updated["cookies"].append({"name": "token", "value": new_acc, "domain": ".okala.com", "path": "/", "secure": True, "sameSite": "None"})
            if new_ref and not found_ref:
                updated["cookies"].append({"name": "refresh_token", "value": new_ref, "domain": ".okala.com", "path": "/", "secure": True, "sameSite": "None"})

        for origin in updated.get("origins", []):
            for item in origin.get("localStorage", []):
                if item.get("name") == "tokenMS" and new_acc:
                    item["value"] = new_acc
                elif item.get("name") == "persist:root" and new_acc:
                    try:
                        p_root = json.loads(item["value"])
                        if "user" in p_root:
                            u_outer = json.loads(p_root["user"])
                            if "user" in u_outer and isinstance(u_outer["user"], dict):
                                u_outer["user"]["token"] = new_acc
                                p_root["user"] = json.dumps(u_outer, ensure_ascii=False)
                                item["value"] = json.dumps(p_root, ensure_ascii=False)
                    except Exception:
                        pass
        return updated
    except Exception:
        return data


class OkalaAPI:
    def __init__(self, custom_headers=None, proxies_list=None):
        self.request_logs = []
        self.proxies_list = proxies_list or []
        if custom_headers:
            self.base_headers = custom_headers.copy()
        else:
            self.base_headers = {
                'accept': 'application/json, text/plain, */*',
                'source': 'okala',
                'ui-version': '2.0',
                'origin': 'https://www.okala.com',
                'User-Agent': random.choice(USER_AGENTS),
                'sec-ch-ua': '"Chromium";v="137", "Not/A)Brand";v="24"',
                'sec-ch-ua-mobile': '?1',
                'sec-ch-ua-platform': '"Android"',
            }

    def log_request(self, method, url, status_code, response_text, proxy_used=None):
        timestamp = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
        p_str = mask_proxy(proxy_used)
        self.request_logs.append(
            f"[{timestamp}] {method} {url} | Proxy: {p_str}\n"
            f"Status: {status_code}\n"
            f"Response: {response_text}\n"
            f"{'-'*50}\n"
        )
        if len(self.request_logs) > 4000:
            self.request_logs = self.request_logs[-3000:]

    def make_request(self, method, url, access_token=None, proxy_dict=None, keep_session_ids=False, fast_mode=False, **kwargs):
        headers = self.base_headers.copy()
        if not keep_session_ids:
            headers['X-Correlation-Id'] = str(uuid.uuid4())
            headers['X-User-Unique-Id'] = str(uuid.uuid4())
            headers['session-id'] = str(uuid.uuid4())
        if access_token:
            headers['Authorization'] = f'Bearer {access_token}'
        if 'headers' in kwargs:
            headers.update(kwargs.pop('headers'))

        timeout_val = 12 if fast_mode else 18
        start_idx = random.randint(0, max(len(self.proxies_list) - 1, 0))
        max_attempts = max(min(len(self.proxies_list), 5), 3)

        for attempt in range(max_attempts):
            if attempt == 0 and proxy_dict:
                current_proxy = proxy_dict
            else:
                current_proxy = get_proxy_by_index(self.proxies_list, start_idx + attempt) or proxy_dict

            try:
                if not fast_mode:
                    time.sleep(random.uniform(0.1, 0.3))
                res = requests.request(method, url, headers=headers, proxies=current_proxy, timeout=timeout_val, **kwargs)
                self.log_request(method, f"{url} (Attempt {attempt+1})", res.status_code, res.text[:500], current_proxy)
                if res.status_code == 200:
                    try:
                        return 200, res.json()
                    except Exception:
                        return 200, {}
                elif res.status_code in [400, 401]:
                    return res.status_code, res.text
                elif res.status_code in [403, 407, 429, 500, 502, 503, 504]:
                    continue
                else:
                    return res.status_code, res.text
            except Exception as e:
                self.log_request(method, f"{url} (Attempt {attempt+1})", "PROXY_OR_NET_ERROR", str(e), current_proxy)
                continue
        return 0, "Network/Proxy Error (All attempts failed)"

    def refresh_token_sequential_proxy(self, refresh_token, start_proxy_idx=0):
        """
        دریافت توکن جدید با چرخش ترتیبی روی پروکسی‌های بعدی در صورت بروز خطای پروکسی.
        خروجی: (state, new_access_token, new_refresh_token, status_code, raw_response)
        """
        if not refresh_token:
            return "unrecoverable", None, None, "NO_TOKEN", "Refresh token is empty"

        url = "https://apigateway.okala.com/api/v1/accounts/tokens"
        data = {
            "grant_type": "refresh_token",
            "client_id": "customer_client_id",
            "client_secret": "u_M{'57j!%LI21#",
            "scope": "offline_access",
            "refresh_token": refresh_token
        }
        total_proxies = len(self.proxies_list)
        max_tries = max(min(total_proxies, 6), 3)
        last_status = 0
        last_resp = "No response"

        for step in range(max_tries):
            current_proxy = get_proxy_by_index(self.proxies_list, start_proxy_idx + step) if total_proxies > 0 else None
            headers = self.base_headers.copy()
            headers["content-type"] = "application/x-www-form-urlencoded"
            headers['X-Correlation-Id'] = str(uuid.uuid4())
            headers['X-User-Unique-Id'] = str(uuid.uuid4())
            headers['session-id'] = str(uuid.uuid4())

            try:
                res = requests.post(url, headers=headers, data=data, proxies=current_proxy, timeout=12)
                self.log_request('POST', f"{url} (ProxyStep {step+1})", res.status_code, res.text[:500], current_proxy)
                last_status = res.status_code
                last_resp = res.text

                if res.status_code == 200:
                    resp_json = res.json()
                    new_acc = resp_json.get('access_token')
                    new_ref = resp_json.get('refresh_token')
                    if new_acc:
                        return "success", new_acc, new_ref, 200, resp_json
                    return "unrecoverable", None, None, 200, res.text
                elif res.status_code in [400, 401]:
                    return "unrecoverable", None, None, res.status_code, res.text
                else:
                    continue
            except Exception as e:
                self.log_request('POST', f"{url} (ProxyStep {step+1})", "PROXY_ERROR", str(e), current_proxy)
                last_status = "PROXY_ERROR"
                last_resp = str(e)
                continue

        return "proxy_error", None, None, last_status, last_resp

    def check_access_token_alive(self, access_token, start_proxy_idx=0):
        """تست مستقیم سلامت Access Token از طریق سرور اکالا"""
        if not access_token:
            return "dead", 401, "No access token"
        proxy_dict = get_proxy_by_index(self.proxies_list, start_proxy_idx)
        status, resp = self.get_addresses_api(access_token, proxy_dict=proxy_dict, fast_mode=True)
        if status == 200:
            return "alive", 200, resp
        elif status in [400, 401]:
            return "dead", status, resp
        return "proxy_error", status, resp

    def verify_and_renew_account(self, access_token, refresh_token, start_proxy_idx=0):
        """بررسی همزمان Refresh و Access"""
        last_status, last_resp = 0, "Empty tokens"

        if refresh_token:
            r_state, new_acc, new_ref, r_status, r_resp = self.refresh_token_sequential_proxy(refresh_token, start_proxy_idx)
            last_status, last_resp = r_status, r_resp
            if r_state == "success" and new_acc:
                return "refreshed", new_acc, (new_ref or refresh_token), 200, r_resp
            elif r_state == "proxy_error" and not access_token:
                return "proxy_error", None, None, r_status, r_resp

        if access_token:
            a_state, a_status, a_resp = self.check_access_token_alive(access_token, start_proxy_idx)
            if a_state == "alive":
                return "access_only", access_token, (refresh_token or ""), 200, a_resp
            elif a_state == "proxy_error":
                return "proxy_error", None, None, a_status, a_resp

        return "unrecoverable", None, None, last_status, last_resp

    def check_discount_api(self, token, uid, proxy_dict=None, fast_mode=True):
        url = f"https://apigateway.okala.com/api/discount/v1/discounts/customer/{uid}"
        return self.make_request('GET', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode)

    def get_addresses_api(self, token, proxy_dict=None, fast_mode=True):
        url = "https://apigateway.okala.com/api/v1/accounts/userprofile/getcustomeraddresseswithpaging?pageIndex=1&pageSize=15"
        return self.make_request('GET', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode)

    def get_address_react_api(self, token, customer_id, proxy_dict=None, fast_mode=True):
        url = 'https://apigateway.okala.com/api/voyager/CustomerAddress/CustomerAddressForReact'
        return self.make_request('GET', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode, params={'customerId': customer_id})

    def add_address_api(self, token, customer_id, addr_data: dict, proxy_dict=None, fast_mode=True):
        """
        ساخت و ثبت آدرس در اکانت دقیقاً بر اساس اطلاعات فایل Main (9).py
        """
        url = 'https://apigateway.okala.com/api/voyager/C/CustomerAccount/AddAddress/'
        plaque_val = addr_data.get('plaque') or '1'
        unit_val = addr_data.get('unit') or '1'
        address_text = addr_data.get('address')
        if not address_text or not str(address_text).strip():
            address_text = 'آدرس ثبت شده از نقشه'

        payload = {
            'id': 0,
            'customerId': customer_id,
            'mobilePhone': '',
            'ShoppingSectorPartId': '0',
            'shoppingSectorId': '0',
            'plaque': str(plaque_val),
            'unit': str(unit_val),
            'lat': float(addr_data.get('lat', 35.69975)),
            'lng': float(addr_data.get('lng', 51.33551)),
            'title': None,
            'addressTypeId': 3,
            'oprationDuration': random.randint(10000, 20000),
            'address': str(address_text),
            'mapPlatform': 'ParsiMap'
        }
        if addr_data.get('cityId'):
            payload['cityId'] = int(addr_data['cityId'])

        status, res = self.make_request('POST', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode, json=payload)
        if status not in (200, 401) and 'cityId' not in payload:
            payload['cityId'] = 129
            status, res = self.make_request('POST', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode, json=payload)
        return status, res

    def delete_address_api(self, token, address_id, proxy_dict=None, fast_mode=True):
        url = f'https://apigateway.okala.com/api/voyager/C/CustomerAccount/DeleteAddress/{address_id}/'
        return self.make_request('DELETE', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode)

    def get_orders_api(self, token, proxy_dict=None, keep_session_ids=False, fast_mode=True, customer_id=None, data_dict=None):
        uid = customer_id or get_numeric_customer_id_from_token(token, data_dict)
        url = "https://apigateway.okala.com/api/v1/customerorders/list"
        params = {"PageNumber": "1", "PageSize": "10"}
        if uid and int(uid) > 0:
            params["customerId"] = str(uid)
        extra_headers = {
            "X-Skip-Authorization": "false",
            "advertising_id": "null",
            "idfa": "null",
            "metrix_user_id": "null"
        }
        return self.make_request(
            'GET',
            url,
            access_token=token,
            proxy_dict=proxy_dict,
            keep_session_ids=keep_session_ids,
            fast_mode=fast_mode,
            params=params,
            headers=extra_headers
        )


def parse_orders_response(status, response_data):
    if status == 200 and isinstance(response_data, dict):
        if response_data.get("hasValidationError") is True or response_data.get("success") is False:
            return False, False, 0
        data = response_data.get('data')
        if data is None:
            return True, False, 0
        if isinstance(data, list):
            return True, len(data) > 0, len(data)
        elif isinstance(data, dict):
            total_records = data.get('totalRecords')
            if total_records is not None:
                try:
                    tr_int = int(total_records)
                    if tr_int > 0:
                        return True, True, tr_int
                except (ValueError, TypeError):
                    pass
            total_count = data.get('totalCount')
            if total_count is not None:
                try:
                    tc_int = int(total_count)
                    if tc_int > 0:
                        return True, True, tc_int
                except (ValueError, TypeError):
                    pass
            items_field = data.get('items')
            if isinstance(items_field, dict):
                orders_list = items_field.get('orders') or items_field.get('items') or []
                if isinstance(orders_list, list):
                    return True, len(orders_list) > 0, len(orders_list)
            elif isinstance(items_field, list):
                return True, len(items_field) > 0, len(items_field)
            orders = data.get('orders') or []
            if isinstance(orders, list):
                return True, len(orders) > 0, len(orders)
        return True, False, 0
    return False, False, 0


def parse_addresses_response(status, response_data):
    if status == 200 and isinstance(response_data, dict):
        addresses = response_data.get('data', {}).get('customerAddressResponseItems', [])
        if isinstance(addresses, list):
            return True, len(addresses) > 0, len(addresses)
        return True, False, 0
    return False, False, 0


def check_order_history_sync(api_instance, token, proxy_dict):
    status, response_data = api_instance.get_orders_api(token, proxy_dict=proxy_dict, keep_session_ids=True, fast_mode=False)
    ok, has_orders, count = parse_orders_response(status, response_data)
    return ok, has_orders, count, status, response_data


async def send_step_log(bot, chat_id, title: str, status_code, raw_response, proxy_dict=None, extra_logs=None):
    """ارسال ایمن گزارش و پاسخ سرور پس از هر عملیات"""
    p_str = html.escape(mask_proxy(proxy_dict))
    raw_str = json.dumps(raw_response, ensure_ascii=False) if isinstance(raw_response, (dict, list)) else str(raw_response)
    escaped_resp = html.escape(raw_str[:700])

    log_text = (
        f"📋 <b>{html.escape(title)}</b>\n"
        f"🌐 پروکسی: <code>{p_str}</code>\n"
        f"📡 کد وضعیت: <code>{html.escape(str(status_code))}</code>\n"
        f"📥 پاسخ سرور:\n<pre>{escaped_resp}</pre>"
    )
    if extra_logs:
        escaped_extra = html.escape("".join(extra_logs)[-800:])
        log_text += f"\n🔎 <b>جزئیات تلاش‌ها:</b>\n<pre>{escaped_extra}</pre>"

    try:
        await bot.send_message(chat_id=chat_id, text=log_text, parse_mode='HTML')
    except Exception as e:
        logging.error(f"Error sending step log: {e}")


# ==========================================
# تبدیل دیتا برای وب
# ==========================================
def format_for_injector(auth_data):
    access_token = auth_data.get("access_token", "")
    refresh_token = auth_data.get("refresh_token", "")
    user_info = auth_data.get("UserInfo", {})
    jwt_data = decode_jwt_payload(access_token)

    uid_val = user_info.get("Id") or jwt_data.get("userId") or 0
    alt_id = user_info.get("AlternativeId") or jwt_data.get("cerberusId") or ""
    alt_cust_id = user_info.get("AlternativeCustomerId") or jwt_data.get("alternativeCustomerId") or 0
    mobile = clean_digits(str(user_info.get("MobilePhone") or jwt_data.get("mobilePhone") or ""))

    user_dict = {
        "id": uid_val,
        "alternativeId": alt_id,
        "alternativeCustomerId": alt_cust_id,
        "firstName": user_info.get("FirstName", "کاربر"),
        "lastName": user_info.get("LastName", "اکالا"),
        "birthDate": "",
        "genderCode": user_info.get("GenderCode", 1),
        "emailAddress": user_info.get("EmailAddress", ""),
        "userName": user_info.get("UserName", mobile),
        "mobilePhone": mobile,
        "stateCode": user_info.get("StateCode", 1),
        "customerIsLoggedInForFirstTime": user_info.get("CustomerIsLoggedInForFirstTime", False),
        "firstLoginDateTime": user_info.get("FirstLoginDateTime", ""),
        "state": user_info.get("State", False),
        "hasAddress": user_info.get("HasAddress", False),
        "birthDateEpoch": user_info.get("BirthDateEpoch", 0)
    }

    user_url_encoded = urllib.parse.quote(json.dumps(user_dict, ensure_ascii=False))
    persist_user_inner = user_dict.copy()
    persist_user_inner["token"] = access_token

    persist_root_dict = {
        "user": json.dumps({"user": persist_user_inner, "discountCode": None}, ensure_ascii=False),
        "cart": json.dumps({"cartData": [], "totalCartsCount": 0, "showDrawer": False, "cartTotalPrice": 0}),
        "mapInfo": json.dumps({"defaultViewPort": {"latitude": 35.69976, "longitude": 51.33808, "id": 129, "name": "تهران"}, "viewport": {"latitude": 35.69976, "longitude": 51.33808}, "selectedCity": {"id": 129, "name": "تهران", "lat": 35.69975, "lng": 51.33551}, "mapCityName": "تهران"}, ensure_ascii=False),
        "eventData": json.dumps({"isLoggedIn": True, "platform": "web", "viewedLayersCount": 0, "activeDiscountCodesCount": 0, "sessionLayersViewedCount": 0}),
        "_persist": json.dumps({"version": -1, "rehydrated": True})
    }

    persist_root_str = json.dumps(persist_root_dict, ensure_ascii=False)

    return {
        "cookies": [
            {"name": "tokenMS", "value": access_token, "domain": ".okala.com", "path": "/", "secure": True, "sameSite": "None"},
            {"name": "token", "value": access_token, "domain": ".okala.com", "path": "/", "secure": True, "sameSite": "None"},
            {"name": "refresh_token", "value": refresh_token, "domain": ".okala.com", "path": "/", "secure": True, "sameSite": "None"}
        ],
        "origins": [{
            "origin": "https://www.okala.com",
            "localStorage": [
                {"name": "tokenMS", "value": access_token}, {"name": "user", "value": user_url_encoded},
                {"name": "city_name", "value": "تهران"}, {"name": "city_id", "value": "129"},
                {"name": "persist:root", "value": persist_root_str}
            ]
        }]
    }


async def build_phone_to_link_map() -> dict:
    """ساخت نقشه سریع از شماره تلفن به آخرین لینک فعال در دیتابیس"""
    phone_to_latest_link = {}
    try:
        raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
        for item in raw_logs:
            try:
                entry = json.loads(item)
                p = clean_digits(str(entry.get('phone', '')))
                if p and entry.get('link'):
                    phone_to_latest_link[p] = entry['link']
            except Exception:
                pass
    except Exception:
        pass
    return phone_to_latest_link


async def ensure_permanent_link_for_db_account(phone: str, old_acc: str, access_token: str, old_ref: str, refresh_token: str, phone_to_latest_link: dict) -> str:
    """اطمینان از وجود و بروز بودن لینک دائمی برای اکانت دیتابیس"""
    link = phone_to_latest_link.get(phone) or await redis_client.get(f"phone_active_link:{phone}")
    link_id = link.split('/acc/')[-1].strip() if (link and '/acc/' in link) else None

    if link_id and await redis_client.exists(f"acc_link:{link_id}"):
        if access_token != old_acc:
            old_l_data = await redis_client.get(f"acc_link:{link_id}")
            updated_l = update_tokens_in_data(old_l_data, old_acc, access_token, old_ref, refresh_token)
            await redis_client.set(f"acc_link:{link_id}", json.dumps(updated_l, ensure_ascii=False))
        final_url = f"{WEB_DOMAIN}/acc/{link_id}"
        await redis_client.set(f"phone_active_link:{phone}", final_url)
        return final_url
    else:
        if not link_id:
            link_id = str(uuid.uuid4())[:12]
        auth_data = {"access_token": access_token, "refresh_token": refresh_token or "", "UserInfo": {"MobilePhone": phone}}
        injection_json = format_for_injector(auth_data)
        await redis_client.set(f"acc_link:{link_id}", json.dumps(injection_json, ensure_ascii=False))
        final_url = f"{WEB_DOMAIN}/acc/{link_id}"
        await redis_client.set(f"phone_active_link:{phone}", final_url)
        return final_url


# ==========================================
# استخراج آدرس از لینک الگو، متن دلخواه یا پیش‌فرض (بر اساس Main 9)
# ==========================================
async def resolve_address_config_from_input(raw_text: str, proxies_list: list) -> tuple:
    """
    تشخیص هوشمند آدرس ورودی برای ساخت آدرس:
    ۱. اگر کاربر «پیشفرض» یا «default» بفرستد -> آدرس پیش‌فرض تهران.
    ۲. اگر کاربر لینک اکانت بفرستد -> استخراج اولین آدرس ثبت‌شده در آن اکانت (یا mapInfo آن مطابق Main 9).
    ۳. اگر کاربر متن آدرس یا فرمت lat,lng,address بفرستد -> ساخت آدرس با همان مشخصات.
    خروجی: (addr_dict, description_str, error_str)
    """
    text = (raw_text or "").strip()
    if not text or text in ["پیشفرض", "پیش‌فرض", "default", "Default", "تهران", "1"]:
        return DEFAULT_TEHRAN_ADDRESS.copy(), "آدرس پیش‌فرض تهران (خیابان آزادی)", None

    # بررسی اینکه آیا ورودی یک لینک اکانت است
    url_match = re.search(r'(https?://[^\s]+)', text)
    if url_match:
        target_url = url_match.group(1).strip()
        data = None
        if '/acc/' in target_url:
            lid = target_url.split('/acc/')[-1].strip()
            raw_redis = await redis_client.get(f"acc_link:{lid}")
            if raw_redis:
                try:
                    data = json.loads(raw_redis)
                except Exception:
                    pass
        if not data:
            try:
                loop = asyncio.get_running_loop()
                res = await loop.run_in_executor(executor, lambda: requests.get(target_url, timeout=15))
                if res.status_code == 200:
                    data = res.json()
            except Exception as e:
                return None, None, f"❌ خطا در دریافت اطلاعات از لینک الگو: {e}"

        if not isinstance(data, dict):
            return None, None, "❌ لینک ارسالی معتبر نیست یا اطلاعات اکانت در آن یافت نشد."

        api = OkalaAPI(proxies_list=proxies_list)
        t_acc, t_ref, _ = extract_tokens_from_json_data(data)
        loop = asyncio.get_running_loop()

        if not t_acc and t_ref:
            st, new_acc, new_ref, _, _ = await loop.run_in_executor(executor, api.refresh_token_sequential_proxy, t_ref, 0)
            if st == "success" and new_acc:
                t_acc = new_acc
                t_ref = new_ref or t_ref

        if not t_acc:
            return None, None, "❌ توکن معتبری در لینک الگو یافت نشد."

        t_uid = get_numeric_customer_id_from_token(t_acc, data)
        proxy_dict = get_proxy_by_index(proxies_list, 0)

        status, addr_res = await loop.run_in_executor(executor, api.get_address_react_api, t_acc, t_uid, proxy_dict, True)
        if status == 401 and t_ref:
            st, new_acc, new_ref, _, _ = await loop.run_in_executor(executor, api.refresh_token_sequential_proxy, t_ref, 0)
            if st == "success" and new_acc:
                t_acc = new_acc
                t_uid = get_numeric_customer_id_from_token(t_acc, data)
                status, addr_res = await loop.run_in_executor(executor, api.get_address_react_api, t_acc, t_uid, proxy_dict, True)

        template_addr = None
        if status == 200 and isinstance(addr_res, dict) and isinstance(addr_res.get('data'), list) and len(addr_res['data']) > 0:
            template_addr = addr_res['data'][0]
        else:
            status_p, addr_p = await loop.run_in_executor(executor, api.get_addresses_api, t_acc, proxy_dict, True)
            paged_items = (addr_p.get('data') or {}).get('customerAddressResponseItems') if isinstance(addr_p, dict) else None
            if status_p == 200 and isinstance(paged_items, list) and len(paged_items) > 0:
                template_addr = paged_items[0]

        if template_addr and isinstance(template_addr, dict):
            final_addr = {
                'lat': float(template_addr.get('lat', 35.69975)),
                'lng': float(template_addr.get('lng', 51.33551)),
                'address': template_addr.get('address') or 'آدرس ثبت شده از نقشه',
                'plaque': str(template_addr.get('plaque') or '1'),
                'unit': str(template_addr.get('unit') or '1'),
                'cityId': template_addr.get('cityId') or 129
            }
            return final_addr, f"استخراج‌شده از اکانت الگو ({final_addr['address'][:40]})", None

        # Fallback به mapInfo داخل localStorage اکانت الگو (مطابق Main 9)
        lat, lng = 35.69975, 51.33551
        addr_text = "تهران، آدرس استخراج شده از نقشه"
        city_id = 129
        try:
            for origin in (data.get('origins') or []):
                if isinstance(origin, dict):
                    for item in (origin.get('localStorage') or []):
                        if isinstance(item, dict) and item.get('name') == 'mapInfo':
                            map_info = json.loads(item.get('value') or '{}')
                            if isinstance(map_info, dict) and isinstance(map_info.get('selectedCity'), dict):
                                lat = float(map_info['selectedCity'].get('lat', lat))
                                lng = float(map_info['selectedCity'].get('lng', lng))
                                addr_text = map_info['selectedCity'].get('name', addr_text) + "، خیابان اصلی"
                                city_id = map_info['selectedCity'].get('id') or 129
        except Exception:
            pass

        final_addr = {
            'lat': lat,
            'lng': lng,
            'address': addr_text,
            'plaque': '1',
            'unit': '1',
            'cityId': city_id
        }
        return final_addr, f"استخراج‌شده از نقشه اکانت الگو ({addr_text})", None

    # بررسی فرمت مختصات سفارشی: lat,lng,address,plaque,unit
    parts = [p.strip() for p in re.split(r'[,،|]+', clean_digits(text)) if p.strip()]
    if len(parts) >= 2:
        try:
            lat_v = float(parts[0])
            lng_v = float(parts[1])
            addr_str = parts[2] if len(parts) >= 3 else 'تهران، خیابان آزادی، پلاک ۱'
            plaque_str = parts[3] if len(parts) >= 4 else '1'
            unit_str = parts[4] if len(parts) >= 5 else '1'
            return {
                'lat': lat_v,
                'lng': lng_v,
                'address': addr_str,
                'plaque': str(plaque_str),
                'unit': str(unit_str),
                'cityId': 129
            }, f"مختصات سفارشی ({lat_v}, {lng_v}) - {addr_str[:30]}", None
        except ValueError:
            pass

    # اگر کاربر فقط متن آدرس فرستاده باشد
    custom_addr = DEFAULT_TEHRAN_ADDRESS.copy()
    custom_addr['address'] = text
    return custom_addr, f"آدرس متنی سفارشی ({text[:40]})", None


# ==========================================
# نوسازی تمام توکن‌ها، احیای دائمی لینک‌ها و چرخش خودکار پس‌زمینه
# ==========================================
async def process_refresh_and_revive_all(bot, chat_id, acc_keys, is_auto_cycle=False):
    if refresh_task_lock.locked():
        if not is_auto_cycle:
            await bot.send_message(chat_id=chat_id, text="⚠️ یک عملیات نوسازی هم‌اکنون در حال اجراست. لطفاً تا پایان آن صبر کنید.")
        return

    async with refresh_task_lock:
        loop = asyncio.get_running_loop()
        proxies_list = await get_all_proxies_from_db()
        api = OkalaAPI(proxies_list=proxies_list)
        ts = int(time.time())

        if not proxies_list and not is_auto_cycle:
            await bot.send_message(
                chat_id=chat_id,
                text="⚠️ <b>هیچ پروکسی‌ای در سیستم ثبت نشده است!</b>\n"
                     "عملیات بدون پروکسی ادامه می‌یابد اما توصیه می‌شود ابتدا پروکسی تنظیم کنید.",
                parse_mode='HTML'
            )

        phone_to_link_id = {}
        raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
        for item in raw_logs:
            try:
                entry = json.loads(item)
                p = clean_digits(str(entry.get('phone', '')))
                l_url = entry.get('link', '')
                if p and '/acc/' in l_url:
                    phone_to_link_id[p] = l_url.split('/acc/')[-1].strip()
            except Exception:
                pass

        existing_link_keys = await redis_client.keys("acc_link:*")
        for l_key in existing_link_keys:
            try:
                lid = l_key.replace("acc_link:", "")
                l_data = await redis_client.get(l_key)
                if l_data:
                    d_json = json.loads(l_data)
                    origins = d_json.get("origins", [])
                    if origins:
                        for item in origins[0].get("localStorage", []):
                            if item.get("name") == "user":
                                u_obj = json.loads(urllib.parse.unquote(item.get("value")))
                                p = clean_digits(str(u_obj.get("mobilePhone", "")))
                                if p:
                                    phone_to_link_id[p] = lid
                                break
            except Exception:
                pass

        total = len(acc_keys)
        title_prefix = "⏱ [چرخش خودکار دوره‌ای]" if is_auto_cycle else "♻️"
        progress_msg = await bot.send_message(
            chat_id=chat_id,
            text=f"{title_prefix} شروع نوسازی توکن‌ها و ذخیره آخرین Access/Refresh برای <b>{total}</b> اکانت...\n⏳ لطفاً منتظر بمانید.",
            parse_mode='HTML'
        )

        detail_logs = []
        active_links_list = []
        unrecoverable_phones = []
        stats = {"updated": 0, "recreated": 0, "access_only": 0, "unrecoverable": 0, "proxy_error": 0}
        done = 0
        last_edit_time = 0
        lock = asyncio.Lock()
        sem = asyncio.Semaphore(20)

        async def _worker(idx, key):
            nonlocal done, last_edit_time
            raw_phone = key.replace("account:", "")
            phone = clean_digits(raw_phone)

            async with sem:
                try:
                    token_data = await redis_client.hgetall(key)
                    old_acc = token_data.get("access_token", "")
                    old_ref = token_data.get("refresh_token", "")

                    if raw_phone != phone and phone:
                        await redis_client.hset(f"account:{phone}", mapping={"access_token": old_acc, "refresh_token": old_ref})
                        await redis_client.delete(key)
                        key = f"account:{phone}"

                    if not old_ref and not old_acc:
                        async with lock:
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} | فاقد هرگونه توکن (غیرقابل بازگشت)\n")
                            stats["unrecoverable"] += 1
                            unrecoverable_phones.append(raw_phone)
                            done += 1
                        return

                    res_type, final_acc, final_ref, status_code, raw_resp = await loop.run_in_executor(
                        executor, api.verify_and_renew_account, old_acc, old_ref, idx
                    )

                    if res_type in ["refreshed", "access_only"] and final_acc:
                        await redis_client.hset(key, mapping={"access_token": final_acc, "refresh_token": final_ref or ""})

                        link_id = phone_to_link_id.get(phone)
                        if not link_id:
                            active_url = await redis_client.get(f"phone_active_link:{phone}") or await redis_client.get(f"phone_active_link:{raw_phone}")
                            if active_url and '/acc/' in active_url:
                                link_id = active_url.split('/acc/')[-1].strip()

                        link_recreated = False
                        if link_id and await redis_client.exists(f"acc_link:{link_id}"):
                            old_link_str = await redis_client.get(f"acc_link:{link_id}")
                            updated_data = update_tokens_in_data(old_link_str, old_acc, final_acc, old_ref, final_ref)
                            await redis_client.set(f"acc_link:{link_id}", json.dumps(updated_data, ensure_ascii=False))
                        else:
                            if not link_id:
                                link_id = str(uuid.uuid4())[:12]
                            auth_data = {
                                "access_token": final_acc,
                                "refresh_token": final_ref or "",
                                "UserInfo": {"MobilePhone": phone, "HasName": True}
                            }
                            injection_json = format_for_injector(auth_data)
                            await redis_client.set(f"acc_link:{link_id}", json.dumps(injection_json, ensure_ascii=False))
                            link_recreated = True

                        final_url = f"{WEB_DOMAIN}/acc/{link_id}"
                        await redis_client.set(f"phone_active_link:{phone}", final_url)

                        async with lock:
                            if res_type == "access_only":
                                stats["access_only"] += 1
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 🟢 {phone} | رفرش‌توکن نامعتبر بود اما Access Token فعال است: {final_url}\n")
                            elif link_recreated:
                                stats["recreated"] += 1
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 🆕 {phone} | توکن چرخش یافت + لینک دائمی مجدداً تولید شد: {final_url}\n")
                            else:
                                stats["updated"] += 1
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ✅ {phone} | آخرین Access و Refresh ذخیره و لینک آپدیت شد: {final_url}\n")
                            active_links_list.append({"phone": phone, "link": final_url})

                    elif res_type == "unrecoverable":
                        async with lock:
                            stats["unrecoverable"] += 1
                            unrecoverable_phones.append(phone)
                            if raw_phone != phone:
                                unrecoverable_phones.append(raw_phone)
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 💀 {phone} | غیرقابل بازگشت (کد: {status_code}) | پاسخ: {str(raw_resp)[:200]}\n")

                    else:
                        async with lock:
                            stats["proxy_error"] += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} | خطای شبکه/پروکسی پس از چرخش پروکسی‌ها (کد: {status_code})\n")

                    async with lock:
                        done += 1
                        now = time.time()
                        if (now - last_edit_time >= 2.5) or (done == total):
                            last_edit_time = now
                            try:
                                await progress_msg.edit_text(
                                    f"{title_prefix} <b>در حال چرخش توکن‌ها و احیای دائمی لینک‌ها...</b>\n"
                                    f"📊 پیشرفت: <b>{done}/{total}</b>\n"
                                    f"✅ رفرش و آپدیت کامل (Access+Refresh): <b>{stats['updated']}</b>\n"
                                    f"🆕 تولید مجدد لینک حذف‌شده: <b>{stats['recreated']}</b>\n"
                                    f"🟢 فعال فقط با Access Token: <b>{stats['access_only']}</b>\n"
                                    f"💀 غیرقابل بازگشت (هر دو باطل): <b>{stats['unrecoverable']}</b>\n"
                                    f"⚠️ خطای پروکسی/شبکه: <b>{stats['proxy_error']}</b>",
                                    parse_mode='HTML'
                                )
                            except Exception:
                                pass

                except Exception as e:
                    async with lock:
                        stats["proxy_error"] += 1
                        done += 1
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطای غیرمنتظره برای {phone}: {e}\n")

        await asyncio.gather(*[_worker(i, k) for i, k in enumerate(acc_keys)])

        await redis_client.set("settings:last_auto_refresh", datetime.now().strftime("%Y-%m-%d %H:%M:%S"))

        try:
            await progress_msg.delete()
        except Exception:
            pass

        await redis_client.delete("temp:unrecoverable_accounts")
        if unrecoverable_phones:
            await redis_client.sadd("temp:unrecoverable_accounts", *unrecoverable_phones)

        if active_links_list:
            links_txt = f"🔗 لیست لینک‌های دائمی با توکن نوسازی‌شده (تعداد: {len(active_links_list)})\n" + "=" * 50 + "\n\n"
            for idx, item in enumerate(active_links_list, 1):
                links_txt += f"{idx}. 📱 شماره: {item['phone']}\n🔗 {item['link']}\n\n"
            links_io = io.BytesIO(links_txt.encode('utf-8'))
            await bot.send_document(
                chat_id=chat_id,
                document=links_io,
                filename=f"Permanent_Refreshed_Links_{ts}.txt",
                caption=f"✅ فایل لینک‌های دائمی و نوسازی‌شده ({len(active_links_list)} اکانت فعال)"
            )

        try:
            full_log = f"=== گزارش کامل نوسازی توکن‌ها و احیای لینک‌ها | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
            full_log += (
                f"کل اکانت‌ها: {total} | آپدیت‌شده: {stats['updated']} | لینک مجدد: {stats['recreated']} | "
                f"فعال با Access: {stats['access_only']} | غیرقابل بازگشت: {stats['unrecoverable']} | خطای پروکسی: {stats['proxy_error']}\n"
            )
            full_log += "=" * 60 + "\n\n"
            full_log += "=== خلاصه وضعیت تک‌تک شماره‌ها ===\n"
            full_log += "".join(detail_logs)
            full_log += "\n\n=== لاگ کامل درخواست‌ها و پاسخ‌های سرور (HTTP Requests) ===\n"
            full_log += "".join(api.request_logs)

            log_io = io.BytesIO(full_log.encode('utf-8'))
            await bot.send_document(
                chat_id=chat_id,
                document=log_io,
                filename=f"Refresh_All_Requests_Log_{ts}.txt",
                caption="📄 گزارش کامل تمامی درخواست‌ها و پاسخ‌های دریافتی از سرور"
            )
        except Exception as e:
            logging.error(f"Error sending refresh full log: {e}")

        summary_text = (
            f"✅ <b>عملیات چرخش توکن‌ها و ذخیره آخرین Access/Refresh پایان یافت.</b>\n\n"
            f"👥 <b>کل اکانت‌های بررسی شده:</b> <code>{total}</code>\n"
            f"♻️ <b>نوسازی کامل (Access + Refresh جدید):</b> <code>{stats['updated']}</code>\n"
            f"🆕 <b>تولید مجدد لینک دائمی حذف‌شده:</b> <code>{stats['recreated']}</code>\n"
            f"🟢 <b>سالم فقط با Access Token فعلی:</b> <code>{stats['access_only']}</code>\n"
            f"⚠️ <b>خطای شبکه/پروکسی (بدون تغییر):</b> <code>{stats['proxy_error']}</code>\n"
            f"💀 <b>اکانت‌های غیرقابل بازگشت (هر دو توکن باطل):</b> <code>{stats['unrecoverable']}</code>\n"
        )

        if unrecoverable_phones:
            unique_dead_count = len(set(clean_digits(p) for p in unrecoverable_phones))
            summary_text += (
                f"\n❓ <b>آیا مایلید <code>{unique_dead_count}</code> اکانت غیرقابل بازگشت به طور کامل از دیتابیس حذف شوند؟</b>"
            )
            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton(f"🗑 بله، حذف {unique_dead_count} اکانت سوخته", callback_data="admin_confirm_delete_dead")],
                [InlineKeyboardButton("❌ خیر، نادیده بگیر", callback_data="admin_cancel_delete_dead")],
                [InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]
            ])
        else:
            kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]])

        await bot.send_message(chat_id=chat_id, text=summary_text, reply_markup=kb, parse_mode='HTML')


async def auto_refresh_background_task(bot):
    """وظیفه پس‌زمینه برای چرخش خودکار رفرش‌توکن‌ها جهت جلوگیری از انقضای اکانت‌ها"""
    await asyncio.sleep(15)
    while True:
        try:
            interval_str = await redis_client.get("settings:auto_refresh_interval")
            interval = int(interval_str) if (interval_str and interval_str.isdigit()) else 43200

            if interval <= 0:
                await asyncio.sleep(60)
                continue

            last_ts_str = await redis_client.get("settings:last_auto_refresh_ts")
            last_ts = int(last_ts_str) if (last_ts_str and last_ts_str.isdigit()) else 0
            now = int(time.time())

            if now - last_ts >= interval:
                await redis_client.set("settings:last_auto_refresh_ts", str(now))
                acc_keys = await redis_client.keys("account:*")
                if acc_keys and ADMIN_IDS:
                    target_admin = ADMIN_IDS[0]
                    await process_refresh_and_revive_all(bot, target_admin, acc_keys, is_auto_cycle=True)

            await asyncio.sleep(60)
        except Exception as e:
            logging.error(f"Auto refresh loop error: {e}")
            await asyncio.sleep(60)


# ==========================================
# استخراج پرسرعت اکانت‌های خام (بدون خرید و بدون آدرس)
# ==========================================
async def process_raw_accounts_and_send_report(bot, chat_id, acc_keys):
    loop = asyncio.get_running_loop()
    proxies_list = await get_all_proxies_from_db()
    api = OkalaAPI(proxies_list=proxies_list)
    ts = int(time.time())

    if not proxies_list:
        await bot.send_message(
            chat_id=chat_id,
            text="⚠️ <b>هیچ پروکسی‌ای در سیستم تنظیم نشده است!</b>\nبررسی بدون پروکسی ادامه می‌یابد.",
            parse_mode='HTML'
        )

    phone_to_latest_link = await build_phone_to_link_map()

    total = len(acc_keys)
    progress_msg = await bot.send_message(
        chat_id=chat_id,
        text=f"⚡ شروع اسکن موازی و پرسرعت <b>{total}</b> اکانت (۲۰ اکانت همزمان)...\n⏳ لطفاً منتظر بمانید.",
        parse_mode='HTML'
    )

    detail_logs = []
    raw_results = []
    stats = {"raw": 0, "has_address": 0, "has_orders": 0, "failed": 0}
    done = 0
    last_edit_time = 0
    lock = asyncio.Lock()
    sem = asyncio.Semaphore(20)

    def _check_raw_sync(acc_token, ref_token, p_dict, phone, idx):
        proxy_ip = mask_proxy(p_dict)
        log_line = f"[{time.strftime('%H:%M:%S')}] 📱 {phone} | پروکسی اولیه: {proxy_ip}\n"
        new_acc, new_ref = None, None

        addr_status, addr_res = api.get_addresses_api(acc_token, proxy_dict=p_dict, fast_mode=True)
        if addr_status == 401 and ref_token:
            log_line += "  ♻️ توکن منقضی — در حال رفرش با چرخش پروکسی...\n"
            st, new_acc, new_ref, _, _ = api.refresh_token_sequential_proxy(ref_token, start_proxy_idx=idx)
            if st == "success" and new_acc:
                acc_token = new_acc
                log_line += "  ✅ رفرش موفق.\n"
                addr_status, addr_res = api.get_addresses_api(acc_token, proxy_dict=p_dict, fast_mode=True)
            else:
                log_line += "  ❌ رفرش ناموفق.\n"
                return "failed", None, None, log_line

        addr_ok, has_addr, addr_count = parse_addresses_response(addr_status, addr_res)
        if not addr_ok:
            log_line += f"  ❌ خطا در استعلام آدرس (کد: {addr_status})\n"
            return "failed", new_acc, new_ref, log_line

        if has_addr:
            log_line += f"  🏠 دارای {addr_count} آدرس ثبت‌شده (رد شد)\n"
            return "has_address", new_acc, new_ref, log_line

        ord_status, ord_res = api.get_orders_api(acc_token, proxy_dict=p_dict, fast_mode=True)
        ord_ok, has_ord, ord_count = parse_orders_response(ord_status, ord_res)
        if not ord_ok:
            log_line += f"  ❌ خطا در استعلام سفارشات (کد: {ord_status})\n"
            return "failed", new_acc, new_ref, log_line

        if has_ord:
            log_line += f"  🛍 دارای {ord_count} سابقه خرید (رد شد)\n"
            return "has_orders", new_acc, new_ref, log_line

        log_line += "  ✨ اکانت کاملاً خام (بدون آدرس و بدون خرید)\n"
        return "raw", new_acc, new_ref, log_line

    async def _worker(idx, key):
        nonlocal done, last_edit_time
        phone = clean_digits(key.replace("account:", ""))
        async with sem:
            try:
                token_data = await redis_client.hgetall(key)
                access_token = token_data.get("access_token")
                refresh_token = token_data.get("refresh_token")

                if not access_token:
                    async with lock:
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} — توکن موجود نیست.\n")
                        stats["failed"] += 1
                        done += 1
                    return

                proxy_dict = get_proxy_by_index(proxies_list, idx)
                result_state, new_acc, new_ref, log_line = await loop.run_in_executor(
                    executor, _check_raw_sync, access_token, refresh_token, proxy_dict, phone, idx
                )

                old_acc = access_token
                old_ref = refresh_token
                if new_acc:
                    access_token = new_acc
                    refresh_token = new_ref or refresh_token
                    await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                link = None
                if result_state == "raw":
                    link = await ensure_permanent_link_for_db_account(phone, old_acc, access_token, old_ref, refresh_token, phone_to_latest_link)

                async with lock:
                    detail_logs.append(log_line)
                    if result_state == "raw":
                        stats["raw"] += 1
                        raw_results.append({"phone": phone, "link": link})
                    elif result_state in stats:
                        stats[result_state] += 1
                    else:
                        stats["failed"] += 1

                    done += 1
                    now = time.time()
                    if (now - last_edit_time >= 2.0) or (done == total):
                        last_edit_time = now
                        try:
                            await progress_msg.edit_text(
                                f"⚡ اسکن موازی اکانت‌های خام...\n"
                                f"✅ بررسی شده: <b>{done}/{total}</b>\n"
                                f"✨ خام (بدون خرید و آدرس): <b>{stats['raw']}</b>\n"
                                f"🏠 دارای آدرس: <b>{stats['has_address']}</b> | 🛍 دارای خرید: <b>{stats['has_orders']}</b>\n"
                                f"❌ خطا/منقضی: <b>{stats['failed']}</b>",
                                parse_mode='HTML'
                            )
                        except Exception:
                            pass
            except Exception as e:
                async with lock:
                    detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطای کلی برای {key}: {e}\n")
                    stats["failed"] += 1
                    done += 1

    await asyncio.gather(*[_worker(i, k) for i, k in enumerate(acc_keys)])

    try:
        await progress_msg.delete()
    except Exception:
        pass

    summary_caption = (
        f"📊 <b>نتیجه اسکن اکانت‌های خام:</b>\n"
        f"🔢 کل بررسی‌شده: <b>{total}</b>\n"
        f"✨ خام (بدون خرید و آدرس): <b>{stats['raw']}</b>\n"
        f"🏠 رد شده به دلیل داشتن آدرس: <b>{stats['has_address']}</b>\n"
        f"🛍 رد شده به دلیل داشتن خرید: <b>{stats['has_orders']}</b>\n"
        f"❌ خطا یا توکن سوخته: <b>{stats['failed']}</b>"
    )

    if raw_results:
        report_text = f"✨ لیست اکانت‌های خام (بدون سابقه خرید و بدون آدرس) — تعداد: {len(raw_results)}\n" + "=" * 50 + "\n\n"
        for idx, r in enumerate(raw_results, 1):
            report_text += f"{idx}. 📱 شماره: {r['phone']}\n🔗 {r['link']}\n\n"

        file_out = io.BytesIO(report_text.encode('utf-8'))
        await bot.send_document(
            chat_id=chat_id,
            document=file_out,
            filename=f"Raw_Accounts_Links_{ts}.txt",
            caption=summary_caption,
            parse_mode='HTML'
        )
    else:
        await bot.send_message(chat_id=chat_id, text=summary_caption + "\n\n➖ هیچ اکانت خامی یافت نشد.", parse_mode='HTML')

    try:
        full_log = f"=== لاگ بررسی اکانت‌های خام | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
        full_log += "".join(detail_logs)
        full_log += "\n\n=== لاگ کامل درخواست‌ها و پاسخ‌های سرور (HTTP) ===\n"
        full_log += "".join(api.request_logs)

        log_out = io.BytesIO(full_log.encode('utf-8'))
        await bot.send_document(
            chat_id=chat_id,
            document=log_out,
            filename=f"Raw_Scan_Server_Log_{ts}.txt",
            caption="📄 لاگ کامل سرور و پاسخ‌های دریافتی (بررسی آدرس و خرید)"
        )
    except Exception as e:
        logging.error(f"Error sending raw scan log: {e}")


# ==========================================
# بررسی کامل تمامی کدهای تخفیف اکانت‌های دیتابیس (پشتیبانی از چند کد همزمان در هر اکانت)
# ==========================================
async def process_discounts_and_send_report(bot, chat_id, acc_keys):
    loop = asyncio.get_running_loop()
    proxies_list = await get_all_proxies_from_db()
    api = OkalaAPI(proxies_list=proxies_list)
    ts = int(time.time())

    if not proxies_list:
        await bot.send_message(
            chat_id=chat_id,
            text="⚠️ <b>هیچ پروکسی‌ای در سیستم تنظیم نشده است!</b>\nبررسی تخفیف بدون پروکسی ادامه می‌یابد.",
            parse_mode='HTML'
        )

    phone_to_latest_link = await build_phone_to_link_map()

    total = len(acc_keys)
    progress_msg = await bot.send_message(
        chat_id=chat_id,
        text=f"⚡ شروع بررسی موازی تمامی کدهای تخفیف برای <b>{total}</b> اکانت دیتابیس (۲۰ اکانت همزمان)...\n⏳ لطفاً منتظر بمانید.",
        parse_mode='HTML'
    )

    detail_logs = []
    discount_results = []
    amount_counter = Counter()
    total_vouchers_found = 0
    multi_discount_accounts = 0
    done = 0
    last_edit_time = 0
    lock = asyncio.Lock()
    sem = asyncio.Semaphore(20)

    def _check_sync(acc_token, ref_token, uid, p_dict, phone, idx):
        proxy_ip = mask_proxy(p_dict)
        log_line = f"[{time.strftime('%H:%M:%S')}] 📱 {phone} | UUID: {uid} | پروکسی: {proxy_ip}\n"

        status, res = api.check_discount_api(acc_token, uid, proxy_dict=p_dict, fast_mode=True)
        new_acc, new_ref = None, None

        if status == 401 and ref_token:
            log_line += "  ♻️ توکن منقضی — در حال رفرش با چرخش پروکسی...\n"
            st, new_acc, new_ref, _, _ = api.refresh_token_sequential_proxy(ref_token, start_proxy_idx=idx)
            if st == "success" and new_acc:
                new_uid = get_user_id_from_token(new_acc) or uid
                status, res = api.check_discount_api(new_acc, new_uid, proxy_dict=p_dict, fast_mode=True)
                log_line += "  ✅ رفرش موفق — بررسی مجدد انجام شد.\n"
            else:
                log_line += "  ❌ رفرش ناموفق.\n"

        valid_vouchers = []
        if status == 200 and isinstance(res, dict):
            valid_vouchers = extract_all_valid_discounts(res)
            if valid_vouchers:
                summary_str = " + ".join([f"{v['label']} ({v['code']})" for v in valid_vouchers])
                log_line += f"  🎁 تخفیف یافت شد ({len(valid_vouchers)} کد فعال): {summary_str}\n"
            else:
                log_line += "  ➖ بدون کد تخفیف فعال (پاسخ 200)\n"
        elif status == 401:
            log_line += "  🔒 توکن کاملاً منقضی شده.\n"
        else:
            log_line += f"  ❌ خطا — کد پاسخ: {status}\n"

        return status, valid_vouchers, new_acc, new_ref, log_line

    async def _worker(idx, key):
        nonlocal done, last_edit_time, total_vouchers_found, multi_discount_accounts
        phone = clean_digits(key.replace("account:", ""))
        async with sem:
            try:
                token_data = await redis_client.hgetall(key)
                access_token = token_data.get("access_token")
                refresh_token = token_data.get("refresh_token")

                if not access_token and not refresh_token:
                    async with lock:
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} — توکن موجود نیست، رد شد.\n")
                        done += 1
                    return

                user_uuid = get_user_id_from_token(access_token) if access_token else None
                proxy_dict = get_proxy_by_index(proxies_list, idx)

                if not user_uuid and refresh_token:
                    st, r_acc, r_ref, _, _ = await loop.run_in_executor(
                        executor, api.refresh_token_sequential_proxy, refresh_token, idx
                    )
                    if st == "success" and r_acc:
                        access_token = r_acc
                        refresh_token = r_ref or refresh_token
                        await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})
                        user_uuid = get_user_id_from_token(access_token)

                if not user_uuid:
                    async with lock:
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} — UUID قابل استخراج نیست، رد شد.\n")
                        done += 1
                    return

                status, valid_vouchers, new_acc, new_ref, log_line = await loop.run_in_executor(
                    executor, _check_sync, access_token, refresh_token, user_uuid, proxy_dict, phone, idx
                )

                old_acc = access_token
                old_ref = refresh_token
                if new_acc:
                    access_token = new_acc
                    refresh_token = new_ref or refresh_token
                    await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                if status == 200 and valid_vouchers:
                    old_link = await ensure_permanent_link_for_db_account(phone, old_acc, access_token, old_ref, refresh_token, phone_to_latest_link)
                    max_amount_k = max((v['amount_k'] for v in valid_vouchers), default=0)
                    all_amounts_k = [v['amount_k'] for v in valid_vouchers if v['amount_k'] > 0]

                    async with lock:
                        total_vouchers_found += len(valid_vouchers)
                        if len(valid_vouchers) >= 2:
                            multi_discount_accounts += 1
                        for v in valid_vouchers:
                            amount_counter[v['label']] += 1
                        discount_results.append({
                            "phone": phone,
                            "count": len(valid_vouchers),
                            "max_amount": max_amount_k,
                            "all_amounts": all_amounts_k,
                            "vouchers": valid_vouchers,
                            "link": old_link
                        })

                async with lock:
                    detail_logs.append(log_line)
                    done += 1
                    now = time.time()
                    if (now - last_edit_time >= 2.0) or (done == total):
                        last_edit_time = now
                        try:
                            await progress_msg.edit_text(
                                f"⚡ بررسی موازی تخفیف‌های دیتابیس...\n"
                                f"✅ انجام شده: <b>{done}/{total}</b>\n"
                                f"🎁 اکانت دارای تخفیف: <b>{len(discount_results)}</b> (دارای چند کد همزمان: <b>{multi_discount_accounts}</b>)\n"
                                f"🎟 مجموع کل کدهای تخفیف یافت‌شده: <b>{total_vouchers_found}</b>",
                                parse_mode='HTML'
                            )
                        except Exception:
                            pass
            except Exception as e:
                async with lock:
                    detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطای کلی برای {key}: {e}\n")
                    done += 1

    await asyncio.gather(*[_worker(i, k) for i, k in enumerate(acc_keys)])

    discount_results.sort(key=lambda x: (x['max_amount'], x['count']), reverse=True)

    breakdown_lines = [f"▫️ تخفیف <b>{lbl}</b>: <code>{cnt}</code> کد" for lbl, cnt in amount_counter.most_common()]
    breakdown_str = ("\n📋 <b>تفکیک کل کدهای تخفیف یافت‌شده:</b>\n" + "\n".join(breakdown_lines) + "\n") if breakdown_lines else ""

    if discount_results:
        report_text = (
            f"🎁 <b>گزارش کامل بررسی تخفیف‌ها ({len(discount_results)} اکانت دارای تخفیف از {total}):</b>\n"
            f"🎟 مجموع کل کدهای تخفیف فعال: <b>{total_vouchers_found} کد</b>\n"
            f"✨ اکانت‌های دارای ۲ یا چند کد تخفیف همزمان: <b>{multi_discount_accounts} اکانت</b>\n"
            f"{breakdown_str}\n"
        )
        for r in discount_results:
            link_line = f"🔗 {r['link']}" if r['link'] else "⚠️ لینک ثبت‌شده‌ای در دیتابیس یافت نشد"
            amounts_str = " + ".join(str(a) for a in r['all_amounts']) if r['all_amounts'] else str(r['max_amount'])
            report_text += (
                f"📱 شماره: <code>{r['phone']}</code>\n"
                f"🎟 تعداد کد تخفیف: <b>{r['count']}</b> | بیشترین مبلغ: <b>{r['max_amount']} هزار تومان</b> | مبالغ تخفیف: <b>{amounts_str}</b>\n"
            )
            for idx_v, v in enumerate(r['vouchers'], 1):
                min_txt = f" | حداقل خرید: {v['min_order_toman']:,} تومان" if v['min_order_toman'] > 0 else ""
                report_text += f"   {idx_v}. 🎁 <b>{v['detail_val']}</b> | کد: <code>{html.escape(str(v['code']))}</code>{min_txt} | انقضا: <code>{html.escape(str(v['expiration']))}</code>\n"
            report_text += f"{link_line}\n{'─'*32}\n"
    else:
        report_text = f"➖ <b>هیچ تخفیفی یافت نشد.</b>\nتعداد کل اکانت‌های بررسی‌شده: {total}"

    try:
        await progress_msg.delete()
    except Exception:
        pass

    try:
        if len(report_text) > 4000:
            clean_file_text = re.sub(r'<[^>]+>', '', report_text)
            file_out = io.BytesIO(clean_file_text.encode('utf-8'))
            summary_msg = (
                f"✅ <b>بررسی تخفیف دیتابیس به پایان رسید.</b>\n\n"
                f"👥 کل اکانت‌ها: <code>{total}</code>\n"
                f"🎁 اکانت‌های دارای تخفیف: <code>{len(discount_results)}</code>\n"
                f"✨ اکانت‌های دارای چند کد تخفیف همزمان: <code>{multi_discount_accounts}</code>\n"
                f"🎟 مجموع کل کدهای تخفیف: <code>{total_vouchers_found}</code>\n"
                f"{breakdown_str}"
            )
            await bot.send_document(
                chat_id=chat_id,
                document=file_out,
                filename=f"Discounts_Report_{ts}.txt",
                caption=summary_msg[:1020],
                parse_mode='HTML'
            )
        else:
            await bot.send_message(chat_id=chat_id, text=report_text, parse_mode='HTML', disable_web_page_preview=True)

        # ارسال خودکار فایل دسته‌بندی شده بر اساس هر کد تخفیف (اگر اکانتی ۲ کد داشته باشد در هر دو دسته قرار می‌گیرد)
        if discount_results:
            grouped_by_amt = {}
            for r in discount_results:
                if not r.get('link'):
                    continue
                for v in r['vouchers']:
                    lbl = v['label']
                    entry_line = f"{r['link']}  # کد: {v['code']} ({v['detail_val']})"
                    grouped_by_amt.setdefault(lbl, []).append(entry_line)

            if grouped_by_amt:
                cat_lines = [
                    f"📂 لیست تفکیک‌شده لینک‌های تخفیف بر اساس تمامی کدهای هر اکانت (تعداد کل کدها: {total_vouchers_found})\n"
                    f"💡 اکانت‌هایی که ۲ یا چند کد تخفیف همزمان دارند در دسته مربوط به هر کد درج شده‌اند.\n"
                    + "=" * 65 + "\n"
                ]
                for lbl, links_list in grouped_by_amt.items():
                    cat_lines.append(f"🎁 دسته تخفیف {lbl} (تعداد: {len(links_list)}):")
                    cat_lines.append("-" * 45)
                    for l_item in links_list:
                        cat_lines.append(l_item.split("  #")[0])
                    cat_lines.append("\n" + "=" * 65 + "\n")

                cat_io = io.BytesIO("\n".join(cat_lines).encode('utf-8'))
                await bot.send_document(
                    chat_id=chat_id,
                    document=cat_io,
                    filename=f"Categorized_All_Discounts_{ts}.txt",
                    caption="📂 فایل تفکیک خودکار لینک‌ها بر اساس تمامی کدهای تخفیف (بدون افتادن کد دوم)"
                )
    except Exception as e:
        logging.error(f"Error sending discount report: {e}")

    try:
        full_log = f"=== لاگ بررسی تخفیف دیتابیس | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
        full_log += f"کل اکانت‌ها: {total} | دارای تخفیف: {len(discount_results)} | کل کدها: {total_vouchers_found}\n"
        full_log += "=" * 50 + "\n\n"
        full_log += "".join(detail_logs)
        full_log += "\n\n=== لاگ درخواست‌های HTTP ===\n"
        full_log += "".join(api.request_logs)

        log_out = io.BytesIO(full_log.encode('utf-8'))
        await bot.send_document(
            chat_id=chat_id,
            document=log_out,
            filename=f"Discount_Full_Log_{ts}.txt",
            caption=f"📄 لاگ کامل سرور و پاسخ‌ها ({total} اکانت)"
        )
    except Exception as e:
        logging.error(f"Error sending log file: {e}")


# ==========================================
# ۱. ساخت آدرس برای تمامی اکانت‌های دیتابیس (بر اساس اطلاعات Main 9)
# ==========================================
async def process_create_address_for_db(bot, chat_id: int, acc_keys: list, addr_config: dict, addr_desc: str):
    if heavy_task_lock.locked():
        await bot.send_message(chat_id=chat_id, text="⚠️ یک عملیات سنگین هم‌اکنون در حال اجراست. لطفاً تا پایان آن صبر کنید.")
        return

    async with heavy_task_lock:
        loop = asyncio.get_running_loop()
        proxies_list = await get_all_proxies_from_db()
        api = OkalaAPI(proxies_list=proxies_list)
        ts = int(time.time())
        phone_to_latest_link = await build_phone_to_link_map()

        total = len(acc_keys)
        progress_msg = await bot.send_message(
            chat_id=chat_id,
            text=(
                f"📍 <b>شروع ساخت آدرس برای {total} اکانت دیتابیس...</b>\n"
                f"🗺 <b>آدرس انتخابی:</b> <code>{html.escape(addr_desc)}</code>\n"
                f"⏳ لطفاً منتظر بمانید..."
            ),
            parse_mode='HTML'
        )

        stats = {"success": 0, "failed": 0, "expired": 0}
        success_links = []
        detail_logs = []
        done = 0
        last_edit_time = 0.0
        lock = asyncio.Lock()
        sem = asyncio.Semaphore(20)

        def _add_addr_sync(acc_token, ref_token, uid, p_dict, phone, idx):
            proxy_ip = mask_proxy(p_dict)
            log_line = f"[{time.strftime('%H:%M:%S')}] 📱 {phone} | UID: {uid} | پروکسی: {proxy_ip}\n"
            new_acc, new_ref = None, None

            status, res = api.add_address_api(acc_token, uid, addr_config, proxy_dict=p_dict, fast_mode=True)
            if status == 401 and ref_token:
                log_line += "  ♻️ توکن منقضی — در حال رفرش...\n"
                st, new_acc, new_ref, _, _ = api.refresh_token_sequential_proxy(ref_token, start_proxy_idx=idx)
                if st == "success" and new_acc:
                    acc_token = new_acc
                    uid = get_numeric_customer_id_from_token(acc_token) or uid
                    status, res = api.add_address_api(acc_token, uid, addr_config, proxy_dict=p_dict, fast_mode=True)
                    log_line += f"  ✅ رفرش موفق — وضعیت ثبت آدرس: {status}\n"
                else:
                    log_line += "  ❌ رفرش ناموفق.\n"
                    return "expired", None, None, log_line

            if status == 200:
                log_line += "  ✅ آدرس با موفقیت ثبت شد.\n"
                return "success", new_acc, new_ref, log_line
            elif status == 401:
                log_line += "  🔒 توکن منقضی شده است.\n"
                return "expired", new_acc, new_ref, log_line
            else:
                log_line += f"  ❌ خطا در ثبت آدرس (HTTP {status}): {str(res)[:200]}\n"
                return "failed", new_acc, new_ref, log_line

        async def _worker(idx, key):
            nonlocal done, last_edit_time
            phone = clean_digits(key.replace("account:", ""))
            async with sem:
                try:
                    token_data = await redis_client.hgetall(key)
                    access_token = token_data.get("access_token", "")
                    refresh_token = token_data.get("refresh_token", "")

                    if not access_token and not refresh_token:
                        async with lock:
                            stats["expired"] += 1
                            done += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} | فاقد توکن\n")
                        return

                    if not access_token and refresh_token:
                        st, r_acc, r_ref, _, _ = await loop.run_in_executor(
                            executor, api.refresh_token_sequential_proxy, refresh_token, idx
                        )
                        if st == "success" and r_acc:
                            access_token = r_acc
                            refresh_token = r_ref or refresh_token
                            await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                    uid = get_numeric_customer_id_from_token(access_token)
                    proxy_dict = get_proxy_by_index(proxies_list, idx)

                    res_state, new_acc, new_ref, log_line = await loop.run_in_executor(
                        executor, _add_addr_sync, access_token, refresh_token, uid, proxy_dict, phone, idx
                    )

                    old_acc = access_token
                    old_ref = refresh_token
                    if new_acc:
                        access_token = new_acc
                        refresh_token = new_ref or refresh_token
                        await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                    link = await ensure_permanent_link_for_db_account(phone, old_acc, access_token, old_ref, refresh_token, phone_to_latest_link)

                    async with lock:
                        detail_logs.append(log_line)
                        stats[res_state] = stats.get(res_state, 0) + 1
                        if res_state == "success":
                            success_links.append({"phone": phone, "link": link})
                        done += 1
                        now = time.time()
                        if (now - last_edit_time >= 2.0) or (done == total):
                            last_edit_time = now
                            try:
                                await progress_msg.edit_text(
                                    f"📍 <b>در حال ساخت آدرس برای اکانت‌های دیتابیس...</b>\n"
                                    f"🗺 آدرس: <code>{html.escape(addr_desc)}</code>\n"
                                    f"📊 پیشرفت: <b>{done}/{total}</b>\n"
                                    f"✅ ثبت موفق: <b>{stats['success']}</b>\n"
                                    f"🔒 توکن منقضی: <b>{stats['expired']}</b> | ❌ خطا: <b>{stats['failed']}</b>",
                                    parse_mode='HTML'
                                )
                            except Exception:
                                pass
                except Exception as e:
                    async with lock:
                        stats["failed"] += 1
                        done += 1
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطای سیستم برای {phone}: {e}\n")

        await asyncio.gather(*[_worker(i, k) for i, k in enumerate(acc_keys)])

        try:
            await progress_msg.delete()
        except Exception:
            pass

        summary_caption = (
            f"✅ <b>عملیات ساخت آدرس برای اکانت‌های دیتابیس پایان یافت.</b>\n\n"
            f"🗺 <b>آدرس ثبت‌شده:</b> <code>{html.escape(addr_desc)}</code>\n"
            f"👥 <b>کل اکانت‌ها:</b> <code>{total}</code>\n"
            f"🟢 <b>ثبت آدرس موفق:</b> <code>{stats['success']}</code>\n"
            f"🔒 <b>توکن منقضی:</b> <code>{stats['expired']}</code>\n"
            f"🔴 <b>خطا:</b> <code>{stats['failed']}</code>"
        )

        if success_links:
            out_txt = f"📍 لیست اکانت‌های دیتابیس که آدرس برای آن‌ها ثبت شد (تعداد: {len(success_links)})\nآدرس: {addr_desc}\n" + "=" * 55 + "\n\n"
            for idx, item in enumerate(success_links, 1):
                out_txt += f"{idx}. 📱 شماره: {item['phone']}\n🔗 {item['link']}\n\n"
            file_io = io.BytesIO(out_txt.encode('utf-8'))
            await bot.send_document(
                chat_id=chat_id,
                document=file_io,
                filename=f"DB_Address_Created_{ts}.txt",
                caption=summary_caption,
                parse_mode='HTML'
            )
        else:
            await bot.send_message(chat_id=chat_id, text=summary_caption, parse_mode='HTML')

        try:
            full_log = f"=== گزارش ساخت آدرس دیتابیس | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
            full_log += "".join(detail_logs) + "\n\n=== HTTP Logs ===\n" + "".join(api.request_logs)
            log_io = io.BytesIO(full_log.encode('utf-8'))
            await bot.send_document(chat_id=chat_id, document=log_io, filename=f"DB_Add_Address_Log_{ts}.txt", caption="📄 لاگ کامل سرور (ساخت آدرس دیتابیس)")
        except Exception:
            pass

        await bot.send_message(chat_id=chat_id, text="⚙️ بازگشت به پنل مدیریت:", reply_markup=get_admin_keyboard())


# ==========================================
# ۲. بررسی سابقه خرید اکانت‌های دیتابیس (تفکیک بدون خرید و دارای خرید)
# ==========================================
async def process_db_orders_history_and_send_report(bot, chat_id: int, acc_keys: list):
    if heavy_task_lock.locked():
        await bot.send_message(chat_id=chat_id, text="⚠️ یک عملیات سنگین هم‌اکنون در حال اجراست. لطفاً تا پایان آن صبر کنید.")
        return

    async with heavy_task_lock:
        loop = asyncio.get_running_loop()
        proxies_list = await get_all_proxies_from_db()
        api = OkalaAPI(proxies_list=proxies_list)
        ts = int(time.time())
        phone_to_latest_link = await build_phone_to_link_map()

        total = len(acc_keys)
        progress_msg = await bot.send_message(
            chat_id=chat_id,
            text=f"🛍 <b>شروع بررسی موازی سابقه خرید برای {total} اکانت دیتابیس...</b>\n⏳ لطفاً منتظر بمانید.",
            parse_mode='HTML'
        )

        stats = {"has_orders": 0, "no_orders": 0, "failed": 0, "total_orders_count": 0}
        with_orders_list = []
        no_orders_list = []
        detail_logs = []
        done = 0
        last_edit_time = 0.0
        lock = asyncio.Lock()
        sem = asyncio.Semaphore(20)

        def _check_ord_sync(acc_token, ref_token, p_dict, phone, idx):
            proxy_ip = mask_proxy(p_dict)
            log_line = f"[{time.strftime('%H:%M:%S')}] 📱 {phone} | پروکسی: {proxy_ip}\n"
            new_acc, new_ref = None, None

            ord_status, ord_res = api.get_orders_api(acc_token, proxy_dict=p_dict, fast_mode=True)
            if ord_status == 401 and ref_token:
                log_line += "  ♻️ توکن منقضی — در حال رفرش...\n"
                st, new_acc, new_ref, _, _ = api.refresh_token_sequential_proxy(ref_token, start_proxy_idx=idx)
                if st == "success" and new_acc:
                    acc_token = new_acc
                    ord_status, ord_res = api.get_orders_api(acc_token, proxy_dict=p_dict, fast_mode=True)
                    log_line += "  ✅ رفرش موفق.\n"
                else:
                    log_line += "  ❌ رفرش ناموفق.\n"
                    return "failed", 0, None, None, log_line

            ord_ok, has_ord, ord_count = parse_orders_response(ord_status, ord_res)
            if not ord_ok:
                log_line += f"  ❌ خطا در استعلام سفارشات (کد: {ord_status})\n"
                return "failed", 0, new_acc, new_ref, log_line

            if has_ord:
                log_line += f"  🛍 دارای {ord_count} سفارش ثبت‌شده\n"
                return "has_orders", ord_count, new_acc, new_ref, log_line
            else:
                log_line += "  ✨ بدون سابقه خرید (۰ سفارش)\n"
                return "no_orders", 0, new_acc, new_ref, log_line

        async def _worker(idx, key):
            nonlocal done, last_edit_time
            phone = clean_digits(key.replace("account:", ""))
            async with sem:
                try:
                    token_data = await redis_client.hgetall(key)
                    access_token = token_data.get("access_token", "")
                    refresh_token = token_data.get("refresh_token", "")

                    if not access_token and not refresh_token:
                        async with lock:
                            stats["failed"] += 1
                            done += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} — فاقد توکن\n")
                        return

                    if not access_token and refresh_token:
                        st, r_acc, r_ref, _, _ = await loop.run_in_executor(
                            executor, api.refresh_token_sequential_proxy, refresh_token, idx
                        )
                        if st == "success" and r_acc:
                            access_token = r_acc
                            refresh_token = r_ref or refresh_token
                            await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                    proxy_dict = get_proxy_by_index(proxies_list, idx)
                    state_res, ord_cnt, new_acc, new_ref, log_line = await loop.run_in_executor(
                        executor, _check_ord_sync, access_token, refresh_token, proxy_dict, phone, idx
                    )

                    old_acc = access_token
                    old_ref = refresh_token
                    if new_acc:
                        access_token = new_acc
                        refresh_token = new_ref or refresh_token
                        await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                    link = await ensure_permanent_link_for_db_account(phone, old_acc, access_token, old_ref, refresh_token, phone_to_latest_link)

                    async with lock:
                        detail_logs.append(log_line)
                        if state_res == "has_orders":
                            stats["has_orders"] += 1
                            stats["total_orders_count"] += ord_cnt
                            with_orders_list.append({"phone": phone, "count": ord_cnt, "link": link})
                        elif state_res == "no_orders":
                            stats["no_orders"] += 1
                            no_orders_list.append({"phone": phone, "link": link})
                        else:
                            stats["failed"] += 1

                        done += 1
                        now = time.time()
                        if (now - last_edit_time >= 2.0) or (done == total):
                            last_edit_time = now
                            try:
                                await progress_msg.edit_text(
                                    f"🛍 <b>بررسی موازی سابقه خرید دیتابیس...</b>\n"
                                    f"📊 پیشرفت: <b>{done}/{total}</b>\n"
                                    f"✨ بدون خرید (خام از نظر سفارش): <b>{stats['no_orders']}</b>\n"
                                    f"🛍 دارای سابقه خرید: <b>{stats['has_orders']}</b> (مجموع سفارش‌ها: <b>{stats['total_orders_count']}</b>)\n"
                                    f"❌ خطا/منقضی: <b>{stats['failed']}</b>",
                                    parse_mode='HTML'
                                )
                            except Exception:
                                pass
                except Exception as e:
                    async with lock:
                        stats["failed"] += 1
                        done += 1
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطای کلی برای {phone}: {e}\n")

        await asyncio.gather(*[_worker(i, k) for i, k in enumerate(acc_keys)])

        try:
            await progress_msg.delete()
        except Exception:
            pass

        summary_text = (
            f"📊 <b>گزارش بررسی سابقه خرید اکانت‌های دیتابیس:</b>\n\n"
            f"👥 <b>کل اکانت‌های بررسی‌شده:</b> <code>{total}</code>\n"
            f"✨ <b>بدون سابقه خرید (۰ سفارش):</b> <code>{stats['no_orders']}</code>\n"
            f"🛍 <b>دارای سابقه خرید:</b> <code>{stats['has_orders']}</code> (مجموع <code>{stats['total_orders_count']}</code> سفارش)\n"
            f"❌ <b>خطا یا توکن سوخته:</b> <code>{stats['failed']}</code>"
        )
        await bot.send_message(chat_id=chat_id, text=summary_text, parse_mode='HTML')

        if no_orders_list:
            no_ord_txt = f"✨ لیست اکانت‌های بدون سابقه خرید دیتابیس (تعداد: {len(no_orders_list)})\n" + "=" * 55 + "\n\n"
            for idx, r in enumerate(no_orders_list, 1):
                no_ord_txt += f"{idx}. 📱 شماره: {r['phone']}\n🔗 {r['link']}\n\n"
            await bot.send_document(
                chat_id=chat_id,
                document=io.BytesIO(no_ord_txt.encode('utf-8')),
                filename=f"DB_No_Orders_Accounts_{ts}.txt",
                caption=f"✨ اکانت‌های بدون سابقه خرید دیتابیس ({len(no_orders_list)} اکانت)"
            )

        if with_orders_list:
            with_orders_list.sort(key=lambda x: x['count'], reverse=True)
            has_ord_txt = f"🛍 لیست اکانت‌های دارای سابقه خرید دیتابیس (تعداد: {len(with_orders_list)})\n" + "=" * 55 + "\n\n"
            for idx, r in enumerate(with_orders_list, 1):
                has_ord_txt += f"{idx}. 📱 شماره: {r['phone']} | 🛍 تعداد سفارش: {r['count']}\n🔗 {r['link']}\n\n"
            await bot.send_document(
                chat_id=chat_id,
                document=io.BytesIO(has_ord_txt.encode('utf-8')),
                filename=f"DB_Has_Orders_Accounts_{ts}.txt",
                caption=f"🛍 اکانت‌های دارای سابقه خرید دیتابیس ({len(with_orders_list)} اکانت)"
            )

        try:
            full_log = f"=== لاگ بررسی سابقه خرید دیتابیس | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
            full_log += "".join(detail_logs) + "\n\n=== HTTP Logs ===\n" + "".join(api.request_logs)
            await bot.send_document(
                chat_id=chat_id,
                document=io.BytesIO(full_log.encode('utf-8')),
                filename=f"DB_Orders_History_Log_{ts}.txt",
                caption="📄 لاگ کامل سرور (بررسی سابقه خرید دیتابیس)"
            )
        except Exception:
            pass

        await bot.send_message(chat_id=chat_id, text="⚙️ بازگشت به پنل مدیریت:", reply_markup=get_admin_keyboard())


# ==========================================
# ۳. حذف آدرس‌های اکانت‌های دیتابیس (قابلیت تکمیلی از Main 9)
# ==========================================
async def process_delete_addresses_for_db(bot, chat_id: int, acc_keys: list):
    if heavy_task_lock.locked():
        await bot.send_message(chat_id=chat_id, text="⚠️ یک عملیات سنگین هم‌اکنون در حال اجراست. لطفاً تا پایان آن صبر کنید.")
        return

    async with heavy_task_lock:
        loop = asyncio.get_running_loop()
        proxies_list = await get_all_proxies_from_db()
        api = OkalaAPI(proxies_list=proxies_list)
        ts = int(time.time())

        total = len(acc_keys)
        progress_msg = await bot.send_message(
            chat_id=chat_id,
            text=f"🗑 <b>شروع پاکسازی تمامی آدرس‌های {total} اکانت دیتابیس...</b>\n⏳ لطفاً منتظر بمانید.",
            parse_mode='HTML'
        )

        stats = {"success_accounts": 0, "total_deleted": 0, "failed": 0}
        detail_logs = []
        done = 0
        last_edit_time = 0.0
        lock = asyncio.Lock()
        sem = asyncio.Semaphore(20)

        def _del_addr_sync(acc_token, ref_token, p_dict, phone, idx):
            new_acc, new_ref = None, None
            deleted_count = 0
            uid = get_numeric_customer_id_from_token(acc_token)

            for attempt in range(6):
                status, addr_res = api.get_addresses_api(acc_token, proxy_dict=p_dict, fast_mode=True)
                if status == 401 and ref_token:
                    st, new_acc, new_ref, _, _ = api.refresh_token_sequential_proxy(ref_token, start_proxy_idx=idx)
                    if st == "success" and new_acc:
                        acc_token = new_acc
                        uid = get_numeric_customer_id_from_token(acc_token)
                        status, addr_res = api.get_addresses_api(acc_token, proxy_dict=p_dict, fast_mode=True)
                    else:
                        return "failed", 0, None, None

                addresses = []
                if status == 200 and isinstance(addr_res, dict):
                    addresses = (addr_res.get('data') or {}).get('customerAddressResponseItems') or []

                if not addresses and uid:
                    r_st, r_res = api.get_address_react_api(acc_token, uid, proxy_dict=p_dict, fast_mode=True)
                    if r_st == 200 and isinstance(r_res, dict) and isinstance(r_res.get('data'), list):
                        addresses = r_res['data']
                    elif status != 200 and attempt == 0:
                        return "failed", 0, new_acc, new_ref

                if not addresses:
                    break

                del_round = 0
                for addr in addresses:
                    addr_id = addr.get('id') if isinstance(addr, dict) else None
                    if addr_id:
                        d_st, _ = api.delete_address_api(acc_token, addr_id, proxy_dict=p_dict, fast_mode=True)
                        if d_st == 200:
                            deleted_count += 1
                            del_round += 1
                if del_round == 0:
                    break

            return "success", deleted_count, new_acc, new_ref

        async def _worker(idx, key):
            nonlocal done, last_edit_time
            phone = clean_digits(key.replace("account:", ""))
            async with sem:
                try:
                    token_data = await redis_client.hgetall(key)
                    access_token = token_data.get("access_token", "")
                    refresh_token = token_data.get("refresh_token", "")
                    if not access_token and not refresh_token:
                        async with lock:
                            stats["failed"] += 1
                            done += 1
                        return

                    proxy_dict = get_proxy_by_index(proxies_list, idx)
                    st_res, del_cnt, new_acc, new_ref = await loop.run_in_executor(
                        executor, _del_addr_sync, access_token, refresh_token, proxy_dict, phone, idx
                    )
                    if new_acc:
                        await redis_client.hset(f"account:{phone}", mapping={"access_token": new_acc, "refresh_token": new_ref or refresh_token or ""})

                    async with lock:
                        if st_res == "success":
                            stats["success_accounts"] += 1
                            stats["total_deleted"] += del_cnt
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ✅ {phone} | حذف شد: {del_cnt} آدرس\n")
                        else:
                            stats["failed"] += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} | خطا در حذف آدرس\n")
                        done += 1
                        now = time.time()
                        if (now - last_edit_time >= 2.0) or (done == total):
                            last_edit_time = now
                            try:
                                await progress_msg.edit_text(
                                    f"🗑 <b>در حال پاکسازی آدرس‌های دیتابیس...</b>\n"
                                    f"📊 پیشرفت: <b>{done}/{total}</b>\n"
                                    f"✅ اکانت‌های بررسی‌شده: <b>{stats['success_accounts']}</b>\n"
                                    f"🗑 مجموع آدرس‌های حذف‌شده: <b>{stats['total_deleted']}</b>\n"
                                    f"❌ خطا: <b>{stats['failed']}</b>",
                                    parse_mode='HTML'
                                )
                            except Exception:
                                pass
                except Exception:
                    async with lock:
                        stats["failed"] += 1
                        done += 1

        await asyncio.gather(*[_worker(i, k) for i, k in enumerate(acc_keys)])
        try:
            await progress_msg.delete()
        except Exception:
            pass

        await bot.send_message(
            chat_id=chat_id,
            text=(
                f"✅ <b>پاکسازی آدرس‌های دیتابیس به پایان رسید.</b>\n\n"
                f"👥 کل اکانت‌ها: <code>{total}</code>\n"
                f"🟢 موفق: <code>{stats['success_accounts']}</code>\n"
                f"🗑 مجموع آدرس‌های حذف‌شده: <code>{stats['total_deleted']}</code>\n"
                f"🔴 خطا: <code>{stats['failed']}</code>"
            ),
            reply_markup=get_admin_keyboard(),
            parse_mode='HTML'
        )


# ==========================================
# سیستم جامع دریافت دسته‌ای (Batch Collector) برای ۱۰۰ تا ۱۰۰۰+ فایل زیپ، لینک یا فایل متنی
# پشتیبانی از:
#   1. تبدیل فایل زیپ به لینک دائمی (zip_to_link)
#   2. بررسی تخفیف همه کدهای زیپ/لینک (user_discount_check)
#   3. ساخت آدرس برای لینک/زیپ ارسالی کاربر (user_create_address)
#   4. بررسی سابقه خرید لینک/زیپ ارسالی کاربر (user_check_orders)
#   5. حذف آدرس‌های لینک/زیپ ارسالی کاربر (user_delete_addresses)
# ==========================================
BATCH_MODE_TITLES = {
    'zip_to_link': '🔗 تبدیل دسته‌ای فایل‌های ZIP به لینک دائمی',
    'delete_zip_from_db': '🗑 حذف دسته‌ای اکانت‌های فایل ZIP / لینک از دیتابیس',
    'user_discount_check': '🎁 بررسی تمامی کدهای تخفیف (لینک / ZIP / TXT)',
    'user_create_address': '📍 ساخت آدرس برای اکانت‌های ارسالی (لینک / ZIP / TXT)',
    'user_check_orders': '🛍 بررسی سابقه خرید اکانت‌های ارسالی (لینک / ZIP / TXT)',
    'user_delete_addresses': '🗑 حذف آدرس‌های اکانت‌های ارسالی (لینک / ZIP / TXT)',
}


def get_batch_collector_keyboard(mode: str, zip_count: int, doc_count: int, url_count: int):
    total_inputs = zip_count + doc_count + url_count
    kb = []
    if total_inputs > 0:
        btn_label = f"✅ تایید و شروع عملیات ({zip_count} زیپ"
        if url_count > 0:
            btn_label += f" + {url_count} لینک"
        if doc_count > 0:
            btn_label += f" + {doc_count} فایل"
        btn_label += ")"
        kb.append([InlineKeyboardButton(btn_label, callback_data="batch_confirm_start")])
        kb.append([InlineKeyboardButton("🗑 پاک کردن لیست ارسالی", callback_data="batch_clear_queue")])
    kb.append([InlineKeyboardButton("❌ انصراف و بازگشت به پنل", callback_data="batch_cancel_collect")])
    return InlineKeyboardMarkup(kb)


def get_batch_collector_status_text(mode: str, user_data: dict) -> str:
    title = BATCH_MODE_TITLES.get(mode, "📦 دریافت دسته‌ای فایل‌ها و لینک‌ها")
    queue = user_data.get('batch_items_queue', [])
    zip_cnt = sum(1 for x in queue if x['kind'] == 'zip')
    doc_cnt = sum(1 for x in queue if x['kind'] in ('txt', 'json'))
    url_cnt = sum(len(x.get('urls', [])) for x in queue if x['kind'] == 'urls')
    total_size = sum(x.get('file_size', 0) for x in queue)

    addr_desc = user_data.get('batch_address_desc')
    extra_info = f"\n🗺 <b>آدرس انتخابی برای ثبت:</b> <code>{html.escape(addr_desc)}</code>\n" if (mode == 'user_create_address' and addr_desc) else ""

    if not queue:
        if mode == 'zip_to_link':
            return (
                f"📦 <b>{title}</b>\n\n"
                "لطفاً فایل‌های <code>.zip</code> خود را ارسال یا فوروارد کنید.\n"
                "🔹 <b>پشتیبانی از ۱۰۰ تا ۱۰۰۰+ فایل زیپ همزمان:</b> تمامی فایل‌ها بدون محدودیت در صف ذخیره می‌شوند و ربات تا قبل از تایید شما هیچ پردازشی را شروع نمی‌کند.\n"
                "🔹 شماره‌های تکراری موجود در دیتابیس به‌صورت هوشمند رد می‌شوند تا لینک تکراری ساخته نشود.\n\n"
                "👇 پس از پایان ارسال همه فایل‌ها، روی دکمه <b>«✅ تایید و شروع عملیات»</b> بزنید (یا دستور /start_batch را ارسال کنید):"
            )
        elif mode == 'delete_zip_from_db':
            return (
                f"🗑 <b>{title}</b>\n\n"
                "لطفاً فایل‌های <code>.zip</code> (یا فایل <code>.txt</code> / <code>.json</code> یا لینک و شماره) که می‌خواهید اکانت‌های آن‌ها از دیتابیس حذف شوند را ارسال یا فوروارد کنید.\n"
                "🔹 <b>پشتیبانی از ۱۰۰ تا ۱۰۰۰+ فایل زیپ همزمان:</b> تمامی فایل‌ها در صف قرار می‌گیرند و تا قبل از تایید شما هیچ حذفی انجام نمی‌شود.\n"
                "🔹 با تایید شما، تمام اطلاعات اکانت‌های موجود در این فایل‌ها (توکن‌ها، شماره‌ها و لینک‌های دائمی آن‌ها) به‌طور کامل از دیتابیس پاکسازی می‌شوند.\n\n"
                "👇 پس از پایان ارسال همه فایل‌ها، روی دکمه <b>«✅ تایید و شروع عملیات»</b> بزنید (یا دستور /start_batch را ارسال کنید):"
            )
        else:
            return (
                f"📦 <b>{title}</b>{extra_info}\n\n"
                "لطفاً اکانت‌های خود را به هر یک از روش‌های زیر ارسال یا فوروارد کنید:\n"
                "1️⃣ <b>یک یا صدها فایل <code>.zip</code></b> (حاوی فایل‌های JSON اکانت‌ها یا فایل TXT لینک‌ها)\n"
                "2️⃣ <b>فایل‌های <code>.txt</code> یا <code>.json</code></b>\n"
                "3️⃣ <b>لینک‌های مستقیم اکانت</b> در پیام متنی\n\n"
                "🔹 می‌توانید صدها فایل را پشت سر هم فوروارد کنید؛ پس از اتمام ارسال، روی دکمه <b>«✅ تایید و شروع عملیات»</b> بزنید:"
            )

    return (
        f"📥 <b>{title} — در حال جمع‌آوری ورودی‌ها...</b>{extra_info}\n\n"
        f"📦 <b>فایل‌های ZIP دریافت‌شده:</b> <b><code>{zip_cnt}</code> فایل</b>\n"
        f"📄 <b>فایل‌های TXT/JSON دریافت‌شده:</b> <b><code>{doc_cnt}</code> فایل</b>\n"
        f"🔗 <b>لینک‌های متنی دریافت‌شده:</b> <b><code>{url_cnt}</code> لینک</b>\n"
        f"💾 <b>حجم کل فایل‌ها:</b> <code>{format_bytes(total_size)}</code>\n\n"
        "💡 می‌توانید فایل‌ها یا لینک‌های بیشتری ارسال کنید، یا برای آغاز پردازش دکمه <b>«✅ تایید و شروع عملیات»</b> زیر را لمس کنید (یا /start_batch بفرستید):"
    )


async def _delayed_update_collector_ui(bot, chat_id: int, user_data: dict):
    """بروزرسانی هوشمند و ضد-فلود (Debounce) پیام وضعیت هنگام دریافت ۱۰۰ تا ۱۰۰۰ فایل زیپ"""
    await asyncio.sleep(1.3)
    mode = user_data.get('batch_collect_mode')
    if not mode:
        return
    queue = user_data.get('batch_items_queue', [])
    zip_cnt = sum(1 for x in queue if x['kind'] == 'zip')
    doc_cnt = sum(1 for x in queue if x['kind'] in ('txt', 'json'))
    url_cnt = sum(len(x.get('urls', [])) for x in queue if x['kind'] == 'urls')

    text = get_batch_collector_status_text(mode, user_data)
    kb = get_batch_collector_keyboard(mode, zip_cnt, doc_cnt, url_cnt)
    msg_id = user_data.get('batch_status_msg_id')

    if msg_id:
        try:
            await bot.edit_message_text(chat_id=chat_id, message_id=msg_id, text=text, reply_markup=kb, parse_mode='HTML')
            return
        except Exception as e:
            if "Message is not modified" in str(e):
                return
    try:
        new_msg = await bot.send_message(chat_id=chat_id, text=text, reply_markup=kb, parse_mode='HTML')
        user_data['batch_status_msg_id'] = new_msg.message_id
    except Exception as e:
        logging.error(f"Error updating collector UI: {e}")


async def enqueue_batch_input_message(update: Update, context: ContextTypes.DEFAULT_TYPE) -> bool:
    """افزودن فایل زیپ، فایل متنی/JSON یا لینک به صف جمع‌آوری دسته‌ای"""
    mode = context.user_data.get('batch_collect_mode')
    if not mode:
        return False

    msg = update.message
    if not msg:
        return False

    added = False
    async with batch_collection_lock:
        if 'batch_items_queue' not in context.user_data:
            context.user_data['batch_items_queue'] = []
        queue = context.user_data['batch_items_queue']

        if msg.document:
            fname = msg.document.file_name or "file"
            lower_name = fname.lower()
            if lower_name.endswith('.zip'):
                queue.append({
                    "kind": "zip",
                    "file_id": msg.document.file_id,
                    "file_name": fname,
                    "file_size": msg.document.file_size or 0
                })
                added = True
            elif lower_name.endswith('.txt') or lower_name.endswith('.csv') or lower_name.endswith('.log'):
                queue.append({
                    "kind": "txt",
                    "file_id": msg.document.file_id,
                    "file_name": fname,
                    "file_size": msg.document.file_size or 0
                })
                added = True
            elif lower_name.endswith('.json'):
                queue.append({
                    "kind": "json",
                    "file_id": msg.document.file_id,
                    "file_name": fname,
                    "file_size": msg.document.file_size or 0
                })
                added = True
            else:
                await msg.reply_text("❌ فرمت فایل پشتیبانی نمی‌شود. لطفاً فایل `.zip`، `.txt` یا `.json` ارسال کنید.")
                return True

        elif msg.text:
            txt = msg.text.strip()
            if txt in ["شروع", "تایید", "start", "Start", "شروع پردازش", "/start_zip", "/start_batch"]:
                await trigger_batch_processing(update, context)
                return True

            urls = re.findall(r'(https?://[^\s]+)', txt)
            phones_in_txt = re.findall(r'09\d{9}', clean_digits(txt)) if mode == 'delete_zip_from_db' else []
            if urls or phones_in_txt:
                queue.append({
                    "kind": "urls",
                    "urls": urls + [f"phone://{p}" for p in phones_in_txt],
                    "file_size": len(txt)
                })
                added = True
            else:
                await msg.reply_text("⚠️ هیچ لینک یا ورودی معتبری در متن یافت نشد. لطفاً فایل `.zip` / `.txt` بفرستید یا روی دکمه «✅ تایید و شروع عملیات» بزنید.")
                return True

    if added:
        uid = update.effective_user.id
        old_task = batch_ui_update_tasks.get(uid)
        if old_task and not old_task.done():
            old_task.cancel()
        batch_ui_update_tasks[uid] = asyncio.create_task(
            _delayed_update_collector_ui(context.bot, update.effective_chat.id, context.user_data)
        )
    return True


async def resolve_account_data_from_url(url: str, loop) -> tuple:
    """دریافت دیتای JSON اکانت از لینک (ابتدا بررسی سریع در Redis محلی، سپس درخواست وب)"""
    if '/acc/' in url:
        lid = url.split('/acc/')[-1].strip()
        raw_redis = await redis_client.get(f"acc_link:{lid}")
        if raw_redis:
            try:
                return json.loads(raw_redis), lid
            except Exception:
                pass
    try:
        res = await loop.run_in_executor(executor, lambda: requests.get(url, timeout=15))
        if res.status_code == 200:
            return res.json(), None
    except Exception:
        pass
    return None, None


async def iterate_targets_from_batch_item(bot, item: dict):
    """
    باز کردن یک آیتم از صف (فایل زیپ، فایل متنی، فایل JSON یا لیست لینک‌ها)
    و برگرداندن لیست اکانت‌های داخل آن به صورت:
    [{"type": "json"|"url", "source": str, "zip_name": str, "data": dict|None, "url": str|None}]
    """
    kind = item.get("kind")
    targets = []

    if kind == "urls":
        for u in item.get("urls", []):
            if str(u).startswith("phone://"):
                ph_v = clean_digits(str(u).replace("phone://", ""))
                targets.append({"type": "phone", "source": ph_v, "zip_name": "ورودی متنی", "data": None, "url": None, "phone": ph_v})
            else:
                targets.append({"type": "url", "source": u, "zip_name": "لینک مستقیم", "data": None, "url": u})
        return targets

    file_id = item.get("file_id")
    fname = item.get("file_name", "file")
    if not file_id:
        return targets

    with tempfile.TemporaryDirectory() as temp_dir:
        local_path = os.path.join(temp_dir, fname)
        tg_file = await bot.get_file(file_id)
        await tg_file.download_to_drive(local_path)

        if kind == "zip":
            try:
                with zipfile.ZipFile(local_path, 'r') as zf:
                    for info in zf.infolist():
                        if info.is_dir() or '__MACOSX' in info.filename:
                            continue
                        base_name = os.path.basename(info.filename)
                        if not base_name or base_name.startswith('.'):
                            continue
                        raw_bytes = zf.read(info.filename)
                        raw_text = raw_bytes.decode('utf-8', errors='ignore')
                        if base_name.lower().endswith('.json'):
                            try:
                                parsed = json.loads(raw_text)
                                if isinstance(parsed, dict) and ('cookies' in parsed or 'origins' in parsed or 'access_token' in parsed):
                                    targets.append({
                                        "type": "json",
                                        "source": base_name,
                                        "zip_name": fname,
                                        "data": parsed,
                                        "url": None
                                    })
                                else:
                                    for u in re.findall(r'(https?://[^\s"\'>]+)', raw_text):
                                        targets.append({"type": "url", "source": u, "zip_name": fname, "data": None, "url": u})
                            except Exception:
                                pass
                        elif base_name.lower().endswith(('.txt', '.csv', '.log')):
                            found_urls = re.findall(r'(https?://[^\s]+)', raw_text)
                            for u in found_urls:
                                targets.append({"type": "url", "source": u, "zip_name": fname, "data": None, "url": u})
                            for ph_m in re.findall(r'09\d{9}', clean_digits(raw_text)):
                                targets.append({"type": "phone", "source": ph_m, "zip_name": fname, "data": None, "url": None, "phone": ph_m})
            except Exception as e:
                logging.error(f"Error unpacking zip {fname}: {e}")

        elif kind == "json":
            try:
                with open(local_path, 'r', encoding='utf-8', errors='ignore') as f:
                    raw_text = f.read()
                parsed = json.loads(raw_text)
                if isinstance(parsed, dict) and ('cookies' in parsed or 'origins' in parsed or 'access_token' in parsed):
                    targets.append({"type": "json", "source": fname, "zip_name": fname, "data": parsed, "url": None})
                elif isinstance(parsed, dict):
                    # پشتیبانی از فایل JSON شامل دیکشنری شماره‌ها و توکن‌ها
                    for ph, tok_obj in parsed.items():
                        if isinstance(tok_obj, dict) and (tok_obj.get("access_token") or tok_obj.get("refresh_token")):
                            inj = format_for_injector({
                                "access_token": tok_obj.get("access_token", ""),
                                "refresh_token": tok_obj.get("refresh_token", ""),
                                "UserInfo": {"MobilePhone": clean_digits(str(ph))}
                            })
                            targets.append({"type": "json", "source": f"{ph}.json", "zip_name": fname, "data": inj, "url": None})
            except Exception:
                pass

        elif kind == "txt":
            try:
                with open(local_path, 'r', encoding='utf-8', errors='ignore') as f:
                    raw_text = f.read()
                for u in re.findall(r'(https?://[^\s]+)', raw_text):
                    targets.append({"type": "url", "source": u, "zip_name": fname, "data": None, "url": u})
                for ph_m in re.findall(r'09\d{9}', clean_digits(raw_text)):
                    targets.append({"type": "phone", "source": ph_m, "zip_name": fname, "data": None, "url": None, "phone": ph_m})
            except Exception:
                pass

    return targets


# ==========================================
# اجرای عملیات ۱: تبدیل ۱۰۰ تا ۱۰۰۰+ فایل زیپ به لینک دائمی (پس از تایید کاربر)
# ==========================================
async def process_batch_zips_to_links(bot, chat_id: int, batch_items: list):
    total_batches = len(batch_items)
    ts = int(time.time())

    live_msg = await bot.send_message(
        chat_id=chat_id,
        text=f"⏳ <b>عملیات پردازش دسته‌ای {total_batches} بسته ورودی در صف قرار گرفت...</b>\nلطفاً منتظر بمانید.",
        parse_mode='HTML'
    )

    async with zip_queue_lock:
        try:
            await live_msg.edit_text(
                "🔍 <b>در حال استخراج اولیه شماره‌های موجود در دیتابیس برای جلوگیری از ساخت لینک تکراری...</b>",
                parse_mode='HTML'
            )
        except Exception:
            pass

        existing_phones = await get_all_existing_phones_in_db()
        initial_db_count = len(existing_phones)

        proxies_list = await get_all_proxies_from_db()
        api = OkalaAPI(proxies_list=proxies_list)
        loop = asyncio.get_running_loop()
        sem = asyncio.Semaphore(30)
        lock = asyncio.Lock()

        overall_stats = {
            "zips_done": 0,
            "total_zips": total_batches,
            "total_accounts_found": 0,
            "processed_accounts": 0,
            "refreshed": 0,
            "access_only": 0,
            "skipped_duplicate": 0,
            "dead": 0,
            "proxy_error": 0,
            "zip_errors": 0
        }

        healthy_links = []
        detail_logs = []
        last_edit_time = [0.0]
        start_time = time.time()

        async def update_live_progress(current_zip_name: str, current_zip_idx: int, zip_acc_done: int, zip_acc_total: int, force: bool = False):
            now = time.time()
            if not force and (now - last_edit_time[0] < 2.5):
                return
            last_edit_time[0] = now

            elapsed = int(now - start_time)
            mins, secs = divmod(elapsed, 60)
            time_str = f"{mins}:{secs:02d}"

            zip_pct = int((current_zip_idx / max(total_batches, 1)) * 100)
            bar_len = 12
            filled = int(bar_len * zip_pct / 100)
            bar = "█" * filled + "░" * (bar_len - filled)

            status_text = (
                f"⚡ <b>پردازش زنده تبدیل دسته‌ای ZIP به لینک دائمی</b>\n"
                f"<code>[{bar}] {zip_pct}%</code> | ⏱ زمان: <code>{time_str}</code>\n\n"
                f"📦 <b>فایل‌های زیپ پردازش‌شده:</b> <code>{current_zip_idx}/{total_batches}</code>\n"
                f"📂 <b>فایل فعلی:</b> <code>{html.escape(current_zip_name[:35])}</code> (<code>{zip_acc_done}/{zip_acc_total}</code>)\n"
                f"👥 <b>کل اکانت‌های بررسی‌شده:</b> <code>{overall_stats['processed_accounts']}</code> از <code>{overall_stats['total_accounts_found']}</code>\n"
                f"────────────────────\n"
                f"🔗 <b>لینک‌های جدید ساخته‌شده:</b> <b><code>{len(healthy_links)}</code></b>\n"
                f"  ├─ ♻️ نوسازی کامل (Refresh+Access): <code>{overall_stats['refreshed']}</code>\n"
                f"  └─ 🟢 سالم با Access فعلی: <code>{overall_stats['access_only']}</code>\n"
                f"⏭ <b>رد شده (تکراری و موجود در دیتابیس):</b> <code>{overall_stats['skipped_duplicate']}</code>\n"
                f"💀 <b>رد شده (توکن باطل/منقضی):</b> <code>{overall_stats['dead']}</code>\n"
                f"⚠️ <b>خطای شبکه/پروکسی:</b> <code>{overall_stats['proxy_error']}</code>"
            )
            try:
                await live_msg.edit_text(status_text, parse_mode='HTML')
            except Exception:
                pass

        for z_idx, b_item in enumerate(batch_items, 1):
            orig_zip_name = b_item.get("file_name", f"Batch_{z_idx}.zip")
            await update_live_progress(orig_zip_name, z_idx - 1, 0, 0, force=(z_idx == 1))

            try:
                targets = await iterate_targets_from_batch_item(bot, b_item)
                json_targets = [t for t in targets if t["type"] == "json" and isinstance(t.get("data"), dict)]

                if not json_targets:
                    async with lock:
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ فایل {orig_zip_name} فاقد فایل JSON معتبر بود.\n")
                        overall_stats["zips_done"] = z_idx
                    continue

                zip_total_files = len(json_targets)
                overall_stats["total_accounts_found"] += zip_total_files
                zip_done_files = 0

                await update_live_progress(orig_zip_name, z_idx - 1, 0, zip_total_files)

                async def _zip_acc_worker(acc_idx, target_obj):
                    nonlocal zip_done_files
                    filename = target_obj["source"]
                    data = target_obj["data"]
                    async with sem:
                        try:
                            acc_tok, ref_tok, extracted_phone = extract_tokens_from_json_data(data)
                            phone = extracted_phone or clean_digits(filename.replace('.json', ''))

                            async with lock:
                                if phone and phone in existing_phones:
                                    overall_stats["skipped_duplicate"] += 1
                                    overall_stats["processed_accounts"] += 1
                                    zip_done_files += 1
                                    if len(detail_logs) < 10000:
                                        detail_logs.append(
                                            f"[{time.strftime('%H:%M:%S')}] ⏭ {phone} ({orig_zip_name}) | از قبل در دیتابیس وجود دارد (لینک تکراری ساخته نشد)\n"
                                        )
                                    await update_live_progress(orig_zip_name, z_idx - 1, zip_done_files, zip_total_files)
                                    return
                                if phone:
                                    existing_phones.add(phone)

                            if not acc_tok and not ref_tok:
                                async with lock:
                                    if phone:
                                        existing_phones.discard(phone)
                                    overall_stats["dead"] += 1
                                    overall_stats["processed_accounts"] += 1
                                    zip_done_files += 1
                                    if len(detail_logs) < 10000:
                                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} ({orig_zip_name}/{filename}) | فاقد توکن معتبر\n")
                                    await update_live_progress(orig_zip_name, z_idx - 1, zip_done_files, zip_total_files)
                                return

                            res_type, final_acc, final_ref, st_code, _ = await loop.run_in_executor(
                                executor, api.verify_and_renew_account, acc_tok, ref_tok, acc_idx
                            )

                            if res_type in ["refreshed", "access_only"] and final_acc:
                                await redis_client.hset(f"account:{phone}", mapping={
                                    "access_token": final_acc,
                                    "refresh_token": final_ref or ""
                                })

                                updated_json_data = update_tokens_in_data(data, acc_tok, final_acc, ref_tok, final_ref)
                                updated_content_str = json.dumps(updated_json_data, ensure_ascii=False)

                                link_id = str(uuid.uuid4())[:12]
                                await redis_client.set(f"acc_link:{link_id}", updated_content_str)
                                final_url = f"{WEB_DOMAIN}/acc/{link_id}"
                                await redis_client.set(f"phone_active_link:{phone}", final_url)

                                async with lock:
                                    if res_type == "refreshed":
                                        overall_stats["refreshed"] += 1
                                        if len(detail_logs) < 10000:
                                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ✅ {phone} ({orig_zip_name}) | نوسازی موفق و ساخت لینک: {final_url}\n")
                                    else:
                                        overall_stats["access_only"] += 1
                                        if len(detail_logs) < 10000:
                                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 🟢 {phone} ({orig_zip_name}) | Access سالم و ساخت لینک: {final_url}\n")
                                    healthy_links.append({"phone": phone, "link": final_url, "zip": orig_zip_name})
                            else:
                                async with lock:
                                    if phone:
                                        existing_phones.discard(phone)
                                    if res_type == "unrecoverable":
                                        overall_stats["dead"] += 1
                                        if len(detail_logs) < 10000:
                                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 💀 {phone} ({orig_zip_name}) | توکن باطل (کد: {st_code}) — لینک ساخته نشد\n")
                                    else:
                                        overall_stats["proxy_error"] += 1
                                        if len(detail_logs) < 10000:
                                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} ({orig_zip_name}) | خطای شبکه/پروکسی (کد: {st_code})\n")

                            async with lock:
                                overall_stats["processed_accounts"] += 1
                                zip_done_files += 1
                                await update_live_progress(orig_zip_name, z_idx - 1, zip_done_files, zip_total_files)

                        except Exception as e:
                            async with lock:
                                overall_stats["dead"] += 1
                                overall_stats["processed_accounts"] += 1
                                zip_done_files += 1
                                if len(detail_logs) < 10000:
                                    detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطا در خواندن {orig_zip_name}/{filename}: {e}\n")
                                await update_live_progress(orig_zip_name, z_idx - 1, zip_done_files, zip_total_files)

                await asyncio.gather(*[_zip_acc_worker(i, t) for i, t in enumerate(json_targets)])
                overall_stats["zips_done"] = z_idx
                await update_live_progress(orig_zip_name, z_idx, zip_total_files, zip_total_files)

            except Exception as e:
                overall_stats["zip_errors"] += 1
                overall_stats["zips_done"] = z_idx
                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطا در باز کردن فایل زیپ {orig_zip_name}: {e}\n")

        await update_live_progress("اتمام تمامی فایل‌ها", total_batches, 0, 0, force=True)
        try:
            await live_msg.delete()
        except Exception:
            pass

        elapsed_total = int(time.time() - start_time)
        mins, secs = divmod(elapsed_total, 60)

        summary_cap = (
            f"✅ <b>عملیات پردازش دسته‌ای فایل‌های ZIP به پایان رسید.</b>\n\n"
            f"📦 <b>تعداد فایل‌های زیپ پردازش‌شده:</b> <code>{total_batches}</code>\n"
            f"👥 <b>کل اکانت‌های داخل زیپ‌ها:</b> <code>{overall_stats['total_accounts_found']}</code>\n"
            f"🔗 <b>مجموع لینک‌های جدید ساخته‌شده:</b> <b><code>{len(healthy_links)}</code></b>\n"
            f"  ├─ ♻️ نوسازی کامل (Refresh+Access): <code>{overall_stats['refreshed']}</code>\n"
            f"  └─ 🟢 سالم با Access فعلی: <code>{overall_stats['access_only']}</code>\n"
            f"⏭ <b>رد شده (تکراری — موجود در دیتابیس):</b> <code>{overall_stats['skipped_duplicate']}</code>\n"
            f"💀 <b>رد شده (توکن باطل/سوخته):</b> <code>{overall_stats['dead']}</code>\n"
            f"⚠️ <b>خطای شبکه/پروکسی:</b> <code>{overall_stats['proxy_error']}</code>\n"
            f"⏱ <b>زمان کل پردازش:</b> <code>{mins} دقیقه و {secs} ثانیه</code>"
        )

        if healthy_links:
            links_out_txt = (
                f"🔗 لیست لینک‌های دائمی جدید استخراج‌شده از {total_batches} فایل زیپ (تعداد: {len(healthy_links)})\n"
                f"شماره‌های تکراری موجود در دیتابیس ({overall_stats['skipped_duplicate']} مورد) نادیده گرفته شدند.\n"
                + "=" * 60 + "\n\n"
            )
            for idx, item in enumerate(healthy_links, 1):
                links_out_txt += f"{idx}. 📱 شماره: {item['phone']} | 📦 [{item['zip']}]\n🔗 {item['link']}\n\n"
            file_out = io.BytesIO(links_out_txt.encode('utf-8'))
            await bot.send_document(
                chat_id=chat_id,
                document=file_out,
                filename=f"Batch_Valid_Zip_Links_{ts}.txt",
                caption=summary_cap,
                parse_mode='HTML'
            )
        else:
            await bot.send_message(
                chat_id=chat_id,
                text=summary_cap + "\n\n⚠️ هیچ لینک جدیدی ساخته نشد (اکانت‌ها یا تکراری بودند یا منقضی).",
                parse_mode='HTML'
            )

        try:
            full_zip_log = (
                f"=== گزارش کامل پردازش دسته‌ای {total_batches} فایل زیپ | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
                f"اکانت‌های اولیه دیتابیس: {initial_db_count} | کل اکانت‌های زیپ: {overall_stats['total_accounts_found']} | "
                f"لینک جدید: {len(healthy_links)} | تکراری رد شده: {overall_stats['skipped_duplicate']} | باطل: {overall_stats['dead']}\n"
                + "=" * 65 + "\n\n"
            )
            full_zip_log += "".join(detail_logs)
            full_zip_log += "\n\n=== لاگ درخواست‌های سرور (HTTP) ===\n"
            full_zip_log += "".join(api.request_logs)
            log_io = io.BytesIO(full_zip_log.encode('utf-8'))
            await bot.send_document(
                chat_id=chat_id,
                document=log_io,
                filename=f"Batch_Zip_Validation_Log_{ts}.txt",
                caption=f"📄 لاگ کامل بررسی {total_batches} فایل زیپ"
            )
        except Exception as e:
            logging.error(f"Error sending batch zip log: {e}")

        await bot.send_message(
            chat_id=chat_id,
            text="⚙️ بازگشت به پنل مدیریت:",
            reply_markup=get_admin_keyboard()
        )


# ==========================================
# اجرای عملیات ویژه: حذف دسته‌ای اکانت‌های موجود در فایل‌های ZIP / لینک / TXT از دیتابیس
# ==========================================
async def process_delete_zips_from_db(bot, chat_id: int, batch_items: list):
    total_batches = len(batch_items)
    ts = int(time.time())

    live_msg = await bot.send_message(
        chat_id=chat_id,
        text=f"⏳ <b>عملیات حذف دسته‌ای اکانت‌های {total_batches} بسته ورودی از دیتابیس در صف قرار گرفت...</b>\nلطفاً منتظر بمانید.",
        parse_mode='HTML'
    )

    async with zip_queue_lock:
        try:
            await live_msg.edit_text(
                "🔍 <b>در حال فهرست‌برداری از اکانت‌ها و لینک‌های فعلی دیتابیس برای تطبیق سریع و دقیق...</b>",
                parse_mode='HTML'
            )
        except Exception:
            pass

        # ۱. ساخت نقشه کامل از دیتابیس فعلی (شماره‌ها، توکن‌ها و لینک‌ها)
        raw_account_keys_by_phone = {}
        raw_active_keys_by_phone = {}
        link_ids_by_phone = {}
        phone_by_link_id = {}
        phone_by_token = {}

        try:
            acc_keys = await redis_client.keys("account:*")
            for i in range(0, len(acc_keys), 500):
                chunk = acc_keys[i:i + 500]
                pipe = redis_client.pipeline()
                for k in chunk:
                    pipe.hgetall(k)
                results = await pipe.execute()
                for k, tok_data in zip(chunk, results):
                    raw_p = k.replace("account:", "")
                    norm_p = clean_digits(raw_p)
                    if norm_p:
                        raw_account_keys_by_phone.setdefault(norm_p, set()).add(k)
                    if isinstance(tok_data, dict):
                        a_t = tok_data.get("access_token")
                        r_t = tok_data.get("refresh_token")
                        if a_t and norm_p:
                            phone_by_token[a_t] = norm_p
                        if r_t and norm_p:
                            phone_by_token[r_t] = norm_p

            active_keys = await redis_client.keys("phone_active_link:*")
            for i in range(0, len(active_keys), 500):
                chunk = active_keys[i:i + 500]
                pipe = redis_client.pipeline()
                for k in chunk:
                    pipe.get(k)
                results = await pipe.execute()
                for k, link_val in zip(chunk, results):
                    raw_p = k.replace("phone_active_link:", "")
                    norm_p = clean_digits(raw_p)
                    if norm_p:
                        raw_active_keys_by_phone.setdefault(norm_p, set()).add(k)
                    if link_val and "/acc/" in str(link_val):
                        lid = str(link_val).split("/acc/")[-1].strip()
                        if lid:
                            if norm_p:
                                link_ids_by_phone.setdefault(norm_p, set()).add(lid)
                                phone_by_link_id[lid] = norm_p

            acc_link_keys = await redis_client.keys("acc_link:*")
            for i in range(0, len(acc_link_keys), 500):
                chunk = acc_link_keys[i:i + 500]
                pipe = redis_client.pipeline()
                for k in chunk:
                    pipe.get(k)
                results = await pipe.execute()
                for k, raw_json in zip(chunk, results):
                    lid = k.replace("acc_link:", "").strip()
                    if not raw_json:
                        continue
                    try:
                        d_obj = json.loads(raw_json)
                        a_t, r_t, extr_p = extract_tokens_from_json_data(d_obj)
                        if extr_p:
                            link_ids_by_phone.setdefault(extr_p, set()).add(lid)
                            phone_by_link_id[lid] = extr_p
                            if a_t:
                                phone_by_token[a_t] = extr_p
                            if r_t:
                                phone_by_token[r_t] = extr_p
                    except Exception:
                        pass

            raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
            for item in raw_logs:
                try:
                    entry = json.loads(item)
                    p = clean_digits(str(entry.get("phone", "")))
                    l_url = str(entry.get("link", ""))
                    if p and "/acc/" in l_url:
                        lid = l_url.split("/acc/")[-1].strip()
                        if lid:
                            link_ids_by_phone.setdefault(p, set()).add(lid)
                            if lid not in phone_by_link_id:
                                phone_by_link_id[lid] = p
                except Exception:
                    pass
        except Exception as e:
            logging.error(f"Error building DB index for batch delete: {e}")

        initial_db_accounts = len(raw_account_keys_by_phone)
        existing_link_ids_set = {k.replace("acc_link:", "").strip() for k in acc_link_keys} if 'acc_link_keys' in locals() else set()

        stats = {
            "zips_done": 0,
            "total_zips": total_batches,
            "total_targets_found": 0,
            "processed_targets": 0,
            "deleted_accounts": 0,
            "deleted_links": 0,
            "not_in_db": 0,
            "duplicate_in_batch": 0,
            "invalid_items": 0
        }

        deleted_phones_tracker = set()
        deleted_lids_tracker = set()
        deleted_records_report = []
        detail_logs = []
        last_edit_time = [0.0]
        start_time = time.time()

        async def update_delete_progress(current_zip_name: str, current_zip_idx: int, force: bool = False):
            now = time.time()
            if not force and (now - last_edit_time[0] < 2.2):
                return
            last_edit_time[0] = now

            elapsed = int(now - start_time)
            mins, secs = divmod(elapsed, 60)
            time_str = f"{mins}:{secs:02d}"

            zip_pct = int((current_zip_idx / max(total_batches, 1)) * 100)
            bar_len = 12
            filled = int(bar_len * zip_pct / 100)
            bar = "█" * filled + "░" * (bar_len - filled)

            status_text = (
                f"🗑 <b>پاکسازی زنده اکانت‌های ارسالی از دیتابیس</b>\n"
                f"<code>[{bar}] {zip_pct}%</code> | ⏱ زمان: <code>{time_str}</code>\n\n"
                f"📦 <b>بسته‌های پردازش‌شده:</b> <code>{current_zip_idx}/{total_batches}</code>\n"
                f"📂 <b>فایل فعلی:</b> <code>{html.escape(current_zip_name[:35])}</code>\n"
                f"👥 <b>کل موارد بررسی‌شده:</b> <code>{stats['processed_targets']}/{stats['total_targets_found']}</code>\n"
                f"────────────────────\n"
                f"✅ <b>اکانت‌های حذف‌شده از دیتابیس:</b> <b><code>{stats['deleted_accounts']}</code></b>\n"
                f"🔗 <b>لینک‌های دائمی حذف‌شده:</b> <b><code>{stats['deleted_links']}</code></b>\n"
                f"➖ <b>موجود نبوده در دیتابیس:</b> <code>{stats['not_in_db']}</code>\n"
                f"⏭ <b>تکراری در فایل‌های ارسالی:</b> <code>{stats['duplicate_in_batch']}</code>"
            )
            try:
                await live_msg.edit_text(status_text, parse_mode='HTML')
            except Exception:
                pass

        for z_idx, b_item in enumerate(batch_items, 1):
            orig_zip_name = b_item.get("file_name", f"Batch_{z_idx}")
            await update_delete_progress(orig_zip_name, z_idx - 1, force=(z_idx == 1))

            try:
                targets = await iterate_targets_from_batch_item(bot, b_item)
                if not targets:
                    detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ فایل {orig_zip_name} فاقد اکانت یا لینک معتبر بود.\n")
                    stats["zips_done"] = z_idx
                    continue

                stats["total_targets_found"] += len(targets)
                redis_keys_to_delete = set()

                for target in targets:
                    stats["processed_targets"] += 1
                    t_type = target.get("type")
                    source_name = target.get("source", "")
                    cand_phone = None
                    cand_lid = None

                    if t_type == "json":
                        data = target.get("data")
                        acc_tok, ref_tok, extr_phone = extract_tokens_from_json_data(data)
                        fn_digits = clean_digits(os.path.basename(source_name).replace(".json", ""))
                        cand_phone = (
                            extr_phone
                            or (fn_digits if re.match(r"^09\d{9}$", fn_digits) or fn_digits in raw_account_keys_by_phone else None)
                            or phone_by_token.get(acc_tok)
                            or phone_by_token.get(ref_tok)
                        )
                    elif t_type == "url":
                        u_str = str(target.get("url") or source_name)
                        if "/acc/" in u_str:
                            cand_lid = u_str.split("/acc/")[-1].strip()
                            cand_phone = phone_by_link_id.get(cand_lid)
                    elif t_type == "phone":
                        cand_phone = clean_digits(str(target.get("phone") or source_name))

                    if not cand_phone and not cand_lid:
                        stats["invalid_items"] += 1
                        if len(detail_logs) < 10000:
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {orig_zip_name}/{source_name} | شماره یا لینک معتبر یافت نشد.\n")
                        continue

                    if (cand_phone and cand_phone in deleted_phones_tracker) or (cand_lid and cand_lid in deleted_lids_tracker and not cand_phone):
                        stats["duplicate_in_batch"] += 1
                        continue

                    # بررسی وجود در دیتابیس
                    acc_keys_for_p = raw_account_keys_by_phone.get(cand_phone, set()) if cand_phone else set()
                    act_keys_for_p = raw_active_keys_by_phone.get(cand_phone, set()) if cand_phone else set()
                    lids_for_p = set(link_ids_by_phone.get(cand_phone, set())) if cand_phone else set()
                    if cand_lid and cand_lid in existing_link_ids_set:
                        lids_for_p.add(cand_lid)

                    exists_in_db = bool(acc_keys_for_p or act_keys_for_p or lids_for_p)
                    if not exists_in_db:
                        stats["not_in_db"] += 1
                        if len(detail_logs) < 10000:
                            detail_logs.append(
                                f"[{time.strftime('%H:%M:%S')}] ➖ {cand_phone or cand_lid} ({orig_zip_name}) | در دیتابیس وجود نداشت.\n"
                            )
                        continue

                    # ثبت کلیدها برای حذف از Redis
                    if cand_phone:
                        deleted_phones_tracker.add(cand_phone)
                        redis_keys_to_delete.add(f"account:{cand_phone}")
                        redis_keys_to_delete.add(f"phone_active_link:{cand_phone}")
                        redis_keys_to_delete.add(f"otp_cooldown:{cand_phone}")
                        for rk in acc_keys_for_p:
                            redis_keys_to_delete.add(rk)
                        for ak in act_keys_for_p:
                            redis_keys_to_delete.add(ak)

                    deleted_links_for_this = 0
                    for lid in lids_for_p:
                        if lid not in deleted_lids_tracker:
                            deleted_lids_tracker.add(lid)
                            redis_keys_to_delete.add(f"acc_link:{lid}")
                            deleted_links_for_this += 1

                    stats["deleted_accounts"] += 1
                    stats["deleted_links"] += deleted_links_for_this
                    deleted_records_report.append({
                        "phone": cand_phone or "بدون شماره",
                        "links_deleted": deleted_links_for_this,
                        "zip": orig_zip_name
                    })
                    if len(detail_logs) < 10000:
                        detail_logs.append(
                            f"[{time.strftime('%H:%M:%S')}] 🗑 {cand_phone or cand_lid} ({orig_zip_name}) | از دیتابیس حذف شد (تعداد لینک حذف‌شده: {deleted_links_for_this})\n"
                        )

                # اجرای حذف دسته‌ای کلیدهای این فایل در Redis
                if redis_keys_to_delete:
                    keys_list = list(redis_keys_to_delete)
                    for i in range(0, len(keys_list), 500):
                        await redis_client.delete(*keys_list[i:i + 500])

                stats["zips_done"] = z_idx
                await update_delete_progress(orig_zip_name, z_idx)

            except Exception as e:
                stats["zips_done"] = z_idx
                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطا در پردازش {orig_zip_name}: {e}\n")

        # پاکسازی لاگ لینک‌های سراسری (global_link_logs) از شماره‌ها و لینک‌های حذف‌شده
        if deleted_phones_tracker or deleted_lids_tracker:
            try:
                raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
                if raw_logs:
                    kept_logs = []
                    for item in raw_logs:
                        try:
                            entry = json.loads(item)
                            p = clean_digits(str(entry.get("phone", "")))
                            l_url = str(entry.get("link", ""))
                            lid = l_url.split("/acc/")[-1].strip() if "/acc/" in l_url else ""
                            if (p and p in deleted_phones_tracker) or (lid and lid in deleted_lids_tracker):
                                continue
                            kept_logs.append(item)
                        except Exception:
                            kept_logs.append(item)
                    if len(kept_logs) != len(raw_logs):
                        pipe = redis_client.pipeline()
                        pipe.delete("global_link_logs")
                        if kept_logs:
                            pipe.rpush("global_link_logs", *kept_logs)
                        await pipe.execute()
            except Exception as e:
                logging.error(f"Error cleaning global_link_logs after delete: {e}")

        await update_delete_progress("اتمام پاکسازی", total_batches, force=True)
        try:
            await live_msg.delete()
        except Exception:
            pass

        remaining_acc_keys = await redis_client.keys("account:*")
        elapsed_total = int(time.time() - start_time)
        mins, secs = divmod(elapsed_total, 60)

        summary_cap = (
            f"✅ <b>عملیات حذف اکانت‌های ارسالی از دیتابیس به پایان رسید.</b>\n\n"
            f"📦 <b>تعداد بسته‌های بررسی‌شده:</b> <code>{total_batches}</code>\n"
            f"👥 <b>کل اکانت‌های داخل فایل‌ها:</b> <code>{stats['total_targets_found']}</code>\n"
            f"🗑 <b>اکانت‌های حذف‌شده از دیتابیس:</b> <b><code>{stats['deleted_accounts']}</code></b>\n"
            f"🔗 <b>لینک‌های دائمی حذف‌شده:</b> <b><code>{stats['deleted_links']}</code></b>\n"
            f"➖ <b>موجود نبوده در دیتابیس:</b> <code>{stats['not_in_db']}</code>\n"
            f"⏭ <b>تکراری در فایل‌های ارسالی:</b> <code>{stats['duplicate_in_batch']}</code>\n"
            f"📊 <b>اکانت‌های باقی‌مانده در دیتابیس:</b> <code>{len(remaining_acc_keys)}</code> (از <code>{initial_db_accounts}</code>)\n"
            f"⏱ <b>زمان کل عملیات:</b> <code>{mins} دقیقه و {secs} ثانیه</code>"
        )

        if deleted_records_report:
            del_txt = (
                f"🗑 لیست اکانت‌های حذف‌شده از دیتابیس (تعداد: {len(deleted_records_report)})\n"
                + "=" * 60 + "\n\n"
            )
            for idx, item in enumerate(deleted_records_report, 1):
                del_txt += f"{idx}. 📱 شماره: {item['phone']} | 🔗 لینک حذف‌شده: {item['links_deleted']} | 📦 [{item['zip']}]\n"
            await bot.send_document(
                chat_id=chat_id,
                document=io.BytesIO(del_txt.encode('utf-8')),
                filename=f"Deleted_Accounts_From_DB_{ts}.txt",
                caption=summary_cap,
                parse_mode='HTML'
            )
        else:
            await bot.send_message(
                chat_id=chat_id,
                text=summary_cap + "\n\n⚠️ هیچ‌یک از اکانت‌های داخل فایل‌های ارسالی در دیتابیس موجود نبودند.",
                parse_mode='HTML'
            )

        try:
            full_log = (
                f"=== گزارش کامل حذف دسته‌ای اکانت‌های زیپ/لینک از دیتابیس | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
                f"کل بررسی‌شده: {stats['total_targets_found']} | حذف‌شده: {stats['deleted_accounts']} | لینک حذف‌شده: {stats['deleted_links']} | ناموجود: {stats['not_in_db']}\n"
                + "=" * 65 + "\n\n"
                + "".join(detail_logs)
            )
            await bot.send_document(
                chat_id=chat_id,
                document=io.BytesIO(full_log.encode('utf-8')),
                filename=f"Batch_Delete_DB_Log_{ts}.txt",
                caption="📄 لاگ کامل جزئیات حذف اکانت‌ها از دیتابیس"
            )
        except Exception as e:
            logging.error(f"Error sending delete zip log: {e}")

        await bot.send_message(
            chat_id=chat_id,
            text="⚙️ بازگشت به پنل مدیریت:",
            reply_markup=get_admin_keyboard()
        )


# ==========================================
# اجرای عملیات ۲، ۳، ۴ و ۵ روی لینک‌ها یا فایل‌های زیپ ارسالی کاربر
# (بررسی همه کدهای تخفیف، ساخت آدرس، بررسی سابقه خرید، حذف آدرس)
# ==========================================
async def process_user_submitted_targets_batch(bot, chat_id: int, mode: str, batch_items: list, addr_config: dict = None, addr_desc: str = ""):
    ts = int(time.time())
    title = BATCH_MODE_TITLES.get(mode, "پردازش دسته‌ای اکانت‌های ارسالی")

    live_msg = await bot.send_message(
        chat_id=chat_id,
        text=f"⏳ <b>{title}</b>\nدر حال استخراج اکانت‌ها از {len(batch_items)} ورودی ارسالی...",
        parse_mode='HTML'
    )

    async with zip_queue_lock:
        all_targets = []
        for b_item in batch_items:
            extracted = await iterate_targets_from_batch_item(bot, b_item)
            all_targets.extend(extracted)

        if not all_targets:
            try:
                await live_msg.edit_text("❌ هیچ لینک یا فایل اکانت معتبری در ورودی‌های ارسالی یافت نشد.")
            except Exception:
                pass
            await bot.send_message(chat_id=chat_id, text="⚙️ بازگشت به پنل مدیریت:", reply_markup=get_admin_keyboard())
            return

        total_targets = len(all_targets)
        proxies_list = await get_all_proxies_from_db()
        api = OkalaAPI(proxies_list=proxies_list)
        loop = asyncio.get_running_loop()
        phone_to_latest_link = await build_phone_to_link_map()
        sem = asyncio.Semaphore(25)
        lock = asyncio.Lock()

        done = 0
        last_edit_time = [0.0]
        start_time = time.time()

        # متغیرهای خروجی مشترک و اختصاصی هر حالت
        detail_logs = []
        amount_counter = Counter()
        discount_results = []
        total_vouchers_found = 0
        multi_discount_accounts = 0

        addr_success_list = []
        addr_stats = {"success": 0, "failed": 0, "expired": 0, "total_deleted": 0}

        orders_with_list = []
        orders_no_list = []
        orders_stats = {"has_orders": 0, "no_orders": 0, "failed": 0, "total_orders": 0}

        temp_out_dir = tempfile.mkdtemp()
        discounted_json_dir = os.path.join(temp_out_dir, "Discounted_Accounts", "accounts")
        updated_addr_json_dir = os.path.join(temp_out_dir, "Address_Updated_Accounts", "accounts")
        has_discounted_json = False
        has_updated_addr_json = False

        async def _update_progress(force=False):
            now = time.time()
            if not force and (now - last_edit_time[0] < 2.2):
                return
            last_edit_time[0] = now
            pct = int((done / max(total_targets, 1)) * 100)
            filled = int(12 * pct / 100)
            bar = "█" * filled + "░" * (12 - filled)

            if mode == 'user_discount_check':
                body = (
                    f"🎁 اکانت دارای تخفیف: <b>{len(discount_results)}</b> (چندکدی: <b>{multi_discount_accounts}</b>)\n"
                    f"🎟 کل کدهای تخفیف یافت‌شده: <b>{total_vouchers_found}</b>"
                )
            elif mode == 'user_create_address':
                body = (
                    f"🗺 آدرس: <code>{html.escape(addr_desc[:35])}</code>\n"
                    f"✅ ثبت موفق: <b>{addr_stats['success']}</b> | 🔒 منقضی: <b>{addr_stats['expired']}</b> | ❌ خطا: <b>{addr_stats['failed']}</b>"
                )
            elif mode == 'user_check_orders':
                body = (
                    f"✨ بدون خرید (۰ سفارش): <b>{orders_stats['no_orders']}</b>\n"
                    f"🛍 دارای خرید: <b>{orders_stats['has_orders']}</b> (مجموع سفارش: <b>{orders_stats['total_orders']}</b>)\n"
                    f"❌ خطا/منقضی: <b>{orders_stats['failed']}</b>"
                )
            else:
                body = (
                    f"✅ اکانت موفق: <b>{addr_stats['success']}</b>\n"
                    f"🗑 آدرس‌های حذف‌شده: <b>{addr_stats['total_deleted']}</b> | ❌ خطا: <b>{addr_stats['failed']}</b>"
                )

            try:
                await live_msg.edit_text(
                    f"⚡ <b>{title}</b>\n"
                    f"<code>[{bar}] {pct}%</code> — <b>{done}/{total_targets}</b>\n\n"
                    f"{body}",
                    parse_mode='HTML'
                )
            except Exception:
                pass

        async def _worker(idx, target):
            nonlocal done, total_vouchers_found, multi_discount_accounts, has_discounted_json, has_updated_addr_json
            async with sem:
                try:
                    t_type = target["type"]
                    source_label = target["source"]
                    zip_name = target.get("zip_name", "")
                    data = target.get("data")
                    orig_url = target.get("url")
                    local_lid = None

                    if t_type == "url" and orig_url:
                        data, local_lid = await resolve_account_data_from_url(orig_url, loop)

                    if not isinstance(data, dict):
                        async with lock:
                            done += 1
                            addr_stats["failed"] += 1
                            orders_stats["failed"] += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {source_label} | دریافت اطلاعات اکانت ناموفق بود.\n")
                            await _update_progress()
                        return

                    acc_tok, ref_tok, extr_phone = extract_tokens_from_json_data(data)
                    phone = extr_phone or clean_digits(os.path.basename(source_label).replace('.json', '')) or f"acc_{idx+1}"
                    proxy_dict = get_proxy_by_index(proxies_list, idx)

                    if not acc_tok and ref_tok:
                        st, r_acc, r_ref, _, _ = await loop.run_in_executor(
                            executor, api.refresh_token_sequential_proxy, ref_tok, idx
                        )
                        if st == "success" and r_acc:
                            data = update_tokens_in_data(data, acc_tok, r_acc, ref_tok, r_ref or ref_tok)
                            acc_tok = r_acc
                            ref_tok = r_ref or ref_tok

                    if not acc_tok:
                        async with lock:
                            done += 1
                            addr_stats["expired"] += 1
                            orders_stats["failed"] += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} ({source_label}) | فاقد توکن معتبر\n")
                            await _update_progress()
                        return

                    old_acc, old_ref = acc_tok, ref_tok

                    # --- حالت ۱: بررسی تمامی کدهای تخفیف زیپ/لینک ---
                    if mode == 'user_discount_check':
                        uid = get_user_id_from_token(acc_tok)
                        status, res = await loop.run_in_executor(
                            executor, api.check_discount_api, acc_tok, uid, proxy_dict, True
                        )
                        if status == 401 and ref_tok:
                            st, n_acc, n_ref, _, _ = await loop.run_in_executor(
                                executor, api.refresh_token_sequential_proxy, ref_tok, idx
                            )
                            if st == "success" and n_acc:
                                acc_tok = n_acc
                                ref_tok = n_ref or ref_tok
                                data = update_tokens_in_data(data, old_acc, acc_tok, old_ref, ref_tok)
                                uid = get_user_id_from_token(acc_tok) or uid
                                status, res = await loop.run_in_executor(
                                    executor, api.check_discount_api, acc_tok, uid, proxy_dict, True
                                )

                        valid_vouchers = extract_all_valid_discounts(res) if (status == 200 and isinstance(res, dict)) else []

                        if acc_tok != old_acc and phone:
                            await redis_client.hset(f"account:{phone}", mapping={"access_token": acc_tok, "refresh_token": ref_tok or ""})
                            if local_lid:
                                await redis_client.set(f"acc_link:{local_lid}", json.dumps(data, ensure_ascii=False))

                        if valid_vouchers:
                            link_out = orig_url or phone_to_latest_link.get(phone) or await redis_client.get(f"phone_active_link:{phone}")
                            if not link_out:
                                lid = str(uuid.uuid4())[:12]
                                await redis_client.set(f"acc_link:{lid}", json.dumps(data, ensure_ascii=False))
                                link_out = f"{WEB_DOMAIN}/acc/{lid}"
                                if phone:
                                    await redis_client.set(f"phone_active_link:{phone}", link_out)

                            max_amt_k = max((v['amount_k'] for v in valid_vouchers), default=0)
                            all_amts_k = [v['amount_k'] for v in valid_vouchers if v['amount_k'] > 0]

                            async with lock:
                                total_vouchers_found += len(valid_vouchers)
                                if len(valid_vouchers) >= 2:
                                    multi_discount_accounts += 1
                                for v in valid_vouchers:
                                    amount_counter[v['label']] += 1

                                discount_results.append({
                                    "phone": phone,
                                    "source": source_label,
                                    "zip_name": zip_name,
                                    "count": len(valid_vouchers),
                                    "max_amount": max_amt_k,
                                    "all_amounts": all_amts_k,
                                    "vouchers": valid_vouchers,
                                    "link": link_out
                                })

                                if t_type == "json":
                                    os.makedirs(discounted_json_dir, exist_ok=True)
                                    has_discounted_json = True
                                    safe_fn = os.path.basename(source_label)
                                    if not safe_fn.lower().endswith('.json'):
                                        safe_fn += '.json'
                                    out_fp = os.path.join(discounted_json_dir, f"{idx+1}_{safe_fn}")
                                    with open(out_fp, 'w', encoding='utf-8') as fw:
                                        json.dump(data, fw, ensure_ascii=False)

                                summary_v = " + ".join([f"{v['label']}({v['code']})" for v in valid_vouchers])
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 🎁 {phone} | {len(valid_vouchers)} کد: {summary_v} | {link_out}\n")
                        else:
                            async with lock:
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ➖ {phone} | بدون تخفیف (کد وضعیت: {status})\n")

                    # --- حالت ۲: ساخت آدرس برای لینک/زیپ ارسالی کاربر (بر اساس Main 9) ---
                    elif mode == 'user_create_address':
                        uid = get_numeric_customer_id_from_token(acc_tok, data)
                        status, res = await loop.run_in_executor(
                            executor, api.add_address_api, acc_tok, uid, addr_config, proxy_dict, True
                        )
                        if status == 401 and ref_tok:
                            st, n_acc, n_ref, _, _ = await loop.run_in_executor(
                                executor, api.refresh_token_sequential_proxy, ref_tok, idx
                            )
                            if st == "success" and n_acc:
                                acc_tok = n_acc
                                ref_tok = n_ref or ref_tok
                                data = update_tokens_in_data(data, old_acc, acc_tok, old_ref, ref_tok)
                                uid = get_numeric_customer_id_from_token(acc_tok, data) or uid
                                status, res = await loop.run_in_executor(
                                    executor, api.add_address_api, acc_tok, uid, addr_config, proxy_dict, True
                                )

                        if acc_tok != old_acc and phone:
                            await redis_client.hset(f"account:{phone}", mapping={"access_token": acc_tok, "refresh_token": ref_tok or ""})
                            if local_lid:
                                await redis_client.set(f"acc_link:{local_lid}", json.dumps(data, ensure_ascii=False))

                        link_out = orig_url or phone_to_latest_link.get(phone) or await redis_client.get(f"phone_active_link:{phone}")
                        if not link_out:
                            lid = str(uuid.uuid4())[:12]
                            await redis_client.set(f"acc_link:{lid}", json.dumps(data, ensure_ascii=False))
                            link_out = f"{WEB_DOMAIN}/acc/{lid}"
                            if phone:
                                await redis_client.set(f"phone_active_link:{phone}", link_out)

                        async with lock:
                            if status == 200:
                                addr_stats["success"] += 1
                                addr_success_list.append({"phone": phone, "link": link_out, "source": source_label})
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ✅ {phone} | آدرس با موفقیت ثبت شد: {link_out}\n")
                                if t_type == "json":
                                    os.makedirs(updated_addr_json_dir, exist_ok=True)
                                    has_updated_addr_json = True
                                    safe_fn = os.path.basename(source_label)
                                    if not safe_fn.lower().endswith('.json'):
                                        safe_fn += '.json'
                                    out_fp = os.path.join(updated_addr_json_dir, f"{idx+1}_{safe_fn}")
                                    with open(out_fp, 'w', encoding='utf-8') as fw:
                                        json.dump(data, fw, ensure_ascii=False)
                            elif status == 401:
                                addr_stats["expired"] += 1
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 🔒 {phone} | توکن منقضی شده است.\n")
                            else:
                                addr_stats["failed"] += 1
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} | خطا در ثبت آدرس ({status}): {str(res)[:180]}\n")

                    # --- حالت ۳: بررسی سابقه خرید لینک/زیپ ارسالی کاربر ---
                    elif mode == 'user_check_orders':
                        cust_uid = get_numeric_customer_id_from_token(acc_tok, data)
                        ord_status, ord_res = await loop.run_in_executor(
                            executor, api.get_orders_api, acc_tok, proxy_dict, False, True, cust_uid, data
                        )
                        if ord_status == 401 and ref_tok:
                            st, n_acc, n_ref, _, _ = await loop.run_in_executor(
                                executor, api.refresh_token_sequential_proxy, ref_tok, idx
                            )
                            if st == "success" and n_acc:
                                acc_tok = n_acc
                                ref_tok = n_ref or ref_tok
                                data = update_tokens_in_data(data, old_acc, acc_tok, old_ref, ref_tok)
                                cust_uid = get_numeric_customer_id_from_token(acc_tok, data) or cust_uid
                                ord_status, ord_res = await loop.run_in_executor(
                                    executor, api.get_orders_api, acc_tok, proxy_dict, False, True, cust_uid, data
                                )

                        if acc_tok != old_acc and phone:
                            await redis_client.hset(f"account:{phone}", mapping={"access_token": acc_tok, "refresh_token": ref_tok or ""})
                            if local_lid:
                                await redis_client.set(f"acc_link:{local_lid}", json.dumps(data, ensure_ascii=False))

                        link_out = orig_url or phone_to_latest_link.get(phone) or await redis_client.get(f"phone_active_link:{phone}")
                        if not link_out:
                            lid = str(uuid.uuid4())[:12]
                            await redis_client.set(f"acc_link:{lid}", json.dumps(data, ensure_ascii=False))
                            link_out = f"{WEB_DOMAIN}/acc/{lid}"
                            if phone:
                                await redis_client.set(f"phone_active_link:{phone}", link_out)

                        ord_ok, has_ord, ord_cnt = parse_orders_response(ord_status, ord_res)
                        async with lock:
                            if not ord_ok:
                                orders_stats["failed"] += 1
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} | خطا در استعلام خرید (کد: {ord_status})\n")
                            elif has_ord:
                                orders_stats["has_orders"] += 1
                                orders_stats["total_orders"] += ord_cnt
                                orders_with_list.append({"phone": phone, "count": ord_cnt, "link": link_out})
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 🛍 {phone} | دارای {ord_cnt} سفارش | {link_out}\n")
                            else:
                                orders_stats["no_orders"] += 1
                                orders_no_list.append({"phone": phone, "link": link_out})
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ✨ {phone} | بدون سابقه خرید (۰ سفارش) | {link_out}\n")

                    # --- حالت ۴: حذف آدرس‌های لینک/زیپ ارسالی کاربر ---
                    elif mode == 'user_delete_addresses':
                        uid = get_numeric_customer_id_from_token(acc_tok, data)
                        deleted_cnt = 0
                        ok_flag = True
                        for attempt in range(5):
                            st_a, res_a = await loop.run_in_executor(executor, api.get_addresses_api, acc_tok, proxy_dict, True)
                            if st_a == 401 and ref_tok:
                                st_r, n_acc, n_ref, _, _ = await loop.run_in_executor(executor, api.refresh_token_sequential_proxy, ref_tok, idx)
                                if st_r == "success" and n_acc:
                                    acc_tok = n_acc
                                    ref_tok = n_ref or ref_tok
                                    st_a, res_a = await loop.run_in_executor(executor, api.get_addresses_api, acc_tok, proxy_dict, True)
                                else:
                                    ok_flag = False
                                    break
                            addrs = (res_a.get('data') or {}).get('customerAddressResponseItems') if (st_a == 200 and isinstance(res_a, dict)) else []
                            if not addrs and uid:
                                st_r2, res_r2 = await loop.run_in_executor(executor, api.get_address_react_api, acc_tok, uid, proxy_dict, True)
                                if st_r2 == 200 and isinstance(res_r2, dict) and isinstance(res_r2.get('data'), list):
                                    addrs = res_r2['data']
                            if not addrs:
                                break
                            round_del = 0
                            for ad in addrs:
                                aid = ad.get('id') if isinstance(ad, dict) else None
                                if aid:
                                    d_st, _ = await loop.run_in_executor(executor, api.delete_address_api, acc_tok, aid, proxy_dict, True)
                                    if d_st == 200:
                                        deleted_cnt += 1
                                        round_del += 1
                            if round_del == 0:
                                break

                        async with lock:
                            if ok_flag:
                                addr_stats["success"] += 1
                                addr_stats["total_deleted"] += deleted_cnt
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ✅ {phone} | حذف شد: {deleted_cnt} آدرس\n")
                            else:
                                addr_stats["failed"] += 1
                                detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} | خطا در حذف آدرس\n")

                    async with lock:
                        done += 1
                        await _update_progress()

                except Exception as e:
                    async with lock:
                        done += 1
                        addr_stats["failed"] += 1
                        orders_stats["failed"] += 1
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطای پردازش اکانت #{idx+1}: {e}\n")
                        await _update_progress()

        await asyncio.gather(*[_worker(i, t) for i, t in enumerate(all_targets)])
        await _update_progress(force=True)

        try:
            await live_msg.delete()
        except Exception:
            pass

        # --- ارسال خروجی‌ها بر اساس حالت ---
        if mode == 'user_discount_check':
            discount_results.sort(key=lambda x: (x['max_amount'], x['count']), reverse=True)
            breakdown_lines = [f"▫️ تخفیف <b>{lbl}</b>: <code>{cnt}</code> کد" for lbl, cnt in amount_counter.most_common()]
            breakdown_str = ("\n📋 <b>تفکیک کل کدهای تخفیف:</b>\n" + "\n".join(breakdown_lines) + "\n") if breakdown_lines else ""

            summary_text = (
                f"🎁 <b>گزارش بررسی تخفیف لینک/زیپ ارسالی:</b>\n\n"
                f"👥 <b>کل اکانت‌های بررسی‌شده:</b> <code>{total_targets}</code>\n"
                f"🎁 <b>اکانت‌های دارای تخفیف:</b> <code>{len(discount_results)}</code>\n"
                f"✨ <b>اکانت‌های دارای ۲ یا چند کد تخفیف همزمان:</b> <code>{multi_discount_accounts}</code>\n"
                f"🎟 <b>مجموع کل کدهای تخفیف یافت‌شده:</b> <code>{total_vouchers_found}</code>\n"
                f"{breakdown_str}"
            )
            await bot.send_message(chat_id=chat_id, text=summary_text, parse_mode='HTML')

            if discount_results:
                rep_lines = [
                    f"🎁 گزارش کامل اکانت‌های دارای تخفیف ({len(discount_results)} اکانت — مجموع {total_vouchers_found} کد فعال)\n"
                    + "=" * 65 + "\n"
                ]
                grouped_by_lbl = {}
                for r in discount_results:
                    amts_s = " + ".join(str(a) for a in r['all_amounts']) if r['all_amounts'] else str(r['max_amount'])
                    rep_lines.append(
                        f"📱 شماره: {r['phone']} | تعداد کد: {r['count']} | بیشترین مبلغ: {r['max_amount']} هزار تومان | مبالغ تخفیف: {amts_s}"
                    )
                    for idx_v, v in enumerate(r['vouchers'], 1):
                        min_s = f" | حداقل خرید: {v['min_order_toman']:,} تومان" if v['min_order_toman'] > 0 else ""
                        rep_lines.append(f"   {idx_v}. 🎁 {v['detail_val']} | کد: {v['code']}{min_s} | انقضا: {v['expiration']}")
                        if r.get('link'):
                            grouped_by_lbl.setdefault(v['label'], []).append(r['link'])
                    rep_lines.append(f"🔗 {r['link']}\n" + "-" * 45 + "\n")

                await bot.send_document(
                    chat_id=chat_id,
                    document=io.BytesIO("\n".join(rep_lines).encode('utf-8')),
                    filename=f"User_Discounts_Full_Report_{ts}.txt",
                    caption=f"🎁 گزارش کامل تمامی کدهای تخفیف ({len(discount_results)} اکانت)"
                )

                if grouped_by_lbl:
                    cat_lines = [f"📂 تفکیک لینک‌های تخفیف بر اساس تمامی کدهای فعال هر اکانت\n" + "=" * 60 + "\n"]
                    for lbl, l_list in grouped_by_lbl.items():
                        unique_l = list(dict.fromkeys(l_list))
                        cat_lines.append(f"🎁 دسته تخفیف {lbl} (تعداد: {len(unique_l)}):\n" + "-" * 40)
                        cat_lines.extend(unique_l)
                        cat_lines.append("\n" + "=" * 60 + "\n")
                    await bot.send_document(
                        chat_id=chat_id,
                        document=io.BytesIO("\n".join(cat_lines).encode('utf-8')),
                        filename=f"User_Categorized_Discounts_{ts}.txt",
                        caption="📂 لینک‌های تفکیک‌شده بر اساس هر کد تخفیف"
                    )

                if has_discounted_json:
                    zip_base = os.path.join(temp_out_dir, "Discounted_Accounts_Output")
                    zip_file_path = await asyncio.to_thread(shutil.make_archive, zip_base, 'zip', os.path.join(temp_out_dir, "Discounted_Accounts"))
                    with open(zip_file_path, 'rb') as zf:
                        await bot.send_document(
                            chat_id=chat_id,
                            document=zf,
                            filename=f"Discounted_Accounts_{ts}.zip",
                            caption=f"📦 فایل ZIP اکانت‌های دارای تخفیف ({len(discount_results)} اکانت)"
                        )

        elif mode == 'user_create_address':
            summary_text = (
                f"✅ <b>عملیات ساخت آدرس برای لینک/زیپ ارسالی پایان یافت.</b>\n\n"
                f"🗺 <b>آدرس ثبت‌شده:</b> <code>{html.escape(addr_desc)}</code>\n"
                f"👥 <b>کل اکانت‌های بررسی‌شده:</b> <code>{total_targets}</code>\n"
                f"🟢 <b>ثبت آدرس موفق:</b> <code>{addr_stats['success']}</code>\n"
                f"🔒 <b>توکن منقضی:</b> <code>{addr_stats['expired']}</code>\n"
                f"🔴 <b>خطا:</b> <code>{addr_stats['failed']}</code>"
            )
            if addr_success_list:
                out_txt = f"📍 لیست اکانت‌هایی که آدرس با موفقیت برای آن‌ها ثبت شد ({len(addr_success_list)} اکانت)\nآدرس: {addr_desc}\n" + "=" * 55 + "\n\n"
                for idx, item in enumerate(addr_success_list, 1):
                    out_txt += f"{idx}. 📱 شماره: {item['phone']}\n🔗 {item['link']}\n\n"
                await bot.send_document(
                    chat_id=chat_id,
                    document=io.BytesIO(out_txt.encode('utf-8')),
                    filename=f"User_Address_Created_Links_{ts}.txt",
                    caption=summary_text,
                    parse_mode='HTML'
                )
            else:
                await bot.send_message(chat_id=chat_id, text=summary_text, parse_mode='HTML')

            if has_updated_addr_json:
                zip_base = os.path.join(temp_out_dir, "Address_Updated_Output")
                zip_file_path = await asyncio.to_thread(shutil.make_archive, zip_base, 'zip', os.path.join(temp_out_dir, "Address_Updated_Accounts"))
                with open(zip_file_path, 'rb') as zf:
                    await bot.send_document(
                        chat_id=chat_id,
                        document=zf,
                        filename=f"Address_Created_Accounts_{ts}.zip",
                        caption=f"📦 فایل ZIP اکانت‌های دارای آدرس جدید ({addr_stats['success']} اکانت)"
                    )

        elif mode == 'user_check_orders':
            summary_text = (
                f"📊 <b>گزارش بررسی سابقه خرید لینک/زیپ ارسالی:</b>\n\n"
                f"👥 <b>کل اکانت‌های بررسی‌شده:</b> <code>{total_targets}</code>\n"
                f"✨ <b>بدون سابقه خرید (۰ سفارش):</b> <code>{orders_stats['no_orders']}</code>\n"
                f"🛍 <b>دارای سابقه خرید:</b> <code>{orders_stats['has_orders']}</code> (مجموع <code>{orders_stats['total_orders']}</code> سفارش)\n"
                f"❌ <b>خطا یا توکن سوخته:</b> <code>{orders_stats['failed']}</code>"
            )
            await bot.send_message(chat_id=chat_id, text=summary_text, parse_mode='HTML')

            if orders_no_list:
                no_txt = f"✨ لیست اکانت‌های بدون سابقه خرید (تعداد: {len(orders_no_list)})\n" + "=" * 55 + "\n\n"
                for idx, r in enumerate(orders_no_list, 1):
                    no_txt += f"{idx}. 📱 شماره: {r['phone']}\n🔗 {r['link']}\n\n"
                await bot.send_document(
                    chat_id=chat_id,
                    document=io.BytesIO(no_txt.encode('utf-8')),
                    filename=f"User_No_Orders_Links_{ts}.txt",
                    caption=f"✨ اکانت‌های بدون سابقه خرید ({len(orders_no_list)} اکانت)"
                )

            if orders_with_list:
                orders_with_list.sort(key=lambda x: x['count'], reverse=True)
                yes_txt = f"🛍 لیست اکانت‌های دارای سابقه خرید (تعداد: {len(orders_with_list)})\n" + "=" * 55 + "\n\n"
                for idx, r in enumerate(orders_with_list, 1):
                    yes_txt += f"{idx}. 📱 شماره: {r['phone']} | 🛍 تعداد سفارش: {r['count']}\n🔗 {r['link']}\n\n"
                await bot.send_document(
                    chat_id=chat_id,
                    document=io.BytesIO(yes_txt.encode('utf-8')),
                    filename=f"User_Has_Orders_Links_{ts}.txt",
                    caption=f"🛍 اکانت‌های دارای سابقه خرید ({len(orders_with_list)} اکانت)"
                )

        elif mode == 'user_delete_addresses':
            await bot.send_message(
                chat_id=chat_id,
                text=(
                    f"✅ <b>حذف آدرس‌های لینک/زیپ ارسالی به پایان رسید.</b>\n\n"
                    f"👥 کل اکانت‌ها: <code>{total_targets}</code>\n"
                    f"🟢 موفق: <code>{addr_stats['success']}</code>\n"
                    f"🗑 مجموع آدرس‌های حذف‌شده: <code>{addr_stats['total_deleted']}</code>\n"
                    f"🔴 خطا: <code>{addr_stats['failed']}</code>"
                ),
                parse_mode='HTML'
            )

        try:
            full_log = f"=== لاگ عملیات {title} | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
            full_log += "".join(detail_logs) + "\n\n=== HTTP Logs ===\n" + "".join(api.request_logs)
            await bot.send_document(
                chat_id=chat_id,
                document=io.BytesIO(full_log.encode('utf-8')),
                filename=f"Batch_Operation_Log_{ts}.txt",
                caption="📄 لاگ کامل سرور و جزئیات پاسخ‌ها"
            )
        except Exception:
            pass

        shutil.rmtree(temp_out_dir, ignore_errors=True)
        await bot.send_message(chat_id=chat_id, text="⚙️ بازگشت به پنل مدیریت:", reply_markup=get_admin_keyboard())


async def trigger_batch_processing(update: Update, context: ContextTypes.DEFAULT_TYPE):
    """آغاز عملیات پس از تایید نهایی کاربر روی فایل‌های زیپ / لینک‌های جمع‌آوری شده"""
    user_id = update.effective_user.id
    if not await is_user_authorized(user_id):
        return

    mode = context.user_data.get('batch_collect_mode')
    queue = list(context.user_data.get('batch_items_queue', []))

    if not mode:
        if update.message:
            await update.message.reply_text("⚠️ شما در حالت جمع‌آوری فایل نیستید.")
        elif update.callback_query:
            await update.callback_query.answer("⚠️ شما در حالت جمع‌آوری فایل نیستید.", show_alert=True)
        return

    if not queue:
        if update.message:
            await update.message.reply_text("⚠️ هنوز هیچ فایل یا لینکی ارسال نکرده‌اید! ابتدا فایل‌ها یا لینک‌ها را بفرستید.")
        elif update.callback_query:
            await update.callback_query.answer("⚠️ هنوز هیچ فایل یا لینکی ارسال نکرده‌اید!", show_alert=True)
        return

    addr_config = context.user_data.get('batch_address_config') or DEFAULT_TEHRAN_ADDRESS.copy()
    addr_desc = context.user_data.get('batch_address_desc') or "آدرس پیش‌فرض تهران"

    # پاکسازی وضعیت جمع‌آوری
    context.user_data['batch_collect_mode'] = None
    context.user_data['admin_state'] = None
    context.user_data['admin_zip_action'] = None
    context.user_data['batch_items_queue'] = []
    status_msg_id = context.user_data.pop('batch_status_msg_id', None)

    if status_msg_id:
        try:
            await context.bot.delete_message(chat_id=user_id, message_id=status_msg_id)
        except Exception:
            pass

    if mode == 'zip_to_link':
        asyncio.create_task(process_batch_zips_to_links(context.bot, user_id, queue))
    elif mode == 'delete_zip_from_db':
        asyncio.create_task(process_delete_zips_from_db(context.bot, user_id, queue))
    else:
        asyncio.create_task(process_user_submitted_targets_batch(context.bot, user_id, mode, queue, addr_config, addr_desc))


async def handle_zip_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not await is_user_authorized(user_id):
        return

    orig_zip_name = update.message.document.file_name or "file.zip"
    if not orig_zip_name.lower().endswith('.zip'):
        await update.message.reply_text("❌ فایل ارسالی نامعتبر است. لطفاً فایل زیپ (.zip) ارسال کنید.")
        return

    # اگر در هیچ حالتی نبود، به صورت پیش‌فرض وارد حالت جمع‌آوری دسته‌ای تبدیل زیپ به لینک شود (نیازمند تایید کاربر)
    if not context.user_data.get('batch_collect_mode'):
        action = context.user_data.get('admin_zip_action', 'zip_to_link')
        if action == 'zip_discount_check':
            context.user_data['batch_collect_mode'] = 'user_discount_check'
        else:
            context.user_data['batch_collect_mode'] = 'zip_to_link'

    await enqueue_batch_input_message(update, context)


# ==========================================
# مینی‌سرور وب
# ==========================================
async def web_handler_get_account(request):
    link_id = request.match_info.get('link_id', '')
    data = await redis_client.get(f"acc_link:{link_id}")
    if data:
        return web.json_response(json.loads(data))
    return web.json_response({"error": "لینک نامعتبر است یا وجود ندارد."}, status=404)


async def start_web_server():
    app = web.Application()
    app.router.add_get('/acc/{link_id}', web_handler_get_account)
    runner = web.AppRunner(app)
    await runner.setup()
    port = int(os.environ.get("PORT", 8080))
    site = web.TCPSite(runner, '0.0.0.0', port)
    await site.start()


# ==========================================
# منوها و دکمه‌ها (شامل تمامی دکمه‌های جدید درخواستی)
# ==========================================
def get_main_keyboard(is_admin_user, active_tag_name=None):
    keyboard = [[InlineKeyboardButton("🔑 ورود به حساب (ساخت لینک دائمی)", callback_data="user_login")]]

    tag_btn_text = f"🏷 تغییر/حذف برچسب (فعال: {active_tag_name})" if active_tag_name else "🏷 تنظیم برچسب نشست (Tag)"
    keyboard.append([InlineKeyboardButton(tag_btn_text, callback_data="set_tag")])

    keyboard.append([
        InlineKeyboardButton("📂 برچسب‌های من", callback_data="my_tags"),
        InlineKeyboardButton("🔍 جستجوی لینک", callback_data="search_links")
    ])

    # دکمه‌های کاربردی سریع برای کاربران مجاز و ادمین‌ها
    keyboard.append([
        InlineKeyboardButton("📍 ساخت آدرس لینک/زیپ ارسالی", callback_data="admin_addr_user"),
        InlineKeyboardButton("🛍 سابقه خرید لینک/زیپ", callback_data="admin_orders_user")
    ])
    keyboard.append([
        InlineKeyboardButton("🔗 تبدیل دسته‌ای زیپ به لینک", callback_data="admin_zip_to_link"),
        InlineKeyboardButton("🎁 بررسی تخفیف لینک/زیپ", callback_data="admin_zip_discount")
    ])

    if is_admin_user:
        keyboard.append([InlineKeyboardButton("⚙️ پنل مدیریت کامل", callback_data="admin_panel")])
    return InlineKeyboardMarkup(keyboard)


def get_admin_keyboard():
    keyboard = [
        [InlineKeyboardButton("📊 آمار دیتابیس", callback_data="admin_stats"), InlineKeyboardButton("💾 حافظه Redis Railway", callback_data="admin_redis_memory")],
        [InlineKeyboardButton("📋 گزارش لینک‌های کاربران", callback_data="admin_users_report")],
        [InlineKeyboardButton("♻️ نوسازی توکن‌ها و احیای دائمی لینک‌ها", callback_data="admin_refresh_and_revive")],
        [InlineKeyboardButton("⏱ تنظیم چرخش خودکار توکن‌ها", callback_data="admin_auto_refresh_menu")],
        # --- دکمه‌های جدید ساخت آدرس (دیتابیس و لینک/زیپ ارسالی) ---
        [
            InlineKeyboardButton("📍 ساخت آدرس دیتابیس", callback_data="admin_addr_db"),
            InlineKeyboardButton("📍 ساخت آدرس لینک/زیپ", callback_data="admin_addr_user")
        ],
        # --- دکمه‌های جدید بررسی سابقه خرید (دیتابیس و لینک/زیپ ارسالی) ---
        [
            InlineKeyboardButton("🛍 سابقه خرید دیتابیس", callback_data="admin_orders_db"),
            InlineKeyboardButton("🛍 سابقه خرید لینک/زیپ", callback_data="admin_orders_user")
        ],
        # --- دکمه‌های تکمیلی حذف آدرس (از Main 9) ---
        [
            InlineKeyboardButton("🗑 حذف آدرس‌های دیتابیس", callback_data="admin_del_addr_db"),
            InlineKeyboardButton("🗑 حذف آدرس لینک/زیپ", callback_data="admin_del_addr_user")
        ],
        [InlineKeyboardButton("🧹 استخراج اکانت‌های خام (بدون خرید و آدرس)", callback_data="admin_extract_raw")],
        [InlineKeyboardButton("🎁 بررسی تخفیف دیتابیس (همه کدها)", callback_data="admin_check_discounts"), InlineKeyboardButton("📂 تفکیک فایل تخفیف", callback_data="admin_split_discount_file")],
        [InlineKeyboardButton("🔗 تبدیل دسته‌ای زیپ به لینک (۱۰۰ تا ۱۰۰۰+)", callback_data="admin_zip_to_link")],
        [InlineKeyboardButton("🗑 حذف اکانت‌های زیپ/لینک از دیتابیس", callback_data="admin_delete_zip_from_db")],
        [InlineKeyboardButton("🔍 بررسی تخفیف لینک/زیپ (همه کدها)", callback_data="admin_zip_discount")],
        [InlineKeyboardButton("🔗 استخراج لینک‌ها", callback_data="admin_export_links"), InlineKeyboardButton("🔑 استخراج توکن‌ها", callback_data="admin_export_tokens")],
        [InlineKeyboardButton("📥 استخراج شماره‌ها", callback_data="admin_export"), InlineKeyboardButton("🗑 پاکسازی کل دیتابیس", callback_data="admin_clear")],
        [InlineKeyboardButton("🌐 تنظیم پروکسی", callback_data="admin_set_proxy"), InlineKeyboardButton("⏸ روشن/خاموش کردن", callback_data="admin_toggle")],
        [InlineKeyboardButton("🔙 بازگشت به منوی اصلی", callback_data="main_menu")]
    ]
    return InlineKeyboardMarkup(keyboard)


async def show_main_menu(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    user = update.effective_user
    user_id = user.id
    context.user_data['admin_state'] = None
    context.user_data['batch_collect_mode'] = None

    if not await is_user_authorized(user_id):
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("📨 ارسال درخواست دسترسی به مدیر", callback_data="request_bot_access")]])
        unauth_text = (
            "⛔️ <b>دسترسی محدود است!</b>\n\n"
            f"کاربر گرامی، شما هنوز مجوز استفاده از ربات را ندارید.\n"
            f"🆔 آیدی عددی شما: <code>{user_id}</code>\n\n"
            "برای استفاده از ربات، روی دکمه زیر کلیک کنید تا درخواست شما برای مدیریت ارسال شود:"
        )
        if update.message:
            await update.message.reply_text(unauth_text, reply_markup=kb, parse_mode='HTML')
        elif update.callback_query:
            try:
                await update.callback_query.edit_message_text(unauth_text, reply_markup=kb, parse_mode='HTML')
            except Exception:
                pass
        return ConversationHandler.END

    admin_status = is_admin(user_id)
    active_tag = context.user_data.get('active_tag_name')
    text = "👋 <b>به سیستم لینک‌ساز و مدیریت اکانت دائمی خوش آمدید.</b>\n\nلطفاً یک گزینه را انتخاب کنید:"

    if update.message:
        await update.message.reply_text(text, reply_markup=get_main_keyboard(admin_status, active_tag), parse_mode='HTML')
    else:
        try:
            await update.callback_query.edit_message_text(text, reply_markup=get_main_keyboard(admin_status, active_tag), parse_mode='HTML')
        except Exception:
            pass
    return ConversationHandler.END


async def admin_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not is_admin(update.effective_user.id):
        return ConversationHandler.END
    context.user_data['admin_state'] = None
    context.user_data['admin_zip_action'] = None
    context.user_data['batch_collect_mode'] = None
    await update.message.reply_text("⚙️ <b>پنل مدیریت سیستم:</b>", reply_markup=get_admin_keyboard(), parse_mode='HTML')
    return ConversationHandler.END


# ==========================================
# توابع مربوط به برچسب‌گذاری و جستجو
# ==========================================
async def ask_tag_name(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_user_authorized(update.effective_user.id):
        await show_main_menu(update, context)
        return ConversationHandler.END
    await update.callback_query.answer()
    context.user_data['admin_state'] = None
    kb = [[InlineKeyboardButton("❌ لغو عملیات", callback_data="cancel_action")]]
    if context.user_data.get('active_tag_name'):
        kb.insert(0, [InlineKeyboardButton("🗑 پاک کردن برچسب فعلی", callback_data="clear_active_tag")])

    text = (
        "🏷 <b>تنظیم برچسب (Batch Tagging)</b>\n\n"
        "لطفاً یک نام برای این دسته ارسال کنید (مثلاً: <code>مشتری 1</code> یا <code>سفارش صبح</code>).\n"
        "تمامی لینک‌هایی که از این پس ساخته شوند تحت این برچسب در بخش «برچسب‌های من» ذخیره خواهند شد."
    )
    await update.callback_query.edit_message_text(text, reply_markup=InlineKeyboardMarkup(kb), parse_mode='HTML')
    return ASK_TAG


async def receive_tag_name(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    tag_name = update.message.text.strip()
    tag_id = uuid.uuid4().hex[:8]
    context.user_data['active_tag_id'] = tag_id
    context.user_data['active_tag_name'] = tag_name

    await update.message.reply_text(
        f"✅ برچسب <b>«{html.escape(tag_name)}»</b> با موفقیت تنظیم شد.\nاکنون می‌توانید شروع به ساختن لینک کنید.",
        parse_mode='HTML',
        reply_markup=get_main_keyboard(is_admin(update.effective_user.id), tag_name)
    )
    return ConversationHandler.END


async def clear_active_tag_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    context.user_data.pop('active_tag_id', None)
    context.user_data.pop('active_tag_name', None)
    await update.callback_query.answer("برچسب پاک شد 🗑")
    await show_main_menu(update, context)
    return ConversationHandler.END


async def ask_search_query(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_user_authorized(update.effective_user.id):
        await show_main_menu(update, context)
        return ConversationHandler.END
    await update.callback_query.answer()
    context.user_data['admin_state'] = None
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("❌ لغو عملیات", callback_data="cancel_action")]])
    text = (
        "🔍 <b>جستجوی سریع لینک‌ها</b>\n\n"
        "لطفاً شماره موبایل کامل یا <b>۴ رقم آخر</b> آن‌ها را ارسال کنید.\n"
        "می‌توانید در هر خط یک شماره بفرستید تا ربات همه را با هم جستجو کند."
    )
    await update.callback_query.edit_message_text(text, reply_markup=kb, parse_mode='HTML')
    return ASK_SEARCH


async def receive_search_query(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    queries = update.message.text.strip().split('\n')
    queries = [clean_digits(q.strip()) for q in queries if q.strip()]

    msg = await update.message.reply_text("⏳ در حال جستجو در دیتابیس...")
    phone_to_latest_link = await build_phone_to_link_map()

    active_keys = await redis_client.keys("phone_active_link:*")
    for ak in active_keys:
        p = clean_digits(ak.replace("phone_active_link:", ""))
        val = await redis_client.get(ak)
        if p and val:
            phone_to_latest_link[p] = val

    report_text = "🔍 <b>نتایج جستجوی شما:</b>\n\n"
    found_count = 0

    for q in queries:
        found_for_q = False
        for phone, link in phone_to_latest_link.items():
            if q == phone or (len(q) >= 4 and phone.endswith(q)):
                report_text += f"✅ <code>{html.escape(phone)}</code>\n🔗 {html.escape(link)}\n\n"
                found_for_q = True
                found_count += 1
        if not found_for_q:
            report_text += f"❌ <code>{html.escape(q)}</code> ➔ یافت نشد\n\n"

    if len(report_text) > 4000:
        clean_rep = re.sub(r'<[^>]+>', '', report_text)
        file_out = io.BytesIO(clean_rep.encode('utf-8'))
        await context.bot.send_document(chat_id=update.effective_user.id, document=file_out, filename=f"Search_Results_{int(time.time())}.txt", caption=f"✅ جستجو پایان یافت. پیدا شده: {found_count}")
        await msg.delete()
    else:
        await msg.edit_text(report_text, parse_mode='HTML', disable_web_page_preview=True)

    await show_main_menu(update, context)
    return ConversationHandler.END


# ==========================================
# مدیریت دکمه‌های اصلی، درخواست دسترسی و پنل ادمین
# ==========================================
async def core_callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    query = update.callback_query
    user = query.from_user
    user_id = user.id
    data = query.data

    # ۱. پردازش درخواست دسترسی کاربر
    if data == "request_bot_access":
        if await is_user_authorized(user_id):
            await query.answer("شما از قبل دسترسی دارید ✅", show_alert=True)
            await show_main_menu(update, context)
            return

        already_req = await redis_client.get(f"pending_access_req:{user_id}")
        if already_req:
            await query.answer("⏳ درخواست شما قبلاً ارسال شده و در انتظار تایید مدیر است.", show_alert=True)
            return

        await redis_client.setex(f"pending_access_req:{user_id}", 3600, "1")
        uname = f"@{html.escape(user.username)}" if user.username else "ندارد"
        full_name = html.escape(user.full_name or "بدون نام")

        admin_kb = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("✅ تایید دسترسی", callback_data=f"auth_approve_{user_id}"),
                InlineKeyboardButton("❌ رد درخواست", callback_data=f"auth_reject_{user_id}")
            ]
        ])
        req_text = (
            f"🔔 <b>درخواست جدید برای استفاده از ربات:</b>\n\n"
            f"👤 نام: <b>{full_name}</b>\n"
            f"🆔 آیدی عددی: <code>{user_id}</code>\n"
            f"🔗 یوزرنیم: {uname}\n\n"
            f"آیا اجازه استفاده از ربات را به این کاربر می‌دهید؟"
        )
        for aid in ADMIN_IDS:
            try:
                await context.bot.send_message(chat_id=aid, text=req_text, reply_markup=admin_kb, parse_mode='HTML')
            except Exception as e:
                logging.error(f"Could not send access request to admin {aid}: {e}")

        await query.answer("درخواست شما برای مدیریت ارسال شد ✅", show_alert=True)
        await query.edit_message_text(
            "✅ <b>درخواست دسترسی شما با موفقیت برای مدیر ارسال شد.</b>\n"
            "لطفاً منتظر بمانید؛ به محض تایید مدیر، پیام فعال‌سازی برای شما ارسال خواهد شد.",
            parse_mode='HTML'
        )
        return

    # ۲. تایید یا رد دسترسی توسط ادمین
    if data.startswith("auth_approve_") or data.startswith("auth_reject_"):
        if not is_admin(user_id):
            await query.answer("⛔️ فقط ادمین مجاز است.", show_alert=True)
            return
        target_uid = int(data.split("_")[2])
        await redis_client.delete(f"pending_access_req:{target_uid}")
        safe_orig_text = html.escape(query.message.text or "")

        if data.startswith("auth_approve_"):
            await redis_client.sadd("authorized_users", str(target_uid))
            await query.answer("دسترسی کاربر تایید شد ✅")
            await query.edit_message_text(safe_orig_text + "\n\n✅ <b>توسط ادمین تایید شد.</b>", parse_mode='HTML')
            try:
                await context.bot.send_message(
                    chat_id=target_uid,
                    text="🎉 <b>دسترسی شما توسط مدیریت تایید شد!</b>\nهم‌اکنون می‌توانید از امکانات ربات استفاده کنید:",
                    reply_markup=get_main_keyboard(is_admin(target_uid)),
                    parse_mode='HTML'
                )
            except Exception:
                pass
        else:
            await redis_client.srem("authorized_users", str(target_uid))
            await query.answer("درخواست کاربر رد شد ❌")
            await query.edit_message_text(safe_orig_text + "\n\n❌ <b>توسط ادمین رد شد.</b>", parse_mode='HTML')
            try:
                await context.bot.send_message(chat_id=target_uid, text="⛔️ متاسفانه درخواست دسترسی شما به ربات توسط مدیریت رد شد.")
            except Exception:
                pass
        return

    # بررسی مجوز برای سایر دکمه‌ها
    if not await is_user_authorized(user_id):
        await query.answer("⛔️ شما مجوز استفاده از ربات را ندارید.", show_alert=True)
        await show_main_menu(update, context)
        return

    if data == "main_menu":
        await query.answer()
        context.user_data['admin_state'] = None
        context.user_data['batch_collect_mode'] = None
        await show_main_menu(update, context)
        return

    if data == "finish_link_creation":
        await query.answer("در حال آماده‌سازی لینک‌های شما... ⏳")
        session_links = context.user_data.get('session_links', [])
        active_tag_name = context.user_data.get('active_tag_name')
        active_tag_id = context.user_data.get('active_tag_id')

        if not session_links:
            await query.edit_message_text("⚠️ هیچ لینکی در این نوبت ساخته نشده است.", reply_markup=get_main_keyboard(is_admin(user_id), active_tag_name))
            return

        report_text = f"🎉 <b>لینک‌های دائمی تولید شده شما (تعداد: {len(session_links)}):</b>\n"

        if active_tag_name and active_tag_id:
            report_text += f"🏷 <b>ذخیره شده در برچسب:</b> {html.escape(active_tag_name)}\n\n"
            tag_meta_key = f"user_tag_meta:{user_id}:{active_tag_id}"
            await redis_client.set(tag_meta_key, active_tag_name)
            await redis_client.sadd(f"user_tags_set:{user_id}", active_tag_id)

            tag_links_key = f"user_tag_links:{active_tag_id}"
            for item in session_links:
                await redis_client.rpush(tag_links_key, json.dumps(item, ensure_ascii=False))
        else:
            report_text += "\n"

        for idx, item in enumerate(session_links, 1):
            report_text += f"{idx}. 📱 <b>شماره:</b> <code>{item['phone']}</code>\n🔗 {item['link']}\n\n"

        context.user_data['session_links'] = []

        if len(report_text) > 4000:
            clean_rep = re.sub(r'<[^>]+>', '', report_text)
            file_out = io.BytesIO(clean_rep.encode('utf-8'))
            await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"My_Links_{int(time.time())}.txt", caption="✅ لینک‌های دائمی ساخته شده شما")
            await query.message.delete()
            await context.bot.send_message(chat_id=user_id, text="بازگشت به منوی اصلی:", reply_markup=get_main_keyboard(is_admin(user_id), active_tag_name))
        else:
            await query.edit_message_text(report_text, disable_web_page_preview=True, parse_mode='HTML')
            await context.bot.send_message(chat_id=user_id, text="بازگشت به منوی اصلی:", reply_markup=get_main_keyboard(is_admin(user_id), active_tag_name))
        return

    if data == "my_tags":
        await query.answer()
        tag_ids = await redis_client.smembers(f"user_tags_set:{user_id}")
        active_tag_name = context.user_data.get('active_tag_name')

        if not tag_ids:
            await query.edit_message_text("⚠️ شما هنوز هیچ برچسبی ایجاد نکرده‌اید.", reply_markup=get_main_keyboard(is_admin(user_id), active_tag_name))
            return

        kb = []
        for tid in list(tag_ids)[:40]:
            t_name = await redis_client.get(f"user_tag_meta:{user_id}:{tid}")
            if t_name:
                kb.append([InlineKeyboardButton(f"🏷 {t_name}", callback_data=f"show_tag_{tid}")])

        kb.append([InlineKeyboardButton("🔙 بازگشت به منوی اصلی", callback_data="main_menu")])
        await query.edit_message_text("📂 <b>برچسب‌های ذخیره‌شده شما:</b>\nبرای مشاهده و دریافت لینک‌ها روی برچسب مورد نظر کلیک کنید:", reply_markup=InlineKeyboardMarkup(kb), parse_mode='HTML')
        return

    if data.startswith("show_tag_"):
        await query.answer()
        tid = data.split("show_tag_")[1]
        t_name = await redis_client.get(f"user_tag_meta:{user_id}:{tid}") or "نامشخص"
        raw_links = await redis_client.lrange(f"user_tag_links:{tid}", 0, -1)

        if not raw_links:
            await query.edit_message_text("⚠️ این برچسب خالی است.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت", callback_data="my_tags")]]))
            return

        report_text = f"📂 <b>لینک‌های برچسب «{html.escape(t_name)}» (تعداد: {len(raw_links)}):</b>\n\n"
        for idx, l in enumerate(raw_links, 1):
            try:
                ld = json.loads(l)
                report_text += f"{idx}. 📱 <code>{ld['phone']}</code>\n🔗 {ld['link']}\n\n"
            except Exception:
                pass

        if len(report_text) > 4000:
            clean_rep = re.sub(r'<[^>]+>', '', report_text)
            file_out = io.BytesIO(clean_rep.encode('utf-8'))
            await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Tag_{t_name}.txt", caption=f"📂 تمامی لینک‌های مربوط به برچسب: {t_name}")
            await context.bot.send_message(chat_id=user_id, text="بازگشت به لیست برچسب‌ها:", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت", callback_data="my_tags")]]))
        else:
            await query.edit_message_text(report_text, disable_web_page_preview=True, parse_mode='HTML', reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت", callback_data="my_tags")]]))
        return

    # === دکمه‌های کنترل صف دسته‌ای (Batch Collector) برای کاربران مجاز و ادمین ===
    if data in ["batch_confirm_start", "admin_start_zip_batch"]:
        await query.answer("🚀 عملیات آغاز شد!")
        await trigger_batch_processing(update, context)
        return

    if data in ["batch_clear_queue", "admin_clear_zip_batch"]:
        await query.answer("لیست فایل‌ها پاک شد 🗑")
        context.user_data['batch_items_queue'] = []
        mode = context.user_data.get('batch_collect_mode', 'zip_to_link')
        await query.edit_message_text(
            text=get_batch_collector_status_text(mode, context.user_data),
            reply_markup=get_batch_collector_keyboard(mode, 0, 0, 0),
            parse_mode='HTML'
        )
        return

    if data in ["batch_cancel_collect", "admin_cancel_zip_batch"]:
        await query.answer("عملیات لغو شد ❌")
        context.user_data['batch_collect_mode'] = None
        context.user_data['admin_state'] = None
        context.user_data['admin_zip_action'] = None
        context.user_data['batch_items_queue'] = []
        context.user_data.pop('batch_status_msg_id', None)
        if is_admin(user_id):
            await query.edit_message_text("⚙️ <b>پنل مدیریت سیستم:</b>", reply_markup=get_admin_keyboard(), parse_mode='HTML')
        else:
            await show_main_menu(update, context)
        return

    # === دکمه‌های مشترک کاربر مجاز و ادمین (ساخت آدرس لینک/زیپ، سابقه خرید لینک/زیپ، تبدیل زیپ به لینک، تخفیف زیپ) ===
    if data == "admin_zip_to_link":
        await query.answer()
        context.user_data['batch_collect_mode'] = 'zip_to_link'
        context.user_data['admin_state'] = None
        context.user_data['batch_items_queue'] = []
        status_msg = await query.edit_message_text(
            text=get_batch_collector_status_text('zip_to_link', context.user_data),
            reply_markup=get_batch_collector_keyboard('zip_to_link', 0, 0, 0),
            parse_mode='HTML'
        )
        context.user_data['batch_status_msg_id'] = status_msg.message_id
        return

    if data == "admin_delete_zip_from_db":
        if not is_admin(user_id):
            await query.answer("⛔️ فقط ادمین مجاز به حذف از دیتابیس است.", show_alert=True)
            return
        await query.answer()
        context.user_data['batch_collect_mode'] = 'delete_zip_from_db'
        context.user_data['admin_state'] = None
        context.user_data['batch_items_queue'] = []
        status_msg = await query.edit_message_text(
            text=get_batch_collector_status_text('delete_zip_from_db', context.user_data),
            reply_markup=get_batch_collector_keyboard('delete_zip_from_db', 0, 0, 0),
            parse_mode='HTML'
        )
        context.user_data['batch_status_msg_id'] = status_msg.message_id
        return

    if data == "admin_zip_discount":
        await query.answer()
        context.user_data['batch_collect_mode'] = 'user_discount_check'
        context.user_data['admin_state'] = None
        context.user_data['batch_items_queue'] = []
        status_msg = await query.edit_message_text(
            text=get_batch_collector_status_text('user_discount_check', context.user_data),
            reply_markup=get_batch_collector_keyboard('user_discount_check', 0, 0, 0),
            parse_mode='HTML'
        )
        context.user_data['batch_status_msg_id'] = status_msg.message_id
        return

    if data == "admin_orders_user":
        await query.answer()
        context.user_data['batch_collect_mode'] = 'user_check_orders'
        context.user_data['admin_state'] = None
        context.user_data['batch_items_queue'] = []
        status_msg = await query.edit_message_text(
            text=get_batch_collector_status_text('user_check_orders', context.user_data),
            reply_markup=get_batch_collector_keyboard('user_check_orders', 0, 0, 0),
            parse_mode='HTML'
        )
        context.user_data['batch_status_msg_id'] = status_msg.message_id
        return

    if data == "admin_addr_user":
        await query.answer()
        context.user_data['admin_state'] = 'waiting_addr_config_for_user'
        context.user_data['batch_collect_mode'] = None
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("📍 استفاده از آدرس پیش‌فرض تهران (فوری)", callback_data="addr_preset_user_default")],
            [InlineKeyboardButton("❌ انصراف و بازگشت", callback_data="admin_panel" if is_admin(user_id) else "main_menu")]
        ])
        await query.edit_message_text(
            "📍 <b>ساخت آدرس برای اکانت‌های ارسالی (لینک یا فایل ZIP)</b>\n"
            "<i>(بر اساس ساختار ثبت آدرس Main 9)</i>\n\n"
            "لطفاً مشخص کنید چه آدرسی روی اکانت‌ها ثبت شود:\n"
            "1️⃣ روی دکمه <b>«📍 استفاده از آدرس پیش‌فرض تهران»</b> بزنید.\n"
            "2️⃣ یا <b>لینک یک اکانت الگو</b> را بفرستید تا آدرس همان اکانت کپی شود.\n"
            "3️⃣ یا مختصات و آدرس دلخواه را به فرمت زیر ارسال کنید:\n"
            "<code>35.69975, 51.33551, تهران خیابان آزادی پلاک ۱۰</code>",
            reply_markup=kb,
            parse_mode='HTML'
        )
        return

    if data == "addr_preset_user_default":
        await query.answer("آدرس پیش‌فرض تهران انتخاب شد ✅")
        context.user_data['admin_state'] = None
        context.user_data['batch_address_config'] = DEFAULT_TEHRAN_ADDRESS.copy()
        context.user_data['batch_address_desc'] = "آدرس پیش‌فرض تهران (خیابان آزادی)"
        context.user_data['batch_collect_mode'] = 'user_create_address'
        context.user_data['batch_items_queue'] = []
        status_msg = await query.edit_message_text(
            text=get_batch_collector_status_text('user_create_address', context.user_data),
            reply_markup=get_batch_collector_keyboard('user_create_address', 0, 0, 0),
            parse_mode='HTML'
        )
        context.user_data['batch_status_msg_id'] = status_msg.message_id
        return

    # === بخش مربوط به مدیریت ادمین ===
    if not is_admin(user_id):
        return
    await query.answer()

    if data == "admin_panel":
        context.user_data['admin_state'] = None
        context.user_data['admin_zip_action'] = None
        context.user_data['batch_collect_mode'] = None
        await query.edit_message_text("⚙️ <b>پنل مدیریت سیستم:</b>", reply_markup=get_admin_keyboard(), parse_mode='HTML')

    elif data == "admin_addr_db":
        context.user_data['admin_state'] = 'waiting_addr_config_for_db'
        context.user_data['batch_collect_mode'] = None
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("📍 ثبت آدرس پیش‌فرض تهران روی کل دیتابیس", callback_data="addr_preset_db_default")],
            [InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]
        ])
        await query.edit_message_text(
            "📍 <b>ساخت آدرس برای تمامی اکانت‌های دیتابیس</b>\n"
            "<i>(بر اساس ساختار ثبت آدرس Main 9)</i>\n\n"
            "لطفاً مشخص کنید چه آدرسی روی اکانت‌های دیتابیس ثبت شود:\n"
            "1️⃣ روی دکمه <b>«📍 ثبت آدرس پیش‌فرض تهران روی کل دیتابیس»</b> کلیک کنید.\n"
            "2️⃣ یا <b>لینک یک اکانت الگو</b> را ارسال کنید تا آدرس آن استخراج و روی کل دیتابیس ثبت شود.\n"
            "3️⃣ یا مختصات دلخواه را به فرمت زیر ارسال کنید:\n"
            "<code>35.69975, 51.33551, تهران خیابان آزادی پلاک ۱۰</code>",
            reply_markup=kb,
            parse_mode='HTML'
        )

    elif data == "addr_preset_db_default":
        context.user_data['admin_state'] = None
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        asyncio.create_task(
            process_create_address_for_db(
                context.bot, user_id, acc_keys, DEFAULT_TEHRAN_ADDRESS.copy(), "آدرس پیش‌فرض تهران (خیابان آزادی)"
            )
        )

    elif data == "admin_orders_db":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        asyncio.create_task(process_db_orders_history_and_send_report(context.bot, user_id, acc_keys))

    elif data == "admin_del_addr_db":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        asyncio.create_task(process_delete_addresses_for_db(context.bot, user_id, acc_keys))

    elif data == "admin_del_addr_user":
        context.user_data['batch_collect_mode'] = 'user_delete_addresses'
        context.user_data['admin_state'] = None
        context.user_data['batch_items_queue'] = []
        status_msg = await query.edit_message_text(
            text=get_batch_collector_status_text('user_delete_addresses', context.user_data),
            reply_markup=get_batch_collector_keyboard('user_delete_addresses', 0, 0, 0),
            parse_mode='HTML'
        )
        context.user_data['batch_status_msg_id'] = status_msg.message_id

    elif data == "admin_auto_refresh_menu":
        interval_str = await redis_client.get("settings:auto_refresh_interval")
        interval = int(interval_str) if (interval_str and interval_str.isdigit()) else 43200
        last_run = await redis_client.get("settings:last_auto_refresh") or "هنوز اجرا نشده"

        if interval <= 0:
            status_str = "غیرفعال 🔴"
        else:
            status_str = f"فعال 🟢 (هر {interval // 3600} ساعت یک‌بار)"

        kb = InlineKeyboardMarkup([
            [
                InlineKeyboardButton("هر ۶ ساعت ⏱", callback_data="admin_set_autoref_21600"),
                InlineKeyboardButton("هر ۱۲ ساعت 🕧", callback_data="admin_set_autoref_43200")
            ],
            [
                InlineKeyboardButton("هر ۲۴ ساعت 📅", callback_data="admin_set_autoref_86400"),
                InlineKeyboardButton("غیرفعال کردن 🔴", callback_data="admin_set_autoref_0")
            ],
            [InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]
        ])
        text = (
            "⏱ <b>تنظیم چرخش خودکار رفرش‌توکن‌ها (Auto-Rotation):</b>\n\n"
            f"📡 <b>وضعیت فعلی:</b> {status_str}\n"
            f"🕒 <b>آخرین اجرای موفق:</b> <code>{last_run}</code>\n\n"
            "💡 با فعال بودن این گزینه، ربات به صورت خودکار در پس‌زمینه تمام اکانت‌ها را نوسازی کرده و آخرین <code>Access</code> و <code>Refresh</code> را ذخیره می‌کند تا هرگز منقضی نشوند."
        )
        await query.edit_message_text(text, reply_markup=kb, parse_mode='HTML')

    elif data.startswith("admin_set_autoref_"):
        new_int = int(data.split("admin_set_autoref_")[1])
        await redis_client.set("settings:auto_refresh_interval", str(new_int))
        if new_int > 0:
            await redis_client.set("settings:last_auto_refresh_ts", str(int(time.time())))
            msg_txt = f"✅ چرخش خودکار توکن‌ها روی <b>هر {new_int // 3600} ساعت یک‌بار</b> تنظیم شد."
        else:
            msg_txt = "🔴 چرخش خودکار توکن‌ها غیرفعال شد."
        await query.edit_message_text(msg_txt, reply_markup=get_admin_keyboard(), parse_mode='HTML')

    elif data == "admin_set_proxy":
        context.user_data['admin_state'] = 'waiting_for_proxy'
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]])
        await query.edit_message_text(
            "🌐 <b>تنظیم هوشمند پروکسی‌ها:</b>\n\n"
            "لطفاً لیست پروکسی‌ها را (به صورت متن، لینک سابسکریپشن یا فایل <code>.txt</code>) ارسال کنید.\n\n"
            "✅ پشتیبانی خودکار از تمام فرمت‌ها:\n"
            "• <code>user:pass@host:port</code> یا <code>host:port@user:pass</code>\n"
            "• <code>host:port:user:pass</code> یا <code>ip:port</code>",
            reply_markup=kb,
            parse_mode='HTML'
        )

    elif data == "admin_split_discount_file":
        context.user_data['admin_state'] = 'waiting_for_discount_split'
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]])
        await query.edit_message_text(
            "📂 <b>تفکیک و دسته‌بندی فایل تخفیف بر اساس تمامی مبالغ:</b>\n\n"
            "لطفاً فایل متنی گزارش تخفیف‌ها (<code>Discounts_Report_...txt</code>) یا متن پیام گزارش را ارسال کنید.\n\n"
            "🔹 اگر اکانتی ۲ کد تخفیف همزمان داشته باشد، در دسته هر دو مبلغ قرار می‌گیرد تا هیچ کدی از دست نرود.",
            reply_markup=kb,
            parse_mode='HTML'
        )

    elif data == "admin_stats":
        acc_keys = await redis_client.keys("account:*")
        link_keys = await redis_client.keys("acc_link:*")
        auth_users = await redis_client.scard("authorized_users")
        proxies = await get_all_proxies_from_db()
        proxy_count = len(proxies)

        interval_str = await redis_client.get("settings:auto_refresh_interval")
        interval = int(interval_str) if (interval_str and interval_str.isdigit()) else 43200
        auto_ref_str = f"هر {interval // 3600} ساعت 🟢" if interval > 0 else "غیرفعال 🔴"
        last_run = await redis_client.get("settings:last_auto_refresh") or "ثبت نشده"

        maint = await redis_client.get("settings:maintenance")
        status = "غیرفعال 🔴" if maint == "1" else "فعال 🟢"

        text = (
            "📊 <b>وضعیت سیستم:</b>\n\n"
            f"👤 <b>تعداد کل اکانت‌ها:</b> <code>{len(acc_keys)}</code>\n"
            f"🔗 <b>لینک‌های دائمی فعال:</b> <code>{len(link_keys)}</code>\n"
            f"✅ <b>کاربران تاییدشده:</b> <code>{auth_users}</code>\n"
            f"🌐 <b>تعداد پروکسی‌ها:</b> <code>{proxy_count}</code>\n"
            f"⏱ <b>چرخش خودکار توکن‌ها:</b> {auto_ref_str}\n"
            f"🕒 <b>آخرین نوسازی:</b> <code>{last_run}</code>\n"
            f"♾ <b>وضعیت انقضای لینک‌ها:</b> دائمی (بدون انقضا)\n"
            f"🤖 <b>وضعیت ربات:</b> {status}"
        )
        await query.edit_message_text(text, reply_markup=get_admin_keyboard(), parse_mode='HTML')

    elif data == "admin_redis_memory":
        try:
            mem_info = await redis_client.info("memory")
            db_size = await redis_client.dbsize()

            used_memory = int(mem_info.get("used_memory", 0))
            used_memory_rss = int(mem_info.get("used_memory_rss", 0))
            used_memory_peak = int(mem_info.get("used_memory_peak", 0))
            maxmemory = int(mem_info.get("maxmemory", 0))
            total_system_mem = int(mem_info.get("total_system_memory", 0))

            env_limit_mb = int(os.environ.get("REDIS_MAX_MEMORY_MB", "512"))
            effective_limit = maxmemory if maxmemory > 0 else (env_limit_mb * 1024 * 1024)
            limit_source = "تنظیمات Redis (maxmemory)" if maxmemory > 0 else f"پلن Railway ({env_limit_mb} MB)"

            remaining_bytes = max(effective_limit - used_memory, 0)
            usage_pct = min((used_memory / effective_limit) * 100, 100.0) if effective_limit > 0 else 0.0

            bar_len = 14
            filled = int(bar_len * usage_pct / 100)
            bar = "█" * filled + "░" * (bar_len - filled)

            mem_text = (
                "💾 <b>وضعیت حافظه دیتابیس Redis (Railway):</b>\n\n"
                f"📊 <b>درصد مصرف:</b> <code>[{bar}] {usage_pct:.1f}%</code>\n\n"
                f"🟢 <b>حافظه باقی‌مانده (آزاد):</b> <b><code>{format_bytes(remaining_bytes)}</code></b>\n"
                f"🔴 <b>حافظه مصرف‌شده فعلی:</b> <code>{format_bytes(used_memory)}</code>\n"
                f"📦 <b>کل ظرفیت مبنا:</b> <code>{format_bytes(effective_limit)}</code> ({limit_source})\n"
                f"────────────────────\n"
                f"📈 <b>بیشترین مصرف ثبت‌شده (Peak):</b> <code>{format_bytes(used_memory_peak)}</code>\n"
                f"🖥 <b>مصرف واقعی رم (RSS):</b> <code>{format_bytes(used_memory_rss)}</code>\n"
                f"🔑 <b>تعداد کل کلیدهای دیتابیس:</b> <code>{db_size:,}</code> کلید\n"
            )
            if total_system_mem > 0:
                mem_text += f"🌐 <b>کل رم سرور میزبان:</b> <code>{format_bytes(total_system_mem)}</code>\n"

            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 بروزرسانی وضعیت حافظه", callback_data="admin_redis_memory")],
                [InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]
            ])
            await query.edit_message_text(mem_text, reply_markup=kb, parse_mode='HTML')
        except Exception as e:
            logging.error(f"Error fetching redis memory info: {e}")
            await context.bot.send_message(chat_id=user_id, text=f"❌ خطا در دریافت اطلاعات حافظه Redis:\n<code>{html.escape(str(e))}</code>", parse_mode='HTML')

    elif data == "admin_users_report":
        raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
        if not raw_logs:
            await context.bot.send_message(chat_id=user_id, text="⚠️ هیچ گزارشی از ساخت لینک توسط کاربران ثبت نشده است.")
            return

        users_data = {}
        for item in raw_logs:
            try:
                entry = json.loads(item)
                uid = entry.get("tg_id")
                if uid not in users_data:
                    users_data[uid] = {
                        "name": entry.get("tg_name", "نامشخص"),
                        "username": entry.get("tg_user", ""),
                        "links": []
                    }
                users_data[uid]["links"].append(entry)
            except Exception:
                pass

        report_text = "📊 گزارش جامع ساخت لینک کاربران:\n\n"
        for uid, udata in users_data.items():
            uname_str = f" (@{udata['username']})" if udata['username'] else ""
            report_text += f"👤 کاربر: {udata['name']}{uname_str}\n🆔 آیدی: {uid}\n🔢 تعداد کل لینک‌ها: {len(udata['links'])}\n------------------------------------\n"

        file_out = io.BytesIO(report_text.encode('utf-8'))
        await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Users_Summary_{int(time.time())}.txt", caption="📊 گزارش خلاصه کارکرد کاربران")

    elif data == "admin_refresh_and_revive":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        asyncio.create_task(process_refresh_and_revive_all(context.bot, user_id, acc_keys, is_auto_cycle=False))

    elif data == "admin_confirm_delete_dead":
        dead_phones = await redis_client.smembers("temp:unrecoverable_accounts")
        if not dead_phones:
            await query.edit_message_text("⚠️ لیست اکانت‌های غیرقابل بازگشت خالی است یا قبلاً حذف شده‌اند.", reply_markup=get_admin_keyboard())
            return

        deleted_count = 0
        for phone in dead_phones:
            existed = await redis_client.delete(f"account:{phone}")
            active_url = await redis_client.get(f"phone_active_link:{phone}")
            if active_url and "/acc/" in active_url:
                lid = active_url.split("/acc/")[-1].strip()
                await redis_client.delete(f"acc_link:{lid}")
            await redis_client.delete(f"phone_active_link:{phone}")
            if existed:
                deleted_count += 1

        await redis_client.delete("temp:unrecoverable_accounts")
        await query.edit_message_text(
            f"🗑 <b>پاکسازی اکانت‌های سوخته انجام شد.</b>\n"
            f"تعداد <b>{deleted_count}</b> اکانت غیرقابل بازگشت با موفقیت از دیتابیس حذف شدند.",
            reply_markup=get_admin_keyboard(),
            parse_mode='HTML'
        )

    elif data == "admin_cancel_delete_dead":
        await redis_client.delete("temp:unrecoverable_accounts")
        await query.edit_message_text(
            "✅ عملیات حذف لغو شد و تمامی اکانت‌ها در دیتابیس باقی ماندند.",
            reply_markup=get_admin_keyboard()
        )

    elif data == "admin_check_discounts":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        asyncio.create_task(process_discounts_and_send_report(context.bot, user_id, acc_keys))

    elif data == "admin_extract_raw":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        asyncio.create_task(process_raw_accounts_and_send_report(context.bot, user_id, acc_keys))

    elif data == "admin_export":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        export_text = "لیست شماره‌های ثبت شده در سیستم:\n\n"
        for key in acc_keys:
            export_text += f"{clean_digits(key.replace('account:', ''))}\n"

        file_out = io.BytesIO(export_text.encode('utf-8'))
        await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Accounts_{int(time.time())}.txt", caption="📥 فایل دیتابیس (شماره‌ها) دریافت شد.")

    elif data == "admin_export_links":
        link_keys = await redis_client.keys("acc_link:*")
        if not link_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ هیچ لینکی در دیتابیس موجود نیست.")
            return

        await context.bot.send_message(chat_id=user_id, text="⏳ در حال استخراج لینک‌ها و شماره‌ها. لطفاً منتظر بمانید...")

        export_text = "لیست لینک‌های دائمی فعال به همراه شماره:\n\n"
        count = 0
        for l_key in link_keys:
            link_id = l_key.replace("acc_link:", "")
            final_url = f"{WEB_DOMAIN}/acc/{link_id}"
            link_data = await redis_client.get(l_key)
            phone = "نامشخص"
            try:
                data_json = json.loads(link_data)
                _, _, extr_p = extract_tokens_from_json_data(data_json)
                if extr_p:
                    phone = extr_p
            except Exception:
                pass
            export_text += f"📱 شماره: {phone}\n🔗 لینک: {final_url}\n\n"
            count += 1

        file_out = io.BytesIO(export_text.encode('utf-8'))
        await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Links_With_Phone_{int(time.time())}.txt", caption=f"✅ استخراج {count} لینک دائمی با موفقیت انجام شد.")

    elif data == "admin_export_tokens":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        await context.bot.send_message(chat_id=user_id, text="⏳ در حال استخراج آخرین توکن‌ها...")
        exported_data = {}
        for key in acc_keys:
            phone = clean_digits(key.replace('account:', ''))
            tokens = await redis_client.hgetall(key)
            exported_data[phone] = {
                "access_token": tokens.get("access_token", ""),
                "refresh_token": tokens.get("refresh_token", "")
            }
        json_data = json.dumps(exported_data, indent=4, ensure_ascii=False)
        file_out = io.BytesIO(json_data.encode('utf-8'))
        await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Tokens_DB_{int(time.time())}.json", caption=f"🔑 فایل آخرین توکن‌های استخراج شده ({len(exported_data)} شماره)")

    elif data == "admin_clear":
        kb = [[InlineKeyboardButton("✅ تایید عملیات حذف کل دیتابیس", callback_data="admin_clear_confirm"), InlineKeyboardButton("❌ انصراف", callback_data="admin_panel")]]
        await query.edit_message_text("⚠️ <b>اخطار:</b> این عملیات تمامی اکانت‌ها و لینک‌های ثبت شده را حذف خواهد کرد.\nآیا تایید می‌کنید؟", reply_markup=InlineKeyboardMarkup(kb), parse_mode='HTML')

    elif data == "admin_clear_confirm":
        for pattern in ["account:*", "acc_link:*", "phone_active_link:*"]:
            keys = await redis_client.keys(pattern)
            if keys:
                await redis_client.delete(*keys)
        await query.edit_message_text("🗑 عملیات پاکسازی کامل اکانت‌ها و لینک‌ها با موفقیت انجام شد.", reply_markup=get_admin_keyboard())

    elif data == "admin_toggle":
        current = await redis_client.get("settings:maintenance")
        new_val = "0" if current == "1" else "1"
        await redis_client.set("settings:maintenance", new_val)
        status = "غیرفعال (تعمیرات) 🔴" if new_val == "1" else "فعال 🟢"
        await query.edit_message_text(f"⚙️ <b>تغییر وضعیت سیستم:</b>\nوضعیت کنونی: {status}", reply_markup=get_admin_keyboard(), parse_mode='HTML')


# ==========================================
# سیستم هندل کردن ورودی متنی / فایلی (آدرس، صف زیپ/لینک، پروکسی و تفکیک تخفیف)
# ==========================================
async def handle_admin_text_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not await is_user_authorized(user_id):
        return

    # ۱. اگر کاربر در حالت جمع‌آوری دسته‌ای (Batch Collector) است
    if context.user_data.get('batch_collect_mode'):
        await enqueue_batch_input_message(update, context)
        return

    state = context.user_data.get('admin_state')
    if not state:
        return

    # ۲. دریافت آدرس برای ساخت آدرس روی لینک/زیپ ارسالی کاربر
    if state == 'waiting_addr_config_for_user':
        raw_input = update.message.text if update.message.text else ""
        if not raw_input:
            await update.message.reply_text("⚠️ لطفاً لینک اکانت الگو، مختصات یا کلمه «پیشفرض» را به صورت متن ارسال کنید.")
            return
        wait_m = await update.message.reply_text("⏳ در حال بررسی و استخراج اطلاعات آدرس...")
        proxies_list = await get_all_proxies_from_db()
        addr_cfg, addr_desc, err_msg = await resolve_address_config_from_input(raw_input, proxies_list)
        if err_msg or not addr_cfg:
            await wait_m.edit_text(err_msg or "❌ خطا در استخراج آدرس.")
            return

        context.user_data['admin_state'] = None
        context.user_data['batch_address_config'] = addr_cfg
        context.user_data['batch_address_desc'] = addr_desc
        context.user_data['batch_collect_mode'] = 'user_create_address'
        context.user_data['batch_items_queue'] = []

        status_msg = await wait_m.edit_text(
            text=get_batch_collector_status_text('user_create_address', context.user_data),
            reply_markup=get_batch_collector_keyboard('user_create_address', 0, 0, 0),
            parse_mode='HTML'
        )
        context.user_data['batch_status_msg_id'] = status_msg.message_id
        return

    # ۳. دریافت آدرس برای ساخت آدرس روی کل اکانت‌های دیتابیس
    if state == 'waiting_addr_config_for_db':
        if not is_admin(user_id):
            return
        raw_input = update.message.text if update.message.text else ""
        if not raw_input:
            await update.message.reply_text("⚠️ لطفاً لینک اکانت الگو، مختصات یا کلمه «پیشفرض» را به صورت متن ارسال کنید.")
            return
        wait_m = await update.message.reply_text("⏳ در حال بررسی و استخراج اطلاعات آدرس...")
        proxies_list = await get_all_proxies_from_db()
        addr_cfg, addr_desc, err_msg = await resolve_address_config_from_input(raw_input, proxies_list)
        if err_msg or not addr_cfg:
            await wait_m.edit_text(err_msg or "❌ خطا در استخراج آدرس.")
            return

        context.user_data['admin_state'] = None
        await wait_m.delete()
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await update.message.reply_text("⚠️ دیتابیس سیستم خالی است.")
            return
        asyncio.create_task(process_create_address_for_db(context.bot, user_id, acc_keys, addr_cfg, addr_desc))
        return

    if not is_admin(user_id):
        return

    # ۴. دریافت و ذخیره هوشمند پروکسی‌ها (با نرمال‌ساز Main 9)
    if state == 'waiting_for_proxy':
        msg = await update.message.reply_text("⏳ در حال خواندن و استانداردسازی پروکسی‌ها...")
        try:
            if update.message.document:
                file_name = update.message.document.file_name.lower()
                if not file_name.endswith('.txt'):
                    await msg.edit_text("❌ فرمت فایل پروکسی باید `.txt` باشد.")
                    return
                file = await update.message.document.get_file()
                file_bytes = await file.download_as_bytearray()
                text_content = file_bytes.decode('utf-8', errors='ignore')
            else:
                text_content = update.message.text or ""

            proxies = await asyncio.to_thread(load_proxies_from_input, text_content)

            if proxies:
                await redis_client.set("settings:proxies", json.dumps(proxies))
                context.user_data['admin_state'] = None
                sample = html.escape(proxies[0])
                await msg.edit_text(
                    f"✅ تعداد <b>{len(proxies)}</b> پروکسی معتبر با موفقیت استانداردسازی و ذخیره شد.\n"
                    f"🔹 نمونه: <code>{sample}</code>",
                    reply_markup=get_admin_keyboard(),
                    parse_mode='HTML'
                )
            else:
                await msg.edit_text("⚠️ هیچ پروکسی معتبری در ورودی یافت نشد. لطفاً مجدداً امتحان کنید.")
        except Exception as e:
            logging.error(f"Error reading proxies: {e}")
            await msg.edit_text("❌ خطا در پردازش فایل یا متن پروکسی.")

    # ۵. تفکیک فایل گزارش تخفیف بر اساس تمامی مبالغ (پشتیبانی از اکانت‌های چندکدی)
    elif state == 'waiting_for_discount_split':
        msg = await update.message.reply_text("⏳ در حال پردازش و تفکیک لینک‌ها بر اساس تمامی کدهای تخفیف...")
        try:
            if update.message.document:
                file_name = update.message.document.file_name.lower()
                if not file_name.endswith('.txt'):
                    await msg.edit_text("❌ لطفاً یک فایل متنی با پسوند `.txt` ارسال کنید.")
                    return
                file = await update.message.document.get_file()
                file_bytes = await file.download_as_bytearray()
                text_content = file_bytes.decode('utf-8', errors='ignore')
            else:
                text_content = update.message.text or ""

            grouped, total_links = parse_and_split_discounts(text_content)

            if not grouped or total_links == 0:
                await msg.edit_text(
                    "⚠️ هیچ لینک یا مبلغ تخفیفی در متن/فایل ارسالی پیدا نشد.\n"
                    "مطمئن شوید که فایل گزارش تخفیف (<code>Discounts_Report_...txt</code>) را ارسال کرده‌اید.",
                    reply_markup=get_admin_keyboard(),
                    parse_mode='HTML'
                )
                context.user_data['admin_state'] = None
                return

            output_lines = [f"📂 لیست تفکیک‌شده لینک‌های تخفیف (مجموع رکوردها: {total_links})\n" + "=" * 50 + "\n"]
            summary_lines = []

            for amount in sorted(grouped.keys(), reverse=True):
                links = grouped[amount]
                output_lines.append(f"🎁 دسته تخفیف {amount} هزار تومانی (تعداد: {len(links)}):")
                output_lines.append("-" * 40)
                for l in links:
                    output_lines.append(l)
                output_lines.append("\n" + "=" * 50 + "\n")
                summary_lines.append(f"▫️ <b>دسته {amount} هزار تومانی:</b> <code>{len(links)}</code> لینک")

            final_text = "\n".join(output_lines)
            file_out = io.BytesIO(final_text.encode('utf-8'))
            ts = int(time.time())

            caption_text = (
                f"✅ <b>تفکیک فایل تخفیف با موفقیت انجام شد.</b>\n\n"
                f"🔢 <b>مجموع لینک‌ها در دسته‌ها:</b> <code>{total_links}</code>\n"
                + "\n".join(summary_lines)
            )

            context.user_data['admin_state'] = None
            await msg.delete()
            await context.bot.send_document(
                chat_id=user_id,
                document=file_out,
                filename=f"Categorized_Discounts_{ts}.txt",
                caption=caption_text[:1020],
                parse_mode='HTML'
            )
            await context.bot.send_message(
                chat_id=user_id,
                text="⚙️ بازگشت به پنل مدیریت:",
                reply_markup=get_admin_keyboard()
            )
        except Exception as e:
            logging.error(f"Error splitting discount file: {e}")
            await msg.edit_text(f"❌ خطا در تفکیک فایل تخفیف: {e}")


# ==========================================
# توابع اصلی ورود با هویت یکتا، بررسی خرید و تولید لینک دائمی
# ==========================================
async def check_maintenance(update: Update) -> bool:
    maint = await redis_client.get("settings:maintenance")
    user_id = update.effective_user.id if update.effective_user else 0
    if maint == "1" and not is_admin(user_id):
        text = "⛔️ سیستم در حال حاضر موقتاً غیرفعال است."
        if update.message:
            await update.message.reply_text(text)
        else:
            await update.callback_query.message.reply_text(text)
        return True
    return False


async def start_login_process(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_user_authorized(update.effective_user.id):
        await show_main_menu(update, context)
        return ConversationHandler.END
    if await check_maintenance(update):
        return ConversationHandler.END
    await update.callback_query.answer()

    keys_to_clear = ['device_id', 'session_id', 'correlation_id', 'user_agent', 'session_proxy', 'phone', 'auth_data', 'admin_state', 'admin_zip_action', 'batch_collect_mode']
    for k in keys_to_clear:
        context.user_data.pop(k, None)

    kb = InlineKeyboardMarkup([[InlineKeyboardButton("❌ کنسل عملیات", callback_data="cancel_action")]])
    await update.callback_query.edit_message_text("📱 <b>لطفاً شماره موبایل خود را وارد کنید:</b>", reply_markup=kb, parse_mode='HTML')
    return PHONE


async def request_otp(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_user_authorized(update.effective_user.id):
        await show_main_menu(update, context)
        return ConversationHandler.END
    if await check_maintenance(update):
        return ConversationHandler.END
    phone = clean_digits(update.message.text)

    ttl = await redis_client.ttl(f"otp_cooldown:{phone}")
    if ttl > 0:
        minutes, seconds = divmod(ttl, 60)
        time_str = f"{minutes} دقیقه و {seconds} ثانیه" if minutes > 0 else f"{seconds} ثانیه"
        await update.message.reply_text(f"⏳ پیامک به تازگی ارسال شده است.\nلطفاً <b>{time_str}</b> صبر کنید.", parse_mode='HTML')
        return PHONE

    context.user_data['phone'] = phone
    msg = await update.message.reply_text("⏳ در حال ارتباط با سرور و ارسال پیامک...")

    url = "https://apigateway.okala.com/api/voyager/C/CustomerAccount/OTPRegister"
    payload = {"mobile": phone, "deviceTypeCode": 7, "confirmTerms": True, "notRobot": False, "otpType": 0, "ValidationCodeCreateReason": 5, "OtpApp": 0, "IsAppOnly": False}

    init_device_session(context)
    context.user_data['session_proxy'] = await get_random_proxy_from_db()
    proxy_dict = context.user_data['session_proxy']
    headers = get_user_headers(context)

    try:
        loop = asyncio.get_running_loop()
        response = await loop.run_in_executor(
            executor,
            lambda: requests.post(url, json=payload, headers=headers, proxies=proxy_dict, timeout=15)
        )

        await send_step_log(context.bot, update.effective_chat.id, f"گزارش ارسال پیامک ({phone})", response.status_code, response.text, proxy_dict)

        if response.status_code == 200:
            await redis_client.setex(f"otp_cooldown:{phone}", 120, "1")
            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 ارسال مجدد (با پروکسی جدید)", callback_data="resend_otp")],
                [InlineKeyboardButton("❌ کنسل عملیات", callback_data="cancel_action")]
            ])
            await msg.edit_text("✉️ <b>کد تایید ارسال شد.</b>\nلطفاً آن را وارد کنید:", reply_markup=kb, parse_mode='HTML')
            return OTP
        else:
            await msg.edit_text("❌ خطا در ارسال پیامک. جزئیات پاسخ سرور در پیام بالا ارسال شد.", parse_mode='HTML')
            return ConversationHandler.END

    except Exception as e:
        await send_step_log(context.bot, update.effective_chat.id, f"خطای شبکه در ارسال پیامک ({phone})", "EXCEPTION", str(e), proxy_dict)
        await msg.edit_text("❌ خطا در برقراری ارتباط با سرور. لطفاً مجدداً تلاش کنید.")
        return ConversationHandler.END


async def resend_otp_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    phone = context.user_data.get('phone')

    ttl = await redis_client.ttl(f"otp_cooldown:{phone}")
    if ttl > 0:
        minutes, seconds = divmod(ttl, 60)
        time_str = f"{minutes} دقیقه و {seconds} ثانیه" if minutes > 0 else f"{seconds} ثانیه"
        await query.answer(f"⏳ لطفاً {time_str} دیگر صبر کنید.", show_alert=True)
        return OTP

    await query.answer("در حال تغییر مسیر و ارسال مجدد... ⏳")

    url = "https://apigateway.okala.com/api/voyager/C/CustomerAccount/OTPRegister"
    payload = {"mobile": phone, "deviceTypeCode": 7, "confirmTerms": True, "notRobot": False, "otpType": 0, "ValidationCodeCreateReason": 5, "OtpApp": 0, "IsAppOnly": False}

    init_device_session(context)
    context.user_data['session_proxy'] = await get_random_proxy_from_db()
    proxy_dict = context.user_data['session_proxy']
    headers = get_user_headers(context)

    try:
        loop = asyncio.get_running_loop()
        response = await loop.run_in_executor(
            executor,
            lambda: requests.post(url, json=payload, headers=headers, proxies=proxy_dict, timeout=15)
        )

        await send_step_log(context.bot, query.message.chat_id, f"گزارش ارسال مجدد پیامک ({phone})", response.status_code, response.text, proxy_dict)

        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton("🔄 ارسال مجدد (با پروکسی جدید)", callback_data="resend_otp")],
            [InlineKeyboardButton("❌ کنسل عملیات", callback_data="cancel_action")]
        ])

        if response.status_code == 200:
            await redis_client.setex(f"otp_cooldown:{phone}", 60, "1")
            await query.edit_message_text("✉️ <b>کد تایید با مسیر جدید مجدداً ارسال شد.</b>\nکد را وارد کنید:", reply_markup=kb, parse_mode='HTML')
        else:
            await query.edit_message_text("❌ خطا در ارسال مجدد. گزارش سرور در پیام بالا ارسال شد.", reply_markup=kb, parse_mode='HTML')
    except Exception as e:
        await send_step_log(context.bot, query.message.chat_id, f"خطای شبکه در ارسال مجدد ({phone})", "EXCEPTION", str(e), proxy_dict)
        await query.edit_message_text("❌ خطا در اتصال به سرور هنگام ارسال مجدد.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ کنسل", callback_data="cancel_action")]]))

    return OTP


async def verify_otp_and_check_name(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    otp_code = clean_digits(update.message.text)
    phone = clean_digits(context.user_data.get('phone', ''))
    chat_id = update.effective_chat.id
    msg = await update.message.reply_text("⏳ در حال بررسی کد تایید...")

    token_url = "https://apigateway.okala.com/api/v1/accounts/tokens"
    payload = {
        "mobile_number": phone, "otp_code": otp_code, "grant_type": "customer_grant_type",
        "client_id": "customer_client_id", "client_secret": "u_M{'57j!%LI21#",
        "client_name": "customer_client_name", "device_type_code": 7,
        "scope": "offline_access", "loginDuration": 4815
    }

    headers = get_user_headers(context)
    headers["Content-Type"] = "application/x-www-form-urlencoded"
    proxy_dict = context.user_data.get('session_proxy')

    try:
        loop = asyncio.get_running_loop()
        response = await loop.run_in_executor(
            executor,
            lambda: requests.post(token_url, data=payload, headers=headers, proxies=proxy_dict, timeout=15)
        )

        if response.status_code == 200:
            auth_data = response.json()
            context.user_data['auth_data'] = auth_data
            access_token = auth_data.get("access_token")
            refresh_token = auth_data.get("refresh_token")
            user_info_summary = auth_data.get("UserInfo", {})

            await send_step_log(context.bot, chat_id, f"گزارش تایید کد و دریافت توکن ({phone})", response.status_code, user_info_summary, proxy_dict)

            if access_token:
                await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

            has_name = user_info_summary.get("HasName", False)

            if not has_name:
                await msg.edit_text("⚙️ اکانت خام شناسایی شد. در حال ثبت نام تصادفی...")
                first_name, last_name = get_random_persian_name()
                update_name_url = "https://apigateway.okala.com/api/voyager/C/CustomerAccount/UpdateCustomer"
                req_headers = get_user_headers(context)
                req_headers["Authorization"] = f"Bearer {access_token}"
                update_payload = {
                    "birthDate": "", "birthDateEpoch": 700086600, "customerType": 0,
                    "firstName": first_name, "genderCode": 1, "genderTitle": "مذکر",
                    "lastName": last_name, "gender": "male"
                }

                try:
                    name_res = await loop.run_in_executor(
                        executor,
                        lambda: requests.post(update_name_url, json=update_payload, headers=req_headers, proxies=proxy_dict, timeout=15)
                    )
                    await send_step_log(context.bot, chat_id, f"گزارش ثبت نام خودکار ({first_name} {last_name})", name_res.status_code, name_res.text, proxy_dict)
                except Exception as ex:
                    await send_step_log(context.bot, chat_id, f"خطا در ثبت نام خودکار ({phone})", "EXCEPTION", str(ex), proxy_dict)

                if "UserInfo" in auth_data:
                    auth_data["UserInfo"]["FirstName"] = first_name
                    auth_data["UserInfo"]["LastName"] = last_name
                    auth_data["UserInfo"]["HasName"] = True
                context.user_data['auth_data'] = auth_data

                return await generate_and_send_link(update, context, msg)

            else:
                await msg.edit_text("🔍 اکانت از قبل نام دارد. در حال بررسی دقیق سوابق خرید...")

                proxies_list = await get_all_proxies_from_db()
                api = OkalaAPI(custom_headers=get_user_headers(context), proxies_list=proxies_list)
                success, has_orders, order_count, ord_status, raw_resp = await loop.run_in_executor(
                    executor,
                    check_order_history_sync, api, access_token, proxy_dict
                )

                await send_step_log(
                    context.bot, chat_id,
                    f"گزارش بررسی سابقه خرید ({phone}) | تعداد سفارش: {order_count}",
                    ord_status, raw_resp, proxy_dict, extra_logs=api.request_logs
                )

                if not success:
                    kb = InlineKeyboardMarkup([[InlineKeyboardButton("❌ کنسل عملیات", callback_data="cancel_action")]])
                    await msg.edit_text("❌ خطا در استعلام سابقه خرید از سرور اکالا.\nلطفاً گزارش بالا را بررسی کرده و مجدداً تلاش کنید.", reply_markup=kb)
                    return OTP

                if has_orders:
                    kb = InlineKeyboardMarkup([
                        [InlineKeyboardButton("➕ امتحان خط دیگر", callback_data="user_login")],
                        [InlineKeyboardButton("🔙 بازگشت به منوی اصلی", callback_data="main_menu")]
                    ])
                    await msg.edit_text(
                        f"⛔️ <b>عملیات مسدود شد!</b>\n\n"
                        f"📱 شماره <code>{phone}</code> <b>دارای {order_count} سابقه خرید</b> در سیستم اکالا است.\n"
                        f"⚠️ از ساخت لینک برای اکانت‌های غیرخام جلوگیری شد.",
                        reply_markup=kb, parse_mode='HTML'
                    )
                    return ConversationHandler.END
                else:
                    return await generate_and_send_link(update, context, msg)

        else:
            await send_step_log(context.bot, chat_id, f"گزارش خطای تایید کد ({phone})", response.status_code, response.text, proxy_dict)

            kb = InlineKeyboardMarkup([
                [InlineKeyboardButton("🔄 ارسال مجدد (پروکسی جدید)", callback_data="resend_otp")],
                [InlineKeyboardButton("❌ کنسل عملیات", callback_data="cancel_action")]
            ])
            await msg.edit_text("❌ کد وارد شده اشتباه یا منقضی است.\nجهت جزئیات، گزارش بالا را بخوانید.", reply_markup=kb, parse_mode='HTML')
            return OTP

    except Exception as e:
        await send_step_log(context.bot, chat_id, f"خطای شبکه در تایید کد ({phone})", "EXCEPTION", str(e), proxy_dict)
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("❌ کنسل", callback_data="cancel_action")]])
        await msg.edit_text("❌ خطا در ارتباط اینترنتی سرور هنگام تایید کد. مجدداً تلاش کنید.", reply_markup=kb)
        return OTP


async def generate_and_send_link(update: Update, context: ContextTypes.DEFAULT_TYPE, status_msg) -> int:
    auth_data = context.user_data.get('auth_data')
    phone = clean_digits(context.user_data.get('phone', 'نامشخص'))
    injection_json = format_for_injector(auth_data)
    link_id = str(uuid.uuid4())[:12]

    await redis_client.set(f"acc_link:{link_id}", json.dumps(injection_json, ensure_ascii=False))
    final_url = f"{WEB_DOMAIN}/acc/{link_id}"
    await redis_client.set(f"phone_active_link:{phone}", final_url)

    if 'session_links' not in context.user_data:
        context.user_data['session_links'] = []
    context.user_data['session_links'].append({"phone": phone, "link": final_url})

    tg_user = update.effective_user
    log_entry = {"tg_id": tg_user.id, "tg_name": tg_user.full_name or "نامشخص", "tg_user": tg_user.username or "", "phone": phone, "link": final_url, "created_at": time.strftime("%Y-%m-%d %H:%M:%S")}
    await redis_client.rpush("global_link_logs", json.dumps(log_entry, ensure_ascii=False))

    count = len(context.user_data['session_links'])

    kb = InlineKeyboardMarkup([
        [InlineKeyboardButton("➕ ساخت لینک برای یک خط دیگر", callback_data="user_login")],
        [InlineKeyboardButton("🏁 پایان لینک ساختن", callback_data="finish_link_creation")],
        [InlineKeyboardButton("🔙 بازگشت به منوی اصلی", callback_data="main_menu")]
    ])

    text = (
        f"✅ <b>ورود به حساب شماره {phone} با موفقیت انجام شد.</b>\n\n"
        f"♾ لینک به صورت <b>دائمی</b> تولید شد و آماده تحویل است.\n"
        f"📊 تعداد لینک‌های آماده ارسال در این نوبت: <b>{count}</b>\n\n"
        "می‌توانید شماره دیگری اضافه کنید یا دکمه <b>«🏁 پایان لینک ساختن»</b> را بزنید."
    )
    await status_msg.edit_text(text, reply_markup=kb, parse_mode='HTML')
    return ConversationHandler.END


async def cancel_process_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    query = update.callback_query
    await query.answer("عملیات لغو شد ❌")
    await show_main_menu(update, context)
    return ConversationHandler.END


async def fallback_global_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if update.callback_query:
        await core_callback(update, context)
    return ConversationHandler.END


async def cancel(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    await update.message.reply_text("❌ عملیات متوقف شد.")
    await show_main_menu(update, context)
    return ConversationHandler.END


# ==========================================
# راه‌اندازی اصلی
# ==========================================
CALLBACK_PATTERN = (
    r"^(admin_|auth_|batch_|addr_preset_|request_bot_access$|main_menu$|"
    r"admin_panel$|finish_link_creation$|my_tags$|show_tag_)"
)


async def main():
    BOT_TOKEN = os.environ.get("BOT_TOKEN")
    if not BOT_TOKEN:
        logging.error("BOT_TOKEN environment variable is missing.")
        return

    await start_web_server()

    application = Application.builder().token(BOT_TOKEN).build()

    conv_handler = ConversationHandler(
        entry_points=[
            CallbackQueryHandler(start_login_process, pattern="^user_login$"),
            CallbackQueryHandler(ask_tag_name, pattern="^set_tag$"),
            CallbackQueryHandler(ask_search_query, pattern="^search_links$")
        ],
        states={
            PHONE: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, request_otp),
            ],
            OTP: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, verify_otp_and_check_name),
                CallbackQueryHandler(resend_otp_callback, pattern="^resend_otp$"),
            ],
            ASK_TAG: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_tag_name),
                CallbackQueryHandler(clear_active_tag_callback, pattern="^clear_active_tag$")
            ],
            ASK_SEARCH: [
                MessageHandler(filters.TEXT & ~filters.COMMAND, receive_search_query)
            ]
        },
        fallbacks=[
            CommandHandler('start', show_main_menu),
            CommandHandler('admin', admin_command),
            CommandHandler('cancel', cancel),
            CallbackQueryHandler(cancel_process_callback, pattern="^cancel_action$"),
            CallbackQueryHandler(fallback_global_callback, pattern=CALLBACK_PATTERN)
        ]
    )
    application.add_handler(conv_handler)

    application.add_handler(CommandHandler('start', show_main_menu))
    application.add_handler(CommandHandler('admin', admin_command))
    application.add_handler(CommandHandler('start_zip', trigger_batch_processing))
    application.add_handler(CommandHandler('start_batch', trigger_batch_processing))

    application.add_handler(MessageHandler(filters.Document.FileExtension("zip"), handle_zip_upload))
    application.add_handler(CallbackQueryHandler(core_callback, pattern=CALLBACK_PATTERN))
    application.add_handler(
        MessageHandler(
            (filters.TEXT & ~filters.COMMAND) | filters.Document.FileExtension("txt") | filters.Document.FileExtension("json"),
            handle_admin_text_document
        )
    )

    await application.initialize()
    await application.start()
    await application.updater.start_polling()

    # راه‌اندازی سرویس چرخش خودکار توکن‌ها در پس‌زمینه
    asyncio.create_task(auto_refresh_background_task(application.bot))

    logging.info("System initialized successfully with Auto-Refresh background task.")
    stop_signal = asyncio.Event()
    await stop_signal.wait()


if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass