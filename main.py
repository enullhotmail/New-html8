import os
import re
import shutil
import asyncio
import json
import base64
import requests
import time
import uuid
import urllib.parse
import io
import tempfile
import random
import html
from datetime import datetime
import redis.asyncio as redis 
from concurrent.futures import ThreadPoolExecutor
from aiohttp import web
from telegram import Update, InlineKeyboardMarkup, InlineKeyboardButton
from telegram.ext import Application, CommandHandler, MessageHandler, filters, ContextTypes, ConversationHandler, CallbackQueryHandler
import logging

logging.basicConfig(format='%(asctime)s - %(name)s - %(levelname)s - %(message)s', level=logging.INFO)

REDIS_URL = os.environ.get("REDIS_URL", "redis://localhost:6379")
redis_client = redis.Redis.from_url(REDIS_URL, decode_responses=True, max_connections=50)

WEB_DOMAIN = os.environ.get("WEB_DOMAIN", "http://localhost:8080").rstrip('/')
ADMIN_IDS = [int(aid.strip()) for aid in os.environ.get("ADMIN_ID", "0").split(",") if aid.strip().isdigit()]

PHONE, OTP, ASK_TAG, ASK_SEARCH = range(4)

executor = ThreadPoolExecutor(max_workers=30)

USER_AGENTS = [
    "Mozilla/5.0 (Linux; Android 13; SM-S918B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/114.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 12; Pixel 6 Pro) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/112.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 11; SM-G991B) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/111.0.0.0 Mobile Safari/537.36",
    "Mozilla/5.0 (Linux; Android 10; K) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/110.0.0.0 Mobile Safari/537.36"
]

FIRST_NAMES = ["علی", "محمد", "امیر", "حسین", "رضا", "مهدی", "سجاد", "نیما", "عرفان", "پوریا", "سارا", "مریم", "فاطمه", "زهرا", "الهام", "نرگس", "یلدا", "نگار", "مهسا"]
LAST_NAMES = ["محمدی", "حسینی", "احمدی", "رضایی", "کریمی", "موسوی", "جعفری", "قاسمی", "حیدری", "صادقی", "مرادی", "رحیمی", "اکبری", "طاهری", "رستمی"]

def clean_digits(text: str) -> str:
    """تبدیل خودکار ارقام فارسی و عربی به انگلیسی"""
    if not text: return ""
    return text.translate(str.maketrans('۰۱۲۳۴۵۶۷۸۹٠١٢٣٤٥٦٧٨٩', '01234567890123456789')).strip()

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

def parse_and_split_discounts(text_content: str):
    """تحلیل متن یا فایل گزارش تخفیف و دسته‌بندی لینک‌ها بر اساس مبلغ (بدون شماره)"""
    clean_text = re.sub(r'<[^>]+>', '', text_content)
    clean_text = clean_digits(clean_text)
    grouped = {}
    total_links = 0
    current_amount = None

    for line in clean_text.splitlines():
        line = line.strip()
        if not line:
            continue

        amt_match = re.search(r'بیشترین مبلغ\s*:\s*(\d+)', line)
        if amt_match:
            current_amount = int(amt_match.group(1))
            continue

        link_match = re.search(r'(https?://[^\s]+)', line)
        if link_match and current_amount is not None:
            link = link_match.group(1).strip()
            grouped.setdefault(current_amount, []).append(link)
            total_links += 1
            current_amount = None

    return grouped, total_links

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
    try:
        payload = token.split('.')[1]
        payload += '=' * (-len(payload) % 4)
        decoded_bytes = base64.urlsafe_b64decode(payload)
        return json.loads(decoded_bytes)
    except Exception:
        return {}

def get_user_id_from_token(token):
    data = decode_jwt_payload(token)
    return data.get('cerberusId') or data.get('alternativeCustomerId') or data.get('userId')

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
            for c in updated["cookies"]:
                if c.get("name") in ["tokenMS", "token"] and new_acc:
                    c["value"] = new_acc
                elif c.get("name") == "refresh_token" and new_ref:
                    c["value"] = new_ref

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
                    try: return 200, res.json()
                    except: return 200, {}
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
        state: 'success' | 'unrecoverable' | 'proxy_error'
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

    def check_discount_api(self, token, uid, proxy_dict=None, fast_mode=True):
        url = f"https://apigateway.okala.com/api/discount/v1/discounts/customer/{uid}"
        return self.make_request('GET', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode)

    def get_addresses_api(self, token, proxy_dict=None, fast_mode=True):
        url = "https://apigateway.okala.com/api/v1/accounts/userprofile/getcustomeraddresseswithpaging?pageIndex=1&pageSize=15"
        return self.make_request('GET', url, access_token=token, proxy_dict=proxy_dict, fast_mode=fast_mode)

    def get_orders_api(self, token, proxy_dict=None, keep_session_ids=False, fast_mode=True):
        url = "https://apigateway.okala.com/api/voyager/C/Order/GetOrders"
        payload = {"pageIndex": 1, "pageSize": 5}
        return self.make_request('POST', url, access_token=token, proxy_dict=proxy_dict, keep_session_ids=keep_session_ids, fast_mode=fast_mode, json=payload)

def parse_orders_response(status, response_data):
    if status == 200 and isinstance(response_data, dict):
        data = response_data.get('data', {})
        if isinstance(data, list):
            return True, len(data) > 0, len(data)
        elif isinstance(data, dict):
            orders = data.get('orders') or data.get('items') or []
            total_count = data.get('totalCount')
            if total_count is not None and int(total_count) > 0:
                return True, True, int(total_count)
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
    mobile = user_info.get("MobilePhone") or jwt_data.get("mobilePhone") or ""
    
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

# ==========================================
# نوسازی تمام توکن‌ها، احیای دائمی لینک‌ها و شناسایی اکانت‌های سوخته
# ==========================================
async def process_refresh_and_revive_all(bot, chat_id, acc_keys):
    loop = asyncio.get_running_loop()
    proxies_list = await get_all_proxies_from_db()
    api = OkalaAPI(proxies_list=proxies_list)
    ts = int(time.time())

    if not proxies_list:
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
            p = entry.get('phone')
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
                            p = u_obj.get("mobilePhone")
                            if p:
                                phone_to_link_id[p] = lid
                            break
        except Exception:
            pass

    total = len(acc_keys)
    progress_msg = await bot.send_message(
        chat_id=chat_id,
        text=f"♻️ شروع بررسی دیتابیس، نوسازی توکن‌ها و تولید دائمی لینک‌ها برای <b>{total}</b> اکانت...\n⏳ لطفاً منتظر بمانید.",
        parse_mode='HTML'
    )

    detail_logs = []
    active_links_list = []
    unrecoverable_phones = []
    stats = {"updated": 0, "recreated": 0, "unrecoverable": 0, "proxy_error": 0}
    done = 0
    last_edit_time = 0
    lock = asyncio.Lock()
    sem = asyncio.Semaphore(20)

    async def _worker(idx, key):
        nonlocal done, last_edit_time
        phone = key.replace("account:", "")
        async with sem:
            try:
                token_data = await redis_client.hgetall(key)
                old_acc = token_data.get("access_token", "")
                old_ref = token_data.get("refresh_token", "")

                if not old_ref:
                    async with lock:
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ {phone} | فاقد refresh_token (غیرقابل بازگشت)\n")
                        stats["unrecoverable"] += 1
                        unrecoverable_phones.append(phone)
                        done += 1
                    return

                state, new_acc, new_ref, status_code, raw_resp = await loop.run_in_executor(
                    executor, api.refresh_token_sequential_proxy, old_ref, idx
                )

                if state == "success" and new_acc:
                    final_ref = new_ref or old_ref
                    await redis_client.hset(key, mapping={"access_token": new_acc, "refresh_token": final_ref})

                    link_id = phone_to_link_id.get(phone)
                    if not link_id:
                        active_url = await redis_client.get(f"phone_active_link:{phone}")
                        if active_url and '/acc/' in active_url:
                            link_id = active_url.split('/acc/')[-1].strip()

                    link_recreated = False
                    if link_id and await redis_client.exists(f"acc_link:{link_id}"):
                        old_link_str = await redis_client.get(f"acc_link:{link_id}")
                        updated_data = update_tokens_in_data(old_link_str, old_acc, new_acc, old_ref, final_ref)
                        await redis_client.set(f"acc_link:{link_id}", json.dumps(updated_data, ensure_ascii=False))
                    else:
                        if not link_id:
                            link_id = str(uuid.uuid4())[:12]
                        auth_data = {
                            "access_token": new_acc,
                            "refresh_token": final_ref,
                            "UserInfo": {"MobilePhone": phone, "HasName": True}
                        }
                        injection_json = format_for_injector(auth_data)
                        await redis_client.set(f"acc_link:{link_id}", json.dumps(injection_json, ensure_ascii=False))
                        link_recreated = True

                    final_url = f"{WEB_DOMAIN}/acc/{link_id}"
                    await redis_client.set(f"phone_active_link:{phone}", final_url)

                    async with lock:
                        if link_recreated:
                            stats["recreated"] += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 🆕 {phone} | توکن نوسازی شد + لینک دائمی مجدداً تولید شد: {final_url}\n")
                        else:
                            stats["updated"] += 1
                            detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ✅ {phone} | توکن نوسازی شد + لینک دائمی آپدیت شد: {final_url}\n")
                        active_links_list.append({"phone": phone, "link": final_url})

                elif state == "unrecoverable":
                    async with lock:
                        stats["unrecoverable"] += 1
                        unrecoverable_phones.append(phone)
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] 💀 {phone} | غیرقابل بازگشت (کد: {status_code}) | پاسخ: {str(raw_resp)[:200]}\n")

                else:
                    async with lock:
                        stats["proxy_error"] += 1
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} | خطای شبکه/پروکسی پس از چرخش پروکسی‌ها (کد: {status_code})\n")

                async with lock:
                    done += 1
                    now = time.time()
                    if (now - last_edit_time >= 2.0) or (done == total):
                        last_edit_time = now
                        try:
                            await progress_msg.edit_text(
                                f"♻️ <b>در حال نوسازی توکن‌ها و احیای دائمی لینک‌ها...</b>\n"
                                f"📊 پیشرفت: <b>{done}/{total}</b>\n"
                                f"✅ نوسازی و آپدیت لینک: <b>{stats['updated']}</b>\n"
                                f"🆕 تولید مجدد لینک حذف‌شده: <b>{stats['recreated']}</b>\n"
                                f"💀 غیرقابل بازگشت (توکن باطل): <b>{stats['unrecoverable']}</b>\n"
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
            f"کل اکانت‌ها: {total} | آپدیت‌شده: {stats['updated']} | لینک مجدد تولیدشده: {stats['recreated']} | "
            f"غیرقابل بازگشت: {stats['unrecoverable']} | خطای پروکسی: {stats['proxy_error']}\n"
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
        f"✅ <b>عملیات بررسی دیتابیس و نوسازی توکن‌ها پایان یافت.</b>\n\n"
        f"👥 <b>کل اکانت‌های بررسی شده:</b> <code>{total}</code>\n"
        f"♻️ <b>توکن نوسازی و لینک دائمی آپدیت شد:</b> <code>{stats['updated']}</code>\n"
        f"🆕 <b>لینک حذف‌شده مجدداً به صورت دائمی تولید شد:</b> <code>{stats['recreated']}</code>\n"
        f"⚠️ <b>خطای شبکه/پروکسی (بدون تغییر):</b> <code>{stats['proxy_error']}</code>\n"
        f"💀 <b>اکانت‌های غیرقابل بازگشت (توکن باطل):</b> <code>{stats['unrecoverable']}</code>\n"
    )

    if unrecoverable_phones:
        summary_text += (
            f"\n❓ <b>آیا مایلید <code>{len(unrecoverable_phones)}</code> اکانت غیرقابل بازگشت به طور کامل از دیتابیس حذف شوند؟</b>"
        )
        kb = InlineKeyboardMarkup([
            [InlineKeyboardButton(f"🗑 بله، حذف {len(unrecoverable_phones)} اکانت سوخته", callback_data="admin_confirm_delete_dead")],
            [InlineKeyboardButton("❌ خیر، نادیده بگیر", callback_data="admin_cancel_delete_dead")],
            [InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]
        ])
    else:
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]])

    await bot.send_message(chat_id=chat_id, text=summary_text, reply_markup=kb, parse_mode='HTML')

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
            text="⚠️ <b>هیچ پروکسی‌ای در سیستم تنظیم نشده است!</b>\n"
                 "بررسی بدون پروکسی ادامه می‌یابد.",
            parse_mode='HTML'
        )

    raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
    phone_to_latest_link = {}
    for item in raw_logs:
        try:
            entry = json.loads(item)
            phone_to_latest_link[entry['phone']] = entry['link']
        except:
            pass

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
        phone = key.replace("account:", "")
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
                    await redis_client.hset(key, mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                link = None
                if result_state == "raw":
                    link = phone_to_latest_link.get(phone) or await redis_client.get(f"phone_active_link:{phone}")
                    link_id = link.split('/acc/')[-1].strip() if (link and '/acc/' in link) else None

                    if link_id and await redis_client.exists(f"acc_link:{link_id}"):
                        if new_acc:
                            old_l_data = await redis_client.get(f"acc_link:{link_id}")
                            updated_l = update_tokens_in_data(old_l_data, old_acc, access_token, old_ref, refresh_token)
                            await redis_client.set(f"acc_link:{link_id}", json.dumps(updated_l, ensure_ascii=False))
                    else:
                        if not link_id:
                            link_id = str(uuid.uuid4())[:12]
                        auth_data = {"access_token": access_token, "refresh_token": refresh_token or "", "UserInfo": {"MobilePhone": phone}}
                        injection_json = format_for_injector(auth_data)
                        await redis_client.set(f"acc_link:{link_id}", json.dumps(injection_json, ensure_ascii=False))
                        link = f"{WEB_DOMAIN}/acc/{link_id}"
                        await redis_client.set(f"phone_active_link:{phone}", link)

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
# پردازش پرسرعت تخفیف‌ها از دیتابیس
# ==========================================
async def process_discounts_and_send_report(bot, chat_id, acc_keys):
    loop = asyncio.get_running_loop()
    proxies_list = await get_all_proxies_from_db()
    api = OkalaAPI(proxies_list=proxies_list)
    ts = int(time.time())

    if not proxies_list:
        await bot.send_message(
            chat_id=chat_id,
            text="⚠️ <b>هیچ پروکسی‌ای در سیستم تنظیم نشده است!</b>\n"
                 "بررسی تخفیف بدون پروکسی ادامه می‌یابد.",
            parse_mode='HTML'
        )

    raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
    phone_to_latest_link = {}
    for item in raw_logs:
        try:
            entry = json.loads(item)
            phone_to_latest_link[entry['phone']] = entry['link']
        except:
            pass

    total = len(acc_keys)
    progress_msg = await bot.send_message(
        chat_id=chat_id,
        text=f"⚡ شروع بررسی موازی <b>{total}</b> اکانت با پروکسی (۲۰ اکانت همزمان)...\n⏳ لطفاً منتظر بمانید.",
        parse_mode='HTML'
    )

    detail_logs = []
    discount_results = []
    done = 0
    last_edit_time = 0
    lock = asyncio.Lock()
    sem = asyncio.Semaphore(20)

    def _check_sync(acc_token, ref_token, uid, p_dict, phone, idx):
        proxy_ip = mask_proxy(p_dict)
        log_line = f"[{time.strftime('%H:%M:%S')}] 📱 {phone} | UUID: {uid} | پروکسی: {proxy_ip}\n"

        status, res = api.check_discount_api(acc_token, uid, proxy_dict=p_dict, fast_mode=True)

        if status == 401 and ref_token:
            log_line += f"  ♻️ توکن منقضی — در حال رفرش با چرخش پروکسی...\n"
            st, new_acc, new_ref, _, _ = api.refresh_token_sequential_proxy(ref_token, start_proxy_idx=idx)
            if st == "success" and new_acc:
                status, res = api.check_discount_api(new_acc, uid, proxy_dict=p_dict, fast_mode=True)
                log_line += f"  ✅ رفرش موفق — بررسی مجدد انجام شد.\n"
                return status, res, new_acc, new_ref, log_line
            else:
                log_line += f"  ❌ رفرش ناموفق.\n"
        
        if status == 200 and isinstance(res, dict):
            vouchers = res.get('data', [])
            amounts = [v.get('discountAmount', 0) for v in vouchers if v.get('discountAmount')]
            if vouchers:
                log_line += f"  🎁 تخفیف یافت شد: {len(vouchers)} کد | بیشترین مبلغ: {max(amounts)//10000 if amounts else '?'} هزار تومان\n"
            else:
                log_line += f"  ➖ بدون تخفیف (پاسخ 200)\n"
        elif status == 401:
            log_line += f"  🔒 توکن کاملاً منقضی شده.\n"
        else:
            log_line += f"  ❌ خطا — کد پاسخ: {status}\n"

        return status, res, None, None, log_line

    async def _worker(idx, key):
        nonlocal done, last_edit_time
        phone = key.replace("account:", "")
        async with sem:
            try:
                token_data = await redis_client.hgetall(key)
                access_token = token_data.get("access_token")
                refresh_token = token_data.get("refresh_token")

                if not access_token:
                    async with lock:
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} — توکن موجود نیست، رد شد.\n")
                        done += 1
                    return

                user_uuid = get_user_id_from_token(access_token)
                if not user_uuid:
                    async with lock:
                        detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ⚠️ {phone} — UUID قابل استخراج نیست، رد شد.\n")
                        done += 1
                    return

                proxy_dict = get_proxy_by_index(proxies_list, idx)

                status, res, new_acc, new_ref, log_line = await loop.run_in_executor(
                    executor, _check_sync, access_token, refresh_token, user_uuid, proxy_dict, phone, idx
                )

                old_acc = access_token
                old_ref = refresh_token
                if new_acc:
                    access_token = new_acc
                    refresh_token = new_ref or refresh_token
                    await redis_client.hset(key, mapping={"access_token": access_token, "refresh_token": refresh_token or ""})

                old_link = phone_to_latest_link.get(phone) or await redis_client.get(f"phone_active_link:{phone}") or ""

                if status == 200 and isinstance(res, dict):
                    vouchers = res.get('data', [])
                    if vouchers:
                        link_id = old_link.split('/acc/')[-1].strip() if (old_link and '/acc/' in old_link) else None
                        if link_id and await redis_client.exists(f"acc_link:{link_id}"):
                            if new_acc:
                                old_l_data = await redis_client.get(f"acc_link:{link_id}")
                                updated_l = update_tokens_in_data(old_l_data, old_acc, access_token, old_ref, refresh_token)
                                await redis_client.set(f"acc_link:{link_id}", json.dumps(updated_l, ensure_ascii=False))
                        else:
                            if not link_id:
                                link_id = str(uuid.uuid4())[:12]
                            auth_data = {"access_token": access_token, "refresh_token": refresh_token or "", "UserInfo": {"MobilePhone": phone}}
                            injection_json = format_for_injector(auth_data)
                            await redis_client.set(f"acc_link:{link_id}", json.dumps(injection_json, ensure_ascii=False))
                            old_link = f"{WEB_DOMAIN}/acc/{link_id}"
                            await redis_client.set(f"phone_active_link:{phone}", old_link)

                        amounts = [v.get('discountAmount', 0) for v in vouchers if v.get('discountAmount')]
                        max_amount = max(amounts) // 10000 if amounts else 0
                        async with lock:
                            discount_results.append({
                                "phone": phone,
                                "count": len(vouchers),
                                "max_amount": max_amount,
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
                                f"⚡ بررسی موازی اکانت‌ها...\n"
                                f"✅ انجام شده: <b>{done}/{total}</b>\n"
                                f"🎁 دارای تخفیف تاکنون: <b>{len(discount_results)}</b>",
                                parse_mode='HTML'
                            )
                        except Exception:
                            pass
            except Exception as e:
                async with lock:
                    detail_logs.append(f"[{time.strftime('%H:%M:%S')}] ❌ خطای کلی برای {key}: {e}\n")
                    done += 1

    await asyncio.gather(*[_worker(i, k) for i, k in enumerate(acc_keys)])

    if discount_results:
        report_text = f"🎁 <b>گزارش بررسی تخفیف‌ها ({len(discount_results)} اکانت دارای تخفیف از {total}):</b>\n\n"
        for r in discount_results:
            link_line = f"🔗 {r['link']}" if r['link'] else "⚠️ لینک ثبت‌شده‌ای در دیتابیس یافت نشد"
            report_text += (
                f"📱 شماره: <code>{r['phone']}</code>\n"
                f"🎟 تعداد کد تخفیف: <b>{r['count']}</b> | بیشترین مبلغ: <b>{r['max_amount']} هزار تومان</b>\n"
                f"{link_line}\n"
                f"{'─'*30}\n"
            )
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
            await bot.send_document(
                chat_id=chat_id, document=file_out,
                filename=f"Discounts_Report_{ts}.txt",
                caption=f"✅ گزارش کامل تخفیف‌ها — {len(discount_results)} اکانت دارای تخفیف"
            )
        else:
            await bot.send_message(chat_id=chat_id, text=report_text, parse_mode='HTML', disable_web_page_preview=True)
    except Exception as e:
        logging.error(f"Error sending discount report: {e}")

    try:
        full_log = f"=== لاگ بررسی تخفیف | {time.strftime('%Y-%m-%d %H:%M:%S')} ===\n"
        full_log += f"کل اکانت‌ها: {total} | دارای تخفیف: {len(discount_results)}\n"
        full_log += "=" * 50 + "\n\n"
        full_log += "".join(detail_logs)
        full_log += "\n\n=== لاگ درخواست‌های HTTP ===\n"
        full_log += "".join(api.request_logs)

        log_out = io.BytesIO(full_log.encode('utf-8'))
        await bot.send_document(
            chat_id=chat_id, document=log_out,
            filename=f"Discount_Full_Log_{ts}.txt",
            caption=f"📄 لاگ کامل سرور و پاسخ‌ها ({total} اکانت)"
        )
    except Exception as e:
        logging.error(f"Error sending log file: {e}")

# ==========================================
# پردازش فایل زیپ (با تولید لینک دائمی)
# ==========================================
async def handle_zip_upload(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not is_admin(user_id): return
    
    file_name = update.message.document.file_name.lower()
    if not file_name.endswith('.zip'):
        await update.message.reply_text("❌ فایل ارسالی نامعتبر است. لطفاً فایل زیپ (.zip) ارسال کنید.")
        return
        
    action = context.user_data.get('admin_zip_action', 'zip_to_link')
    msg = await update.message.reply_text("⏳ در حال دریافت و استخراج فایل...")
    
    new_file = await update.message.document.get_file()
    
    with tempfile.TemporaryDirectory() as temp_dir:
        zip_path = os.path.join(temp_dir, "uploaded.zip")
        await new_file.download_to_drive(zip_path)
        
        extracted_dir = os.path.join(temp_dir, "extracted")
        await asyncio.to_thread(shutil.unpack_archive, zip_path, extracted_dir)
        
        json_files_paths = []
        for root, dirs, files in os.walk(extracted_dir):
            for file in files:
                if file.lower().endswith('.json'):
                    json_files_paths.append(os.path.join(root, file))
                    
        if not json_files_paths:
            await msg.edit_text("⚠️ هیچ فایل JSON معتبری در فایل زیپ یافت نشد.")
            return

        if action == 'zip_to_link':
            links_text = "<b>لیست لینک‌های دائمی تولید شده:</b>\n\n"
            count = 0
            for file_path in json_files_paths:
                filename = os.path.basename(file_path)
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        file_content = f.read()
                        data = json.loads(file_content)
                        access_token, refresh_token = None, None
                        for cookie in data.get('cookies', []):
                            if cookie.get('name') == 'tokenMS': access_token = cookie.get('value')
                            elif cookie.get('name') == 'refresh_token': refresh_token = cookie.get('value')
                        if not access_token:
                            for origin in data.get('origins', []):
                                for item in origin.get('localStorage', []):
                                    if item.get('name') == 'tokenMS': access_token = item.get('value')
                                    elif item.get('name') == 'refresh_token': refresh_token = item.get('value')
                        phone = filename.replace('.json', '')
                        if access_token:
                            await redis_client.hset(f"account:{phone}", mapping={"access_token": access_token, "refresh_token": refresh_token or ""})
                        link_id = str(uuid.uuid4())[:12]
                        await redis_client.set(f"acc_link:{link_id}", file_content)
                        final_url = f"{WEB_DOMAIN}/acc/{link_id}"
                        await redis_client.set(f"phone_active_link:{phone}", final_url)
                        links_text += f"📱 <b>شماره {phone}:</b>\n{final_url}\n\n"
                        count += 1
                except Exception:
                    pass
            if len(links_text) > 4000:
                clean_links = re.sub(r'<[^>]+>', '', links_text)
                file_out = io.BytesIO(clean_links.encode('utf-8'))
                await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Links_{int(time.time())}.txt", caption=f"✅ استخراج {count} اکانت به صورت دائمی انجام شد.")
                await msg.delete()
            else:
                await msg.edit_text(f"✅ <b>تعداد {count} اکانت به صورت دائمی ذخیره شد:</b>\n\n{links_text}", disable_web_page_preview=True, parse_mode='HTML')

        elif action == 'zip_discount_check':
            await msg.edit_text(f"⚡ در حال بررسی موازی وضعیت تخفیف {len(json_files_paths)} فایل...")
            discount_dir = os.path.join(temp_dir, "Discount_Accounts")
            os.makedirs(os.path.join(discount_dir, 'accounts'), exist_ok=True)
            links_text = "<b>لیست لینک‌های دارای تخفیف:</b>\n\n"
            discount_count = 0
            
            proxies_list = await get_all_proxies_from_db()
            api = OkalaAPI(proxies_list=proxies_list)
            loop = asyncio.get_running_loop()
            sem = asyncio.Semaphore(20)
            lock = asyncio.Lock()

            raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
            phone_to_latest_link = {}
            for item in raw_logs:
                try:
                    entry = json.loads(item)
                    phone_to_latest_link[entry['phone']] = entry['link']
                except: pass
            
            def _check_sync_zip(acc_token, ref_token, uid, p_dict, idx):
                status, res = api.check_discount_api(acc_token, uid, proxy_dict=p_dict, fast_mode=True)
                if status == 401 and ref_token:
                    st, new_acc, new_ref, _, _ = api.refresh_token_sequential_proxy(ref_token, start_proxy_idx=idx)
                    if st == "success" and new_acc:
                        status, res = api.check_discount_api(new_acc, uid, proxy_dict=p_dict, fast_mode=True)
                        return status, res, new_acc, new_ref
                return status, res, None, None
            
            async def _zip_worker(idx, file_path):
                nonlocal discount_count, links_text
                filename = os.path.basename(file_path)
                async with sem:
                    try:
                        with open(file_path, 'r', encoding='utf-8') as f:
                            file_content = f.read()
                            data = json.loads(file_content)
                            access_token = None
                            refresh_token = None
                            phone = filename.replace('.json', '')
                            for cookie in data.get('cookies', []):
                                if cookie.get('name') == 'tokenMS': access_token = cookie.get('value')
                                if cookie.get('name') == 'refresh_token': refresh_token = cookie.get('value')
                            if not access_token:
                                for origin in data.get('origins', []):
                                    for item in origin.get('localStorage', []):
                                        if item.get('name') == 'tokenMS': access_token = item.get('value')
                                        if item.get('name') == 'refresh_token': refresh_token = item.get('value')
                            
                            if access_token:
                                user_uuid = get_user_id_from_token(access_token)
                                if user_uuid:
                                    proxy_dict = get_proxy_by_index(proxies_list, idx)
                                    status, res, new_acc, new_ref = await loop.run_in_executor(
                                        executor, _check_sync_zip, access_token, refresh_token, user_uuid, proxy_dict, idx
                                    )
                                    
                                    if new_acc:
                                        data = update_tokens_in_data(data, access_token, new_acc, refresh_token, new_ref)
                                        file_content = json.dumps(data, ensure_ascii=False)
                                        with open(file_path, 'w', encoding='utf-8') as fw:
                                            fw.write(file_content)

                                    if status == 200 and isinstance(res, dict):
                                        vouchers = res.get('data', [])
                                        if vouchers:
                                            old_link = phone_to_latest_link.get(phone) or await redis_client.get(f"phone_active_link:{phone}")
                                            if not old_link:
                                                lid = str(uuid.uuid4())[:12]
                                                await redis_client.set(f"acc_link:{lid}", file_content)
                                                old_link = f"{WEB_DOMAIN}/acc/{lid}"
                                                await redis_client.set(f"phone_active_link:{phone}", old_link)
                                            async with lock:
                                                discount_count += 1
                                                shutil.copy2(file_path, os.path.join(discount_dir, 'accounts', filename))
                                                links_text += f"📱 <b>شماره {phone}:</b>\n{old_link}\n\n"
                    except Exception as e:
                        async with lock:
                            api.request_logs.append(f"[{filename}] Exception: {str(e)}\n{'-'*40}\n")

            await asyncio.gather(*[_zip_worker(i, fp) for i, fp in enumerate(json_files_paths)])
            debug_logs = api.request_logs
            
            if discount_count > 0:
                discount_zip_path = os.path.join(temp_dir, "Discounted_Accounts")
                await asyncio.to_thread(shutil.make_archive, discount_zip_path, 'zip', discount_dir)
                await msg.delete()
                with open(discount_zip_path + '.zip', 'rb') as zip_file:
                    await context.bot.send_document(chat_id=user_id, document=zip_file, filename="Discounted_Accounts.zip", caption=f"🎁 <b>فایل خروجی (فیلتر شده)</b>\nتعداد اکانت‌های دارای تخفیف: {discount_count}", parse_mode='HTML')
                if len(links_text) > 4000:
                    clean_links = re.sub(r'<[^>]+>', '', links_text)
                    file_out = io.BytesIO(clean_links.encode('utf-8'))
                    await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Discount_Links_{int(time.time())}.txt", caption="🔗 لینک‌های دسترسی سریع")
                else:
                    await context.bot.send_message(chat_id=user_id, text=links_text, disable_web_page_preview=True, parse_mode='HTML')
            else:
                await msg.edit_text("⚠️ هیچ‌یک از اکانت‌های موجود دارای تخفیف نبودند.")
                
            if debug_logs:
                debug_out = io.BytesIO("".join(debug_logs).encode('utf-8'))
                await context.bot.send_document(chat_id=user_id, document=debug_out, filename=f"Discount_Debug_Log_{int(time.time())}.txt", caption="📄 فایل لاگ پاسخ درخواست‌های سرور")

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
# منوها و دکمه‌ها
# ==========================================
def get_main_keyboard(is_admin_user, active_tag_name=None):
    keyboard = [[InlineKeyboardButton("🔑 ورود به حساب (ساخت لینک دائمی)", callback_data="user_login")]]
    
    tag_btn_text = f"🏷 تغییر/حذف برچسب (فعال: {active_tag_name})" if active_tag_name else "🏷 تنظیم برچسب نشست (Tag)"
    keyboard.append([InlineKeyboardButton(tag_btn_text, callback_data="set_tag")])
    
    keyboard.append([
        InlineKeyboardButton("📂 برچسب‌های من", callback_data="my_tags"),
        InlineKeyboardButton("🔍 جستجوی لینک", callback_data="search_links")
    ])
    
    if is_admin_user:
        keyboard.append([InlineKeyboardButton("⚙️ پنل مدیریت", callback_data="admin_panel")])
    return InlineKeyboardMarkup(keyboard)

def get_admin_keyboard():
    keyboard = [
        [InlineKeyboardButton("📊 آمار دیتابیس", callback_data="admin_stats"), InlineKeyboardButton("📋 گزارش لینک‌های کاربران", callback_data="admin_users_report")],
        [InlineKeyboardButton("♻️ نوسازی توکن‌ها و احیای دائمی لینک‌ها", callback_data="admin_refresh_and_revive")],
        [InlineKeyboardButton("🧹 استخراج اکانت‌های خام (بدون خرید و آدرس)", callback_data="admin_extract_raw")],
        [InlineKeyboardButton("🎁 بررسی تخفیف دیتابیس", callback_data="admin_check_discounts"), InlineKeyboardButton("📂 تفکیک فایل تخفیف", callback_data="admin_split_discount_file")],
        [InlineKeyboardButton("🔗 تبدیل زیپ به لینک", callback_data="admin_zip_to_link"), InlineKeyboardButton("🔍 بررسی تخفیف زیپ", callback_data="admin_zip_discount")],
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
    text = "👋 <b>به سیستم لینک‌ساز دائمی خوش آمدید.</b>\n\nلطفاً یک گزینه را انتخاب کنید:"
    
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
        f"✅ برچسب <b>«{ html.escape(tag_name)}»</b> با موفقیت تنظیم شد.\nاکنون می‌توانید شروع به ساختن لینک کنید.", 
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
    
    raw_logs = await redis_client.lrange("global_link_logs", 0, -1)
    phone_to_latest_link = {}
    
    for item in raw_logs:
        try:
            entry = json.loads(item)
            phone_to_latest_link[entry['phone']] = entry['link']
        except: pass
        
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
            await query.edit_message_text(
                safe_orig_text + "\n\n✅ <b>توسط ادمین تایید شد.</b>",
                parse_mode='HTML'
            )
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
            await query.edit_message_text(
                safe_orig_text + "\n\n❌ <b>توسط ادمین رد شد.</b>",
                parse_mode='HTML'
            )
            try:
                await context.bot.send_message(
                    chat_id=target_uid,
                    text="⛔️ متاسفانه درخواست دسترسی شما به ربات توسط مدیریت رد شد."
                )
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
            except: pass
            
        if len(report_text) > 4000:
            clean_rep = re.sub(r'<[^>]+>', '', report_text)
            file_out = io.BytesIO(clean_rep.encode('utf-8'))
            await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Tag_{t_name}.txt", caption=f"📂 تمامی لینک‌های مربوط به برچسب: {t_name}")
            await context.bot.send_message(chat_id=user_id, text="بازگشت به لیست برچسب‌ها:", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت", callback_data="my_tags")]]))
        else:
            await query.edit_message_text(report_text, disable_web_page_preview=True, parse_mode='HTML', reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت", callback_data="my_tags")]]))
        return

    # === بخش مربوط به مدیریت ادمین ===
    if not is_admin(user_id): return
    await query.answer()
    
    if data == "admin_panel":
        context.user_data['admin_state'] = None
        context.user_data['admin_zip_action'] = None
        await query.edit_message_text("⚙️ <b>پنل مدیریت سیستم:</b>", reply_markup=get_admin_keyboard(), parse_mode='HTML')
        
    elif data == "admin_set_proxy":
        context.user_data['admin_state'] = 'waiting_for_proxy'
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]])
        await query.edit_message_text(
            "🌐 <b>تنظیم پروکسی‌ها:</b>\n\n"
            "لطفاً لیست پروکسی‌های خود را (به صورت متن در همین پیام یا یک فایل <code>.txt</code>) ارسال کنید.\n\n"
            "⚠️ <b>فرمت مجاز:</b> <code>user:pass@host:port</code> یا <code>http://user...</code>", 
            reply_markup=kb,
            parse_mode='HTML'
        )

    elif data == "admin_split_discount_file":
        context.user_data['admin_state'] = 'waiting_for_discount_split'
        kb = InlineKeyboardMarkup([[InlineKeyboardButton("🔙 بازگشت به پنل مدیریت", callback_data="admin_panel")]])
        await query.edit_message_text(
            "📂 <b>تفکیک و دسته‌بندی فایل تخفیف بر اساس مبلغ:</b>\n\n"
            "لطفاً فایل متنی گزارش تخفیف‌ها (<code>Discounts_Report_...txt</code>) یا متن پیام گزارش را ارسال کنید.\n\n"
            "🔹 ربات به صورت خودکار شماره‌ها را حذف کرده و لینک‌ها را بر اساس مبلغ تخفیف (مثلاً ۵۰ هزار تومانی، ۱۰۰ هزار تومانی و...) دسته‌بندی و ارسال می‌کند.",
            reply_markup=kb,
            parse_mode='HTML'
        )

    elif data == "admin_stats":
        acc_keys = await redis_client.keys("account:*")
        link_keys = await redis_client.keys("acc_link:*")
        auth_users = await redis_client.scard("authorized_users")
        proxies = await get_all_proxies_from_db()
        proxy_count = len(proxies)
        
        maint = await redis_client.get("settings:maintenance")
        status = "غیرفعال 🔴" if maint == "1" else "فعال 🟢"
        
        text = (
            "📊 <b>وضعیت سیستم:</b>\n\n"
            f"👤 <b>تعداد کل اکانت‌ها:</b> <code>{len(acc_keys)}</code>\n"
            f"🔗 <b>لینک‌های دائمی فعال:</b> <code>{len(link_keys)}</code>\n"
            f"✅ <b>کاربران تاییدشده:</b> <code>{auth_users}</code>\n"
            f"🌐 <b>تعداد پروکسی‌ها:</b> <code>{proxy_count}</code>\n"
            f"♾ <b>وضعیت انقضای لینک‌ها:</b> دائمی (بدون انقضا)\n"
            f"🤖 <b>وضعیت ربات:</b> {status}"
        )
        await query.edit_message_text(text, reply_markup=get_admin_keyboard(), parse_mode='HTML')
        
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
            except Exception: pass
        
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
        asyncio.create_task(process_refresh_and_revive_all(context.bot, user_id, acc_keys))

    elif data == "admin_confirm_delete_dead":
        dead_phones = await redis_client.smembers("temp:unrecoverable_accounts")
        if not dead_phones:
            await query.edit_message_text("⚠️ لیست اکانت‌های غیرقابل بازگشت خالی است یا قبلاً حذف شده‌اند.", reply_markup=get_admin_keyboard())
            return

        deleted_count = 0
        for phone in dead_phones:
            await redis_client.delete(f"account:{phone}")
            active_url = await redis_client.get(f"phone_active_link:{phone}")
            if active_url and "/acc/" in active_url:
                lid = active_url.split("/acc/")[-1].strip()
                await redis_client.delete(f"acc_link:{lid}")
            await redis_client.delete(f"phone_active_link:{phone}")
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

    elif data == "admin_zip_to_link":
        context.user_data['admin_zip_action'] = 'zip_to_link'
        await context.bot.send_message(chat_id=user_id, text="🔗 <b>عملیات استخراج لینک دائمی:</b>\nلطفاً فایل ZIP مربوطه را ارسال کنید.", parse_mode='HTML')
        
    elif data == "admin_zip_discount":
        context.user_data['admin_zip_action'] = 'zip_discount_check'
        await context.bot.send_message(chat_id=user_id, text="🔍 <b>عملیات بررسی تخفیف:</b>\nلطفاً فایل ZIP مربوطه را ارسال کنید.", parse_mode='HTML')

    elif data == "admin_export":
        acc_keys = await redis_client.keys("account:*")
        if not acc_keys:
            await context.bot.send_message(chat_id=user_id, text="⚠️ دیتابیس سیستم خالی است.")
            return
        export_text = "لیست شماره‌های ثبت شده در سیستم:\n\n"
        for key in acc_keys: export_text += f"{key.replace('account:', '')}\n"
        
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
                origins = data_json.get("origins", [])
                if origins:
                    for item in origins[0].get("localStorage", []):
                        if item.get("name") == "user":
                            user_obj = json.loads(urllib.parse.unquote(item.get("value")))
                            phone = user_obj.get("mobilePhone", "نامشخص")
                            break
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
        await context.bot.send_message(chat_id=user_id, text="⏳ در حال استخراج توکن‌ها...")
        exported_data = {}
        for key in acc_keys:
            phone = key.replace('account:', '')
            tokens = await redis_client.hgetall(key)
            exported_data[phone] = {
                "access_token": tokens.get("access_token", ""),
                "refresh_token": tokens.get("refresh_token", "")
            }
        json_data = json.dumps(exported_data, indent=4, ensure_ascii=False)
        file_out = io.BytesIO(json_data.encode('utf-8'))
        await context.bot.send_document(chat_id=user_id, document=file_out, filename=f"Tokens_DB_{int(time.time())}.json", caption=f"🔑 فایل توکن‌های استخراج شده ({len(acc_keys)} شماره)")

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
# سیستم هندل کردن ورودی متنی / فایلی ادمین (پروکسی و تفکیک تخفیف)
# ==========================================
async def handle_admin_text_document(update: Update, context: ContextTypes.DEFAULT_TYPE):
    user_id = update.effective_user.id
    if not is_admin(user_id): return
    
    state = context.user_data.get('admin_state')
    if not state:
        return

    # ۱. دریافت و ذخیره پروکسی‌ها
    if state == 'waiting_for_proxy':
        msg = await update.message.reply_text("⏳ در حال خواندن پروکسی‌ها...")
        
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
                
            proxies = []
            for line in text_content.split('\n'):
                line = line.strip()
                if line:
                    if not line.startswith('http') and not line.startswith('socks'):
                        line = f"http://{line}"
                    proxies.append(line)
                    
            if proxies:
                await redis_client.set("settings:proxies", json.dumps(proxies))
                context.user_data['admin_state'] = None
                await msg.edit_text(f"✅ تعداد <b>{len(proxies)}</b> پروکسی با موفقیت ذخیره و تنظیم شد.", reply_markup=get_admin_keyboard(), parse_mode='HTML')
            else:
                await msg.edit_text("⚠️ متنی حاوی پروکسی یافت نشد. لطفاً مجدداً امتحان کنید.")
                
        except Exception as e:
            logging.error(f"Error reading proxies: {e}")
            await msg.edit_text("❌ خطا در پردازش فایل یا متن پروکسی.")

    # ۲. تفکیک فایل گزارش تخفیف بر اساس مبلغ
    elif state == 'waiting_for_discount_split':
        msg = await update.message.reply_text("⏳ در حال پردازش و تفکیک لینک‌ها بر اساس مبلغ تخفیف...")

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

            output_lines = [f"📂 لیست تفکیک‌شده لینک‌های تخفیف (مجموع: {total_links} لینک)\n" + "=" * 50 + "\n"]
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
                f"🔢 <b>مجموع لینک‌ها:</b> <code>{total_links}</code>\n"
                + "\n".join(summary_lines)
            )

            context.user_data['admin_state'] = None
            await msg.delete()
            await context.bot.send_document(
                chat_id=user_id,
                document=file_out,
                filename=f"Categorized_Discounts_{ts}.txt",
                caption=caption_text,
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
        if update.message: await update.message.reply_text(text)
        else: await update.callback_query.message.reply_text(text)
        return True
    return False

async def start_login_process(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_user_authorized(update.effective_user.id):
        await show_main_menu(update, context)
        return ConversationHandler.END
    if await check_maintenance(update): return ConversationHandler.END
    await update.callback_query.answer()
    
    keys_to_clear = ['device_id', 'session_id', 'correlation_id', 'user_agent', 'session_proxy', 'phone', 'auth_data', 'admin_state', 'admin_zip_action']
    for k in keys_to_clear:
        context.user_data.pop(k, None)
        
    kb = InlineKeyboardMarkup([[InlineKeyboardButton("❌ کنسل عملیات", callback_data="cancel_action")]])
    await update.callback_query.edit_message_text("📱 <b>لطفاً شماره موبایل خود را وارد کنید:</b>", reply_markup=kb, parse_mode='HTML')
    return PHONE

async def request_otp(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    if not await is_user_authorized(update.effective_user.id):
        await show_main_menu(update, context)
        return ConversationHandler.END
    if await check_maintenance(update): return ConversationHandler.END
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
            await query.edit_message_text(f"✉️ <b>کد تایید با مسیر جدید مجدداً ارسال شد.</b>\nکد را وارد کنید:", reply_markup=kb, parse_mode='HTML')
        else:
            await query.edit_message_text(f"❌ خطا در ارسال مجدد. گزارش سرور در پیام بالا ارسال شد.", reply_markup=kb, parse_mode='HTML')
    except Exception as e:
        await send_step_log(context.bot, query.message.chat_id, f"خطای شبکه در ارسال مجدد ({phone})", "EXCEPTION", str(e), proxy_dict)
        await query.edit_message_text("❌ خطا در اتصال به سرور هنگام ارسال مجدد.", reply_markup=InlineKeyboardMarkup([[InlineKeyboardButton("❌ کنسل", callback_data="cancel_action")]]))
        
    return OTP 

async def verify_otp_and_check_name(update: Update, context: ContextTypes.DEFAULT_TYPE) -> int:
    otp_code = clean_digits(update.message.text)
    phone = context.user_data.get('phone')
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
            
            # ۱. اکانت خام است -> ثبت نام خودکار و ساخت لینک دائمی
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
                
            # ۲. اکانت از قبل نام دارد -> استعلام سوابق سفارش
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
    phone = context.user_data.get('phone', 'نامشخص')
    injection_json = format_for_injector(auth_data)
    link_id = str(uuid.uuid4())[:12]
    
    # ذخیره دائمی بدون زمان انقضا
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
            CallbackQueryHandler(fallback_global_callback, pattern="^admin_|^auth_|^request_bot_access$|^main_menu$\vert{}^admin_panel$|^finish_link_creation$\vert{}^my_tags$|^show_tag_")
        ]
    )
    application.add_handler(conv_handler)
    
    application.add_handler(CommandHandler('start', show_main_menu))
    application.add_handler(CommandHandler('admin', admin_command))
    
    application.add_handler(MessageHandler(filters.Document.FileExtension("zip"), handle_zip_upload))
    application.add_handler(CallbackQueryHandler(core_callback, pattern="^admin_|^auth_|^request_bot_access$|^main_menu$\vert{}^admin_panel$|^finish_link_creation$\vert{}^my_tags$|^show_tag_"))
    application.add_handler(MessageHandler((filters.TEXT & ~filters.COMMAND) | filters.Document.FileExtension("txt"), handle_admin_text_document))

    await application.initialize()
    await application.start()
    await application.updater.start_polling()
    
    logging.info("System initialized successfully.")
    stop_signal = asyncio.Event()
    await stop_signal.wait()

if __name__ == '__main__':
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        pass
