import os
import re
import sys
import json
import time
import uuid
import socket
import random
import struct
import asyncio
import logging
import itertools
import threading
from datetime import datetime
from urllib.parse import unquote
from typing import Dict, List, Optional, Tuple, Any

import httpx
from flask import Flask, request, jsonify, send_file
from google_play_scraper import app as play_scraper
from protobuf_decoder.protobuf_decoder import Parser
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from Pb2 import MajoRLoGinrEs_pb2, MajoRLoGinrEq_pb2, PorTs_pb2

try:
    from message_ids import MESSAGE_ID_TO_NAME
except Exception:
    MESSAGE_ID_TO_NAME = {
        1: "UDP_HELLO",
        2: "UDP_ACK",
        3: "UDP_PING",
        101: "RUDP_JOIN_MATCH",
    }

try:
    import thunderFF_pb2
except Exception:
    thunderFF_pb2 = None

DEV_NAME = "JAGWAR x STRAVEX"
START_TIME = time.time()

logging.basicConfig(format='%(asctime)s - %(levelname)s - %(message)s', level=logging.INFO)
log = logging.getLogger("jagwar")

AES_KEY = b'Yg&tc%DEuh6%Zc^8'
AES_IV = b'6oyZDr22E3ychjM%'

REGION_LANG = {
    "BD": "bn", "IND": "hi", "PK": "ur", "SG": "en", "ID": "id",
    "ME": "ar", "VN": "vi", "TW": "zh", "CIS": "ru", "TH": "th",
    "EU": "en", "US": "en", "SAC": "es", "LK": "en", "BR": "pt",
    "RU": "ru", "NA": "en"
}

DEFAULT_HEADERS = {
    'User-Agent': 'UnityPlayer/2018.4.12f1 (UnityWebRequest/1.0, libcurl/8.5.0-DEV)',
    'Connection': 'Keep-Alive',
    'Accept-Encoding': 'gzip',
    'Content-Type': 'application/x-www-form-urlencoded',
    'Expect': '100-continue',
    'X-Unity-Version': '2018.4.12f1',
    'X-GA-SV': '1789535859',
    'X-GA': 'v1 1',
    'ReleaseVersion': 'OB55',
}

# ==================== LEVEL-UP & MATCH CONSTANTS ====================
TOKEN_CACHE_FILE = "token_cache.json"
DEVICES_FILE = "devices.json"
TOKEN_CACHE_TTL = 1200

START_MATCH_INTERVAL = 3.0
NEW_MATCH_DELAY = 3.0
MAX_MATCH_DURATION = 700
MATCH_IDLE_TIMEOUT = 8.0
PRIORITY_REGIONS = ["BD", "IND", "SG", "TH", "PH", "VN", "MY", "ID", "HK", "TW"]
MAX_CONSECUTIVE_PARSE_FAILURES = 5
NON_MATCH_RECONNECT_DELAY = 1.0

CLOUDFLARE_PRIMARY_DNS = "1.1.1.1"
CLOUDFLARE_SECONDARY_DNS = "1.0.0.1"
_DNS_CACHE: Dict[str, Tuple[str, float]] = {}
_DNS_CACHE_TTL = 300.0

CRC7_TABLE = bytes([
    0, 9, 18, 27, 36, 45, 54, 63, 72, 65, 90, 83, 108, 101, 126, 119,
    25, 16, 11, 2, 61, 52, 47, 38, 81, 88, 67, 74, 117, 124, 103, 110,
    50, 59, 32, 41, 22, 31, 4, 13, 122, 115, 104, 97, 94, 87, 76, 69,
    43, 34, 57, 48, 15, 6, 29, 20, 99, 106, 113, 120, 71, 78, 85, 92,
    100, 109, 118, 127, 64, 73, 82, 91, 44, 37, 62, 55, 8, 1, 26, 19,
    125, 116, 111, 102, 89, 80, 75, 66, 53, 60, 39, 46, 17, 24, 3, 10,
    86, 95, 68, 77, 114, 123, 96, 105, 30, 23, 12, 5, 58, 51, 40, 33,
    79, 70, 93, 84, 107, 98, 121, 112, 7, 14, 21, 28, 35, 42, 49, 56,
    65, 72, 83, 90, 101, 108, 119, 126, 9, 0, 27, 18, 45, 36, 63, 54,
    88, 81, 74, 67, 124, 117, 110, 103, 16, 25, 2, 11, 52, 61, 38, 47,
    115, 122, 97, 104, 87, 94, 69, 76, 59, 50, 41, 32, 31, 22, 13, 4,
    106, 99, 120, 113, 78, 71, 92, 85, 34, 43, 48, 57, 6, 15, 20, 29,
    37, 44, 55, 62, 1, 8, 19, 26, 109, 100, 127, 118, 73, 64, 91, 82,
    60, 53, 46, 39, 24, 17, 10, 3, 116, 125, 102, 111, 80, 89, 66, 75,
    23, 30, 5, 12, 51, 58, 33, 40, 95, 86, 77, 68, 123, 114, 105, 96,
    14, 7, 28, 21, 42, 35, 56, 49, 70, 79, 84, 93, 98, 107, 112, 121,
])

_DELTA = 0x9E3779B9
_ROUNDS = 16
_FIELD_SIZES = {0: 1, 1: 2, 2: 2, 3: 1, 4: 2}
_FIELD_NAMES = {0: "sendOption", 1: "cmd", 2: "orderId", 3: "flags", 4: "length"}

ui_logs = []
ui_logs_lock = threading.Lock()
matches_started_total = 0
matches_completed_total = 0
all_paused_flag = False


def push_log(message, level="info"):
    ts = datetime.now().strftime("%H:%M:%S")
    entry = {"time": ts, "level": level, "message": str(message)}
    with ui_logs_lock:
        ui_logs.append(entry)
        if len(ui_logs) > 500:
            del ui_logs[:-500]
    if level == "error":
        log.error(message)
    elif level == "warning":
        log.warning(message)
    else:
        log.info(message)


# ==================== PERSISTENT DEVICE & TOKEN CACHE ====================
def get_device_for_account(account_identifier: str) -> dict:
    devices = {}
    if os.path.exists(DEVICES_FILE):
        try:
            with open(DEVICES_FILE, "r", encoding="utf-8") as f:
                devices = json.load(f)
        except Exception:
            pass

    acc_key = str(account_identifier)
    if acc_key in devices:
        return devices[acc_key]

    device_list = [
        ("Samsung", "SM-G998B", "Adreno (TM) 660", "Android OS 12 / API-31"),
        ("Xiaomi", "2201122G", "Adreno (TM) 730", "Android OS 13 / API-33"),
        ("Realme", "RMX3700", "Mali-G710", "Android OS 14 / API-34"),
        ("OnePlus", "CPH2451", "Adreno (TM) 740", "Android OS 13 / API-33"),
        ("OPPO", "CPH2611", "Adreno (TM) 720", "Android OS 14 / API-34"),
        ("Vivo", "V2203", "Mali-G710", "Android OS 12 / API-31"),
        ("Poco", "M2102J20SG", "Adreno (TM) 660", "Android OS 13 / API-33"),
    ]
    brand, model, gpu, os_ver = random.choice(device_list)

    new_device = {
        "unique_device_id": f"Google|{str(uuid.uuid4())}",
        "brand": brand,
        "model": model,
        "gpu_renderer": gpu,
        "system_software": os_ver,
        "screen_width": random.choice([1080, 1440, 720, 1280]),
        "screen_height": random.choice([2400, 3200, 1600, 2400]),
        "screen_dpi": str(random.randint(300, 420)),
        "memory": random.randint(2800, 6500),
        "processor_details": f"ARM64 FP ASIMD AES VMH | {random.randint(2200, 3200)} | {random.randint(6, 12)}",
        "client_ip": f"{random.randint(103, 223)}.{random.randint(10, 250)}.{random.randint(10, 250)}.{random.randint(10, 250)}"
    }
    devices[acc_key] = new_device
    try:
        with open(DEVICES_FILE, "w", encoding="utf-8") as f:
            json.dump(devices, f, indent=4)
    except Exception as e:
        push_log(f"Failed to save device mapping: {e}", "error")
    return new_device


_token_cache_memo: Dict[str, Any] = {}
_token_cache_memo_time: float = 0.0
_TOKEN_CACHE_MEMO_TTL = 5.0


def _json_serializer(obj):
    if isinstance(obj, (bytes, bytearray)):
        return {"__bytes_hex__": bytes(obj).hex()}
    raise TypeError(f"Type {type(obj)} not serializable")


def _json_deserializer(obj):
    if isinstance(obj, dict):
        if "__bytes_hex__" in obj and len(obj) == 1:
            try:
                return bytes.fromhex(obj["__bytes_hex__"])
            except Exception:
                return b""
        return {k: _json_deserializer(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_json_deserializer(x) for x in obj]
    return obj


def _load_token_cache() -> Dict[str, Any]:
    global _token_cache_memo, _token_cache_memo_time
    now = time.time()
    if _token_cache_memo and (now - _token_cache_memo_time) < _TOKEN_CACHE_MEMO_TTL:
        return _token_cache_memo
    if not os.path.exists(TOKEN_CACHE_FILE):
        return {}
    try:
        with open(TOKEN_CACHE_FILE, "r", encoding="utf-8") as f:
            content = f.read().strip()
        if not content:
            return {}
        data = json.loads(content)
        parsed = _json_deserializer(data)
        _token_cache_memo = parsed
        _token_cache_memo_time = now
        return parsed
    except Exception:
        return {}


def _save_token_cache(cache: Dict[str, Any]):
    global _token_cache_memo, _token_cache_memo_time
    try:
        tmp_file = TOKEN_CACHE_FILE + ".tmp"
        with open(tmp_file, "w", encoding="utf-8") as f:
            json.dump(cache, f, indent=2, default=_json_serializer)
        os.replace(tmp_file, TOKEN_CACHE_FILE)
        _token_cache_memo = cache
        _token_cache_memo_time = time.time()
    except Exception as e:
        push_log(f"Token cache save error: {e}", "error")


def cache_get(uid: str) -> Optional[Dict]:
    cache = _load_token_cache()
    entry = cache.get(str(uid))
    if not entry:
        return None
    if time.time() - entry.get("cached_at", 0) > TOKEN_CACHE_TTL:
        cache_invalidate(uid)
        return None
    return entry


def cache_set(uid: str, account_data: Dict):
    cache = _load_token_cache()
    entry = dict(account_data)
    entry["cached_at"] = time.time()
    cache[str(uid)] = entry
    _save_token_cache(cache)


def cache_invalidate(uid: str):
    cache = _load_token_cache()
    if str(uid) in cache:
        del cache[str(uid)]
        _save_token_cache(cache)


# ==================== DNS & SOCKET OPTIMIZERS ====================
async def resolve_host_cloudflare(hostname: str) -> str:
    if not hostname:
        return hostname
    parts = hostname.split('.')
    if len(parts) == 4 and all(p.isdigit() and 0 <= int(p) <= 255 for p in parts):
        return hostname

    now = time.time()
    if hostname in _DNS_CACHE:
        ip, exp = _DNS_CACHE[hostname]
        if now < exp:
            return ip

    def _query_cloudflare(server_ip: str) -> Optional[str]:
        s = None
        try:
            tx_id = random.randint(1000, 65535)
            header = struct.pack(">HHHHHH", tx_id, 0x0100, 1, 0, 0, 0)
            qname = b"".join(bytes([len(part)]) + part.encode('ascii') for part in hostname.split('.')) + b""
            query_pkt = header + qname + struct.pack(">HH", 1, 1)

            s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
            s.settimeout(1.2)
            s.sendto(query_pkt, (server_ip, 53))
            resp, _ = s.recvfrom(1024)

            if len(resp) >= 12:
                ancount = struct.unpack(">H", resp[6:8])[0]
                if ancount > 0:
                    offset = 12 + len(qname) + 4
                    for _ in range(ancount):
                        if offset >= len(resp):
                            break
                        if (resp[offset] & 0xC0) == 0xC0:
                            offset += 2
                        else:
                            while offset < len(resp) and resp[offset] != 0:
                                offset += 1 + resp[offset]
                            offset += 1
                        if offset + 10 > len(resp):
                            break
                        rtype, rclass, ttl, rdlen = struct.unpack(">HHIH", resp[offset:offset+10])
                        offset += 10
                        if rtype == 1 and rdlen == 4 and offset + 4 <= len(resp):
                            return socket.inet_ntoa(resp[offset:offset+4])
                        offset += rdlen
        except Exception:
            pass
        finally:
            if s:
                try:
                    s.close()
                except Exception:
                    pass
        return None

    loop = asyncio.get_running_loop()
    ip = await loop.run_in_executor(None, _query_cloudflare, CLOUDFLARE_PRIMARY_DNS)
    if not ip:
        ip = await loop.run_in_executor(None, _query_cloudflare, CLOUDFLARE_SECONDARY_DNS)
    if not ip:
        try:
            ip_info = await loop.getaddrinfo(hostname, None, family=socket.AF_INET)
            if ip_info:
                ip = ip_info[0][4][0]
        except Exception:
            ip = hostname

    if ip:
        _DNS_CACHE[hostname] = (ip, now + _DNS_CACHE_TTL)
    return ip or hostname


def optimize_tcp_socket(sock: socket.socket):
    try:
        sock.setsockopt(socket.IPPROTO_TCP, socket.TCP_NODELAY, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_KEEPALIVE, 1)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 65536)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 65536)
    except Exception:
        pass


def optimize_udp_socket(sock: socket.socket):
    try:
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_RCVBUF, 131072)
        sock.setsockopt(socket.SOL_SOCKET, socket.SO_SNDBUF, 131072)
        if hasattr(socket, 'SIO_UDP_CONNRESET') and os.name == 'nt':
            try:
                sock.ioctl(socket.SIO_UDP_CONNRESET, False)
            except Exception:
                pass
    except Exception:
        pass


# ==================== PACKET & CRYPTO HELPERS ====================
async def has_ssan_zig(n):
    z = (n << 1) & 0xFFFFFFFFFFFFFFFF
    out = bytearray()
    while z >= 0x80:
        out.append((z & 0x7F) | 0x80)
        z >>= 7
    out.append(z)
    return bytes(out)


async def uleb_encode(n):
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


async def tea_enc(v0, v1, k0, k1, k2, k3):
    s = 0
    for _ in range(_ROUNDS):
        s = (s + _DELTA) & 0xFFFFFFFF
        v0 = (v0 + (((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF ^
                      ((v1 + s) & 0xFFFFFFFF) ^
                      (((v1 >> 5) + k1) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        v1 = (v1 + (((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF ^
                      ((v0 + s) & 0xFFFFFFFF) ^
                      (((v0 >> 5) + k3) & 0xFFFFFFFF)))) & 0xFFFFFFFF
    return v0, v1


async def tea_dec(v0, v1, k0, k1, k2, k3):
    s = (_DELTA * _ROUNDS) & 0xFFFFFFFF
    for _ in range(_ROUNDS):
        v1 = (v1 - (((((v0 << 4) & 0xFFFFFFFF) + k2) & 0xFFFFFFFF ^
                      ((v0 + s) & 0xFFFFFFFF) ^
                      (((v0 >> 5) + k3) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        v0 = (v0 - (((((v1 << 4) & 0xFFFFFFFF) + k0) & 0xFFFFFFFF ^
                      ((v1 + s) & 0xFFFFFFFF) ^
                      (((v1 >> 5) + k1) & 0xFFFFFFFF)))) & 0xFFFFFFFF
        s = (s - _DELTA) & 0xFFFFFFFF
    return v0, v1


async def tea_cbc_encrypt(padded, key_bytes):
    k0, k1, k2, k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(padded))
    prev_cipher = bytearray(8)
    prev_intermediate = bytearray(8)
    for i in range(0, len(padded), 8):
        xored = bytearray(8)
        for j in range(8):
            xored[j] = padded[i + j] ^ prev_cipher[j]
        e0, e1 = await tea_enc(
            struct.unpack_from("<I", xored, 0)[0],
            struct.unpack_from("<I", xored, 4)[0],
            k0, k1, k2, k3,
        )
        enc = bytearray(8)
        struct.pack_into("<I", enc, 0, e0)
        struct.pack_into("<I", enc, 4, e1)
        for j in range(8):
            out[i + j] = enc[j] ^ prev_intermediate[j]
        prev_cipher[:] = out[i:i + 8]
        prev_intermediate[:] = xored
    return bytes(out)


async def tea_cbc_decrypt(body, key_bytes):
    k0, k1, k2, k3 = (struct.unpack_from("<I", key_bytes, o)[0] for o in (0, 4, 8, 12))
    out = bytearray(len(body))
    prev_intermediate = bytearray(8)
    prev_cipher = bytearray(8)
    xored = bytearray(8)
    dec = bytearray(8)
    for i in range(0, len(body), 8):
        for j in range(8):
            xored[j] = body[i + j] ^ prev_intermediate[j]
        d0, d1 = await tea_dec(
            struct.unpack_from("<I", xored, 0)[0],
            struct.unpack_from("<I", xored, 4)[0],
            k0, k1, k2, k3
        )
        struct.pack_into("<I", dec, 0, d0)
        struct.pack_into("<I", dec, 4, d1)
        for j in range(8):
            out[i + j] = dec[j] ^ prev_cipher[j]
        prev_cipher[:] = body[i:i + 8]
        prev_intermediate[:] = dec
    return bytes(out)


async def build_padded(content):
    pad_len = (8 - (len(content) + 10) % 8) % 8
    return bytes([pad_len, 0, 0]) + b"" * pad_len + content + b"" * 7


async def encode_header(layout, send_option, cmd, order_id, flags, length, k, v80):
    out = bytearray()
    for code in layout:
        value = {0: send_option, 1: cmd, 2: order_id, 3: flags, 4: length}[code]
        if _FIELD_SIZES[code] == 1:
            out.append((value & 0xFF) ^ k)
        else:
            v = ((value & 0xFFFF) ^ v80) & 0xFFFF
            out.append(v & 0xFF)
            out.append((v >> 8) & 0xFF)
    return bytes(out)


async def crc7_buff(crc, buf):
    c = crc & 0x7F
    for b in buf:
        c = CRC7_TABLE[((2 * (c & 0xFF)) ^ (b & 0xFF)) & 0xFF] & 0x7F
    return c & 0x7F


async def sv_frame(msg_key, layout, send_option, cmd, order_id, flags, content, key, encrypted=True):
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0]) + await encode_header(layout, send_option, cmd, order_id, flags, len(body), k, v80)
    packet = bytearray(hdr + body)
    packet[1] = await crc7_buff(0, bytes(packet[2:])) & 0x7F
    return bytes(packet)


async def build_match_startup_packets(token, udp_key, match_code, account_id, block_val,
                                      server_ip="", region="BD", client_version="1.132.6",
                                      client_version_code="2019121229", access_token=""):
    token = token.strip()
    udp_key = bytes.fromhex(udp_key)
    match_code = [int(ch) for ch in str(match_code).strip()]

    thunder_jwt = token[:660] if len(token) > 660 else token
    sharma_jwt = token[660:] if len(token) > 660 else ""
    encoded_thunder_jwt = thunder_jwt.encode() if isinstance(thunder_jwt, str) else thunder_jwt
    encoded_sharma_jwt = sharma_jwt.encode() if isinstance(sharma_jwt, str) else sharma_jwt

    garena420 = await has_ssan_zig(len(encoded_thunder_jwt)) + encoded_thunder_jwt

    reg = str(region).upper() if region else "BD"
    csoversea_block = bytes.fromhex(
        "ca0163736f7665727365612e7374726f6e67686f6c642e66726565666972656d6f62696c652e636f6d"
        "3b302e302e302e303b33342e3132362e37362e34353b33342e38372e3137372e31343b33342e38372e"
        "3137302e3233303b33352e3138352e3138332e35370000000000000100000000000000000000000001"
        "00000800000100000000000100a8a2d7bebd8d8bdf110200"
    )

    mid = bytes.fromhex('0000000001000102030101') + await has_ssan_zig(len(reg)) + reg.encode()
    mid += bytes.fromhex('0001030003000004')
    mid += await has_ssan_zig(len(client_version)) + client_version.encode()
    mid += await has_ssan_zig(len(client_version_code)) + client_version_code.encode()
    mid += csoversea_block

    clean_ip = server_ip.split(':')[0] if server_ip else "0.0.0.0"
    mid += await has_ssan_zig(len(clean_ip)) + clean_ip.encode()

    clean_acc_tok = access_token.strip() if access_token else ""
    if clean_acc_tok:
        mid += await has_ssan_zig(len(clean_acc_tok)) + clean_acc_tok.encode()

    mid += await has_ssan_zig(len(encoded_sharma_jwt)) + encoded_sharma_jwt

    tg_garena420 = (
        await uleb_encode(int(account_id)) +
        await uleb_encode(int(block_val)) +
        await uleb_encode(1) +
        await uleb_encode(43) +
        await uleb_encode(int(block_val)) +
        await uleb_encode(11) +
        mid
    )

    process = await sv_frame(0x5E, match_code, 2, 447, 0, 1, garena420, udp_key)
    loading = await sv_frame(0x5A, match_code, 2, 448, 1, 1, tg_garena420, udp_key)
    return process.hex(), loading.hex()


async def produce_xor_key(secret_key):
    k = secret_key[0] if secret_key and len(secret_key) > 0 else 10
    return k, ((k << 8) | k) & 0xFFFF


async def parse_layout(layout):
    if isinstance(layout, str):
        return [int(ch) for ch in layout.strip()]
    return list(layout)


async def build_hello_packet(text, key, layout):
    data = text.encode("utf-8")
    if len(data) > 25:
        raise ValueError(f"Text is too long ({len(data)} bytes)")
    content = b"" + data + b"" * (29 - 4 - len(data))
    k, v80 = await produce_xor_key(key)
    layout = await parse_layout(layout)
    padded = await build_padded(content)
    enc_body = await tea_cbc_encrypt(padded, key)
    header_bytes = await encode_header(layout, 1, 1, 0, 1, len(enc_body), k, v80)
    packet = bytearray([0x63, 0x00]) + header_bytes + enc_body
    packet[1] = await crc7_buff(0, packet[2:]) & 0x7F
    return bytes(packet).hex()


async def classify(frame):
    cmd = frame["cmd"]
    msg_name = MESSAGE_ID_TO_NAME.get(cmd, f"UNKNOWN_{cmd}")
    if msg_name == "UDP_HELLO":
        return "HELLO"
    if msg_name == "UDP_ACK":
        return "ACK"
    if msg_name == "UDP_PING":
        return "PING"
    if msg_name == "RUDP_JOIN_MATCH":
        return "JOIN_MATCH"
    if msg_name.startswith("RUDP_") or msg_name.startswith("UDP_"):
        return msg_name
    return "DATA"


async def build_packet(msg_key, layout, send_option, cmd, order_id, flags, content, key, encrypted=True):
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    body = await tea_cbc_encrypt(await build_padded(content), key) if encrypted else content
    hdr = bytearray([msg_key, 0])
    for code in layout:
        value = {0: send_option, 1: cmd, 2: order_id, 3: flags, 4: len(body)}[code]
        if _FIELD_SIZES[code] == 1:
            hdr.append((value & 0xFF) ^ k)
        else:
            v = ((value & 0xFFFF) ^ v80) & 0xFFFF
            hdr.append(v & 0xFF)
            hdr.append((v >> 8) & 0xFF)
    packet = bytearray(hdr + body)
    packet[1] = await crc7_buff(0, bytes(packet[2:])) & 0x7F
    return bytes(packet)


async def layouts_from_mask(mask):
    ru = [int(c) for c in str(mask).strip()]
    nr = [c for c in ru if c != 2]
    return ru, nr


async def reply_for(frame, key, mask, ack_key=0x68, ping_key=0x6D, hello_key=0x5B, ack_style="short"):
    ru, nr = await layouts_from_mask(mask)
    typ = await classify(frame)
    if typ == "HELLO":
        if ack_style == "echo":
            content = frame["content"] if frame["content"] else b""
            return typ, await build_packet(hello_key, nr, 1, 1, None, 1, content, key)
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"", key)
    if typ == "ACK":
        content = frame["content"] if frame["content"] else b""
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, content, key)
    if typ == "PING":
        c = frame["content"]
        counter = c[:4] if len(c) >= 4 else c
        return typ, await build_packet(ping_key, nr, 0, 3, None, 0, counter + b"", key, encrypted=False)
    if typ == "JOIN_MATCH":
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"", key)
    return typ, None


async def keepalive_ping(sock, ip, port, key_bytes, mask, stop_event):
    nr = (await layouts_from_mask(mask))[1]
    ping_keys = [0x66, 0x6D, 0x69, 0x6C, 0x6B, 0x6E, 0x6F, 0x70]
    loop = asyncio.get_running_loop()
    i = 0
    while not stop_event.is_set():
        pk = ping_keys[i % len(ping_keys)]
        counter = int(time.time() * 1000) & 0xFFFFFFFF
        pkt = await build_packet(pk, nr, 0, 3, None, 0, struct.pack("<I", counter) + b"", key_bytes, encrypted=False)
        try:
            await loop.sock_sendto(sock, pkt, (ip, port))
        except Exception:
            pass
        i += 1
        try:
            await asyncio.wait_for(stop_event.wait(), timeout=3.0)
        except asyncio.TimeoutError:
            pass


async def try_header(buf, layout, k, v80):
    off = 2
    out = {}
    for code in layout:
        size = _FIELD_SIZES[code]
        if off + size > len(buf):
            return None
        out[_FIELD_NAMES[code]] = (buf[off] ^ k) if size == 1 else ((buf[off] | (buf[off + 1] << 8)) ^ v80) & 0xFFFF
        off += size
    out["headerLen"] = off
    return out


async def oicq_unpad(padded):
    if not padded or len(padded) < 8:
        return None
    if not all(padded[-1 - i] == 0 for i in range(7)):
        return None
    pad_len = padded[0] & 0x07
    s = 3 + pad_len
    e = len(padded) - 7
    return padded[s:e] if s < e else b""


async def decode_packet(packet, key, mask=None):
    data = bytes(packet) if isinstance(packet, bytes) else bytes.fromhex(packet)
    if len(data) < 8:
        return None
    k = key[0]
    v80 = ((k << 8) | k) & 0xFFFF
    crc_ok = (data[1] & 0x7F) == await crc7_buff(0, data[2:])
    candidates = []
    if mask:
        ru, nr = await layouts_from_mask(mask)
        layouts = [("RUDP", ru), ("nonRUDP", nr)]
    else:
        layouts = [("RUDP", list(p)) for p in itertools.permutations([0, 1, 2, 3, 4])]
        layouts += [("nonRUDP", list(p)) for p in itertools.permutations([0, 1, 3, 4])]
    for kind, layout in layouts:
        f = await try_header(data, layout, k, v80)
        if not f or f["flags"] > 7 or f["sendOption"] > 7:
            continue
        if f["length"] != len(data) - f["headerLen"]:
            continue
        body = data[f["headerLen"]:f["headerLen"] + f["length"]]
        content = None
        padded = None
        if f["flags"] & 1:
            if len(body) < 8 or len(body) % 8 != 0:
                continue
            padded = await tea_cbc_decrypt(body, key)
            content = await oicq_unpad(padded)
            if content is None:
                continue
        else:
            content = body
        score = (1 if crc_ok else 0) + (1 if content is not None else 0)
        candidates.append({
            "kind": kind, "layout": layout, "headerLen": f["headerLen"],
            "msgKey": data[0], "cmd": f["cmd"], "flags": f["flags"],
            "sendOption": f["sendOption"], "orderId": f.get("orderId"),
            "length": f["length"], "content": content, "crcOk": crc_ok,
            "padded": padded, "score": score, "total": len(data),
        })
    if not candidates:
        return None
    candidates.sort(key=lambda c: (c["kind"] in ("RUDP", "nonRUDP"), c["score"]), reverse=True)
    return candidates[0]


async def send_keep_alive(region="BD"):
    reg = str(region).upper() if region else "BD"
    ka_hex = "0219" if reg == "BD" else ("0214" if reg == "IND" else "0215")
    return bytes.fromhex(ka_hex)


async def aes_encrypt(payload, key, iv):
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))


def build_ob55_online_auth(account_uid, token, kts, key, iv):
    enc_token = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(token.encode("utf-8"), 16))
    return (bytes.fromhex("830c") + int(account_uid).to_bytes(8, "big") +
            int(kts).to_bytes(4, "big") + len(enc_token).to_bytes(8, "big") + enc_token, enc_token)


# ==================== WORKING LOGIN FUNCTIONS (FROM WORKING OB55 CODE) ====================
def _pb_varint(n):
    if n < 0:
        n = (1 << 64) + n
    out = bytearray()
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        out.append(b)
        if not n:
            break
    return bytes(out)


def _pb_tag(f, w):
    return _pb_varint((f << 3) | w)


def _pb_field(f, v):
    if isinstance(v, bool):
        v = int(v)
    if isinstance(v, int):
        return _pb_tag(f, 0) + _pb_varint(v)
    if isinstance(v, str):
        d = v.encode('utf-8')
        return _pb_tag(f, 2) + _pb_varint(len(d)) + d
    if isinstance(v, (bytes, bytearray)):
        d = bytes(v)
        return _pb_tag(f, 2) + _pb_varint(len(d)) + d
    return b""


def get_proto_field(d, key, default=None):
    if not d or not isinstance(d, dict):
        return default
    if key in d:
        return d[key].get('data', default)
    if str(key) in d:
        return d[str(key)].get('data', default)
    return default


async def parse_results(parsed_results):
    result_dict = {}
    for result in parsed_results:
        fd = {"wire_type": result.wire_type}
        if result.wire_type in ("varint", "string", "bytes"):
            fd["data"] = result.data
        elif result.wire_type == "length_delimited":
            if hasattr(result.data, "results"):
                fd["data"] = await parse_results(result.data.results)
            elif isinstance(result.data, list):
                fd["data"] = await parse_results(result.data)
            else:
                fd["data"] = str(result.data)
        result_dict[str(result.field)] = fd
    return result_dict


_CACHED_APP_VERSION = None


async def get_playstore_version():
    global _CACHED_APP_VERSION
    if _CACHED_APP_VERSION:
        return _CACHED_APP_VERSION
    loop = asyncio.get_running_loop()
    try:
        res = await asyncio.wait_for(
            loop.run_in_executor(
                None, lambda: play_scraper('com.dts.freefireth', lang='hi', country='id')
            ),
            timeout=4.0
        )
        _CACHED_APP_VERSION = res.get("version", "1.134.21")
        return _CACHED_APP_VERSION
    except Exception:
        _CACHED_APP_VERSION = "1.134.21"
        return _CACHED_APP_VERSION


_CACHED_VER_CFG = {}


async def version_config(client_http, region="ME"):
    reg = (region or "ME").upper()
    if reg in _CACHED_VER_CFG:
        return _CACHED_VER_CFG[reg]
    app_version = await get_playstore_version()
    lang = REGION_LANG.get(reg, "hi")
    api_url = (
        f"https://version.ggwhitehawk.com/live/ver.php?version={app_version}"
        f"&lang={lang}&device=android&channel=android&appstore=googleplay"
        f"&region={reg}&whitelist_version=1.3.0&whitelist_sp_version=1.0.0"
    )
    try:
        res = await client_http.get(api_url)
        data = res.json()
        cfg = (
            data.get("latest_release_version") or DEFAULT_HEADERS["ReleaseVersion"],
            data.get("remote_version") or app_version,
            data.get("server_url"),
        )
        if cfg[2]:
            _CACHED_VER_CFG[reg] = cfg
        return cfg
    except Exception:
        return None


async def get_access_token(client_http, uid, password):
    url = "https://100067.connect.garena.com/oauth/guest/token/grant"
    hdrs = {
        "Host": "100067.connect.garena.com",
        "User-Agent": "Dalvik/2.1.0 (Linux; U; Android 12; SM-G998B Build/SP1A.210812.016)",
        "Content-Type": "application/x-www-form-urlencoded",
        "Accept-Encoding": "gzip, deflate, br",
        "Connection": "close",
    }
    data = {
        "uid": str(uid),
        "password": str(password),
        "response_type": "token",
        "client_type": "2",
        "client_secret": "2ee44819e9b4598845141067b281621874d0d5d7af9d8f7e00c1e54715b7d1e3",
        "client_id": "100067",
    }
    for _ in range(3):
        try:
            r = await client_http.post(url, headers=hdrs, data=data)
            if r.status_code == 200:
                rd = r.json()
                open_id = rd.get("open_id")
                access_token = rd.get("access_token")
                if open_id and access_token:
                    return open_id, access_token, rd.get("platform", 4)
        except Exception:
            pass
        await asyncio.sleep(0.4)
    return None


async def build_majorlogin_payload(open_id, access_token, platform,
                                   client_version="1.134.21", region="ME", field_29=None):
    try:
        reg = (region or "ME").upper()
        proto = MajoRLoGinrEq_pb2.MajorLogin()
        proto.event_time = str(datetime.now())[:-7]
        proto.game_name = "free fire"
        proto.platform_id = 1
        proto.client_version = str(client_version or "1.134.21")
        proto.client_version_code = "2019121269"
        proto.system_software = "Android OS 13 / API-33 (TP1A.220624.014/eng.compil.20241021.212130)"
        proto.system_hardware = "Handheld"
        proto.device_type = "Handheld"
        proto.screen_width = 1600
        proto.screen_height = 720
        proto.screen_dpi = "300"
        proto.processor_details = "ARM64 FP ASIMD AES | 2000 | 8"
        proto.memory = 3743
        proto.gpu_renderer = "Mali-G52 MC2"
        proto.gpu_version = "OpenGL ES 3.2 v1.r26p0-01eac0.455662e55e7c7fb95a4b1db7e7af49a8"
        proto.unique_device_id = f"Google|{uuid.uuid4()}"
        proto.client_ip = f"106.219.{random.randint(1, 254)}.{random.randint(1, 254)}"
        proto.language = REGION_LANG.get(reg, "en")
        proto.open_id = str(open_id)
        proto.open_id_type = "4"
        proto.login_open_id_type = 1
        proto.access_token = str(access_token)
        proto.login_by = 3
        proto.platform_sdk_id = 1
        proto.origin_platform_type = "4"
        proto.primary_platform_type = "4"
        proto.reg_avatar = 1
        proto.channel_type = 3
        proto.telecom_operator = "airtel"
        proto.network_operator_a = "airtel"
        proto.network_type = "CarrierDataNetwork"
        proto.network_type_a = "4G"
        proto.cpu_type = 2
        proto.cpu_architecture = "64"
        proto.graphics_api = "OpenGLES2"
        proto.supported_astc_bitset = 4095
        proto.client_using_version = "7428b253defc164018c604a1ebbfebdf"
        proto.loading_time = 12556
        proto.release_channel = "android"
        proto.extra_info = "KqsHTxpGP5CwXDeHDi75pVSLPfiEigAhx+8r/es0KD31a2hBp9ZPNH1uhy+PLLpXhGjqWkGqVhZqw2BMbIBV/Hevo9X80/1swZ0nzuG9Gs6qO6HA"
        proto.android_engine_init_flag = 111207
        proto.if_push = 1
        proto.is_vpn = 0
        proto.memory_available.version = 55
        proto.memory_available.hidden_value = 81
        proto.external_storage_total = 47738
        proto.external_storage_available = 8234
        proto.internal_storage_total = 3504
        proto.internal_storage_available = 8527
        proto.game_disk_storage_total = 47938
        proto.game_disk_storage_available = 8234
        proto.external_sdcard_total_storage = 47738
        proto.external_sdcard_avail_storage = 8234
        proto.library_path = "/data/app/~~AckKiWUMLxHKcTatBB0dBA==/com.garena.game.ffi-PyAatSWUVmz6XVRiHvB2GA==/lib/arm64"
        proto.library_token = "dd9d4c174e0472d34b7fd34bd5924bc9|/data/app/~~AckKiWUMLxHKcTatBB0dBA==/com.garena.game.ffi-PyAatSWUVmz6XVRiHvB2GA==/base.apk"
        base_payload = proto.SerializeToString()
        extra = b""
        extra += _pb_field(25, "vivo V2152")
        extra += _pb_field(26, reg)
        if field_29:
            extra += _pb_field(29, str(field_29))
        extra += _pb_field(96, '{"cur_rate":null,"support_etc2":false}')
        extra += _pb_field(99, "4")
        extra += _pb_field(100, "4")
        extra += _pb_field(102, "")
        extra += _pb_field(104, 98784)
        extra += _pb_field(105, 1)
        extra += _pb_field(106, "https://dl-tata.freefireind.in/live/ABHotUpdates/|https://core-tata.freefireind.in/live/ABHotUpdates/|ac2c27398b1d5d95a4b6b6e04fa94066")
        extra += _pb_field(107, "1.1686d744a88f55b9")
        return await aes_encrypt(base_payload + extra, AES_KEY, AES_IV)
    except Exception as e:
        log.error(f"build_majorlogin_payload: {e}")
        return None


async def send_majorlogin(client_http, data, release_version, server_url):
    try:
        url = f"{server_url}MajorLogin" if server_url.endswith('/') else f"{server_url}/MajorLogin"
        req_headers = DEFAULT_HEADERS.copy()
        req_headers["ReleaseVersion"] = str(release_version)
        response = await client_http.post(url, headers=req_headers, data=data)
        if response.status_code != 200 or len(response.content) < 40:
            log.warning(f"MajorLogin HTTP {response.status_code}")
            return None
        res_proto = MajoRLoGinrEs_pb2.MajorLoginRes()
        try:
            res_proto.ParseFromString(response.content)
        except Exception:
            pass
        if not (res_proto.account_uid and res_proto.token):
            for offset in range(min(128, len(response.content))):
                try:
                    c = MajoRLoGinrEs_pb2.MajorLoginRes()
                    c.ParseFromString(response.content[offset:])
                    if c.account_uid and c.token:
                        res_proto = c
                        break
                except Exception:
                    pass
        parsed = Parser().parse(response.content.hex())
        dict_res = await parse_results(parsed)
        key_val = get_proto_field(dict_res, 22) or res_proto.key or AES_KEY
        iv_val = get_proto_field(dict_res, 23) or res_proto.iv or AES_IV
        if isinstance(key_val, str):
            try:
                key_val = bytes.fromhex(key_val)
            except Exception:
                pass
        if isinstance(iv_val, str):
            try:
                iv_val = bytes.fromhex(iv_val)
            except Exception:
                pass
        res_proto.key = key_val
        res_proto.iv = iv_val
        if not res_proto.url:
            res_proto.url = server_url
        return res_proto
    except Exception as e:
        log.error(f"MajorLogin error: {e}")
        return None


async def send_getlogin(client_http, data, base_url, token, release_version):
    try:
        url = f"{base_url.rstrip('/')}/GetLoginData"
        req_headers = DEFAULT_HEADERS.copy()
        req_headers["ReleaseVersion"] = str(release_version)
        req_headers['Authorization'] = f"Bearer {token}"
        response = await client_http.post(url, headers=req_headers, data=data)
        if response.status_code != 200:
            return None
        res_proto = PorTs_pb2.GetLoginData()
        try:
            res_proto.ParseFromString(response.content)
        except Exception:
            pass
        parsed = Parser().parse(response.content.hex())
        dict_res = await parse_results(parsed)
        return res_proto, dict_res
    except Exception as e:
        log.error(f"GetLoginData error: {e}")
        return None


async def do_login(uid, password, region_pref="ME", token_override=None):
    async with httpx.AsyncClient(verify=False, timeout=15.0) as client_http:
        vc = await version_config(client_http, region_pref)
        if not vc:
            push_log(f"version_config failed for region {region_pref}", "error")
            return None
        release_version, client_version, server_url = vc
        if not server_url:
            push_log(f"version_config returned no server_url for {region_pref}", "error")
            return None
        if token_override:
            open_id = str(uid or "0")
            access_token = str(token_override).strip()
            platform = 4
        else:
            tg = await get_access_token(client_http, uid, password)
            if not tg:
                push_log(f"access_token failed for {uid}", "error")
                return None
            open_id, access_token, platform = tg
        payload = await build_majorlogin_payload(
            open_id, access_token, platform, client_version or "1.134.21", region_pref
        )
        if not payload:
            push_log("payload build failed", "error")
            return None
        major_res = await send_majorlogin(client_http, payload, release_version, server_url)
        if not major_res or not major_res.account_uid:
            push_log(f"MajorLogin rejected for {uid}", "error")
            return None
        gl = await send_getlogin(client_http, payload, major_res.url, major_res.token, release_version)
        if not gl:
            push_log(f"GetLoginData failed for {uid}", "error")
            return None
        res_proto, dict_res = gl
        online_addr = res_proto.Online_IP_Port or get_proto_field(dict_res, 14, "0.0.0.0:0")
        online_ip, online_port = online_addr.split(":") if ':' in online_addr else ("0.0.0.0", "0")
        chat_addr = res_proto.AccountIP_Port or get_proto_field(dict_res, 32, online_addr)
        chat_ip, chat_port = chat_addr.split(":") if ':' in chat_addr else (online_ip, online_port)
        level_val = get_proto_field(dict_res, 6) or get_proto_field(dict_res, 3) or 1
        exp_val = get_proto_field(dict_res, 7) or get_proto_field(dict_res, 21) or 0
        try:
            level_int = int(level_val)
        except Exception:
            level_int = 1
        try:
            exp_int = int(exp_val)
        except Exception:
            exp_int = 0
        get_device_for_account(str(uid))
        result_dict = {
            "auth_uid": str(uid),
            "bot_uid": str(major_res.account_uid),
            "access_token": access_token,
            "token": major_res.token,
            "region": major_res.region or region_pref,
            "key": major_res.key or AES_KEY,
            "iv": major_res.iv or AES_IV,
            "timestamp": major_res.timestamp or int(time.time()),
            "online_ip": online_ip,
            "online_port": online_port,
            "chat_ip": chat_ip,
            "chat_port": chat_port,
            "account_name": res_proto.AccountName or "Unknown",
            "clan_id": res_proto.Clan_ID or 0,
            "clan_data": res_proto.Clan_Compiled_Data or "",
            "server_url": major_res.url,
            "client_version": str(client_version or "1.134.21"),
            "level": level_int,
            "exp": exp_int,
            "login_data_raw": None,
        }
        cache_set(str(uid), result_dict)
        return result_dict


# ==================== LEVEL-UP UDP MATCH & LONE WOLF ENGINE ====================
async def start_game_lone_wolf(region, client_version, writer, key, iv):
    raw_pkt = bytes.fromhex(
        "080112800a0a010b102b3a110a044944433110aa011a064555524f50453a100a044944433210311a064555524f504540014a0801090a0b1219202758016291090a8001303838463832424630324139363736373032303130313030303030303030303030303136303030313030313530303032323246393745454530463030303030303436373632353134303030303030303030303030303030303030303030303030303030303030303030303030303066663030303030303030636163666131366410241afb02735d5e571400024a775d45414d1a041b1c001f11010449715f4243481a001e1d071c1703004b1a4066785c524570735c51486775421b5c5a4c07504042685a63610816054e19025e75196001477c015165406370195f5547404e4550640103020f1304064863754268676c755f65576e40467e5f0a417a4701026d675d6e73670b1108495a4c6a0b78470b740065645e525a057258425f584a447d4e6759440c11044e7c596d7f4b625f7d04055a47505c4e1d6b5b4107447d7201057d7f0f14084e430457674f7e517d72015172415d027473577c4d615f79535256780911030f4d5e027a797f614165067806505d53777750475e75064257076500460817014e741e7e5078487e7a7c465e7669767153497064605a7376677773550d160148037e18675966787f4c42607a645f577e7b441b460776026b18685d0b110205490060020f70676175654674706671797f41067346677c4e06585e780f15074c57047b40517075415f6364027259674b5b0166407f7340600407770a22047a5d5c52300b3a0a167305067162727516134208312e3133302e3232480350015ae90403626253513635686e556f4e36416456324b796f566c636f477776484f624e56526c4d727073504b4f43654177616848494176795556497273743752737149734a7a786b3247525268377a2f637664626d504f6a73552f79626d38547a4c69586d2f474351696d494b53486833447955726f39515152756c34545350626d6d624b7949565937545671577059455372323646572f59624578507338514f706d317372785455736c30796a434144444d4f34616a654b615753366361496c554b4963797a494e396d52516f715277687939797257476d337a644345337a6a61436f492f5a585233656f65365a42647a64677654636b6b665733356e4d4c6a6a565072564b6433523172756174394e50514150724a5546627859696c4c5a3859707336654d5447666b6649793574666a526c314d4648706b51774c6373374439656378566c41636f374e664f6d2b30654756466c4434744478706771385533595973587645384842502f70666c767a737138316a32524f4d7857437556445442492f684735625462773166456e4249725162762b636144775147696f74554e316d4c4b77734379456f4766706746614251457645672b736a764c4c78704743334c304a5344532f74526169504354553344374e6249306547516651622f5a466f4c36455630775a324d6f583932414c572f5049752f56634663584e70596b356f7966326151416a536971486a2f363276354843644f525551303578754e6171795251625653704654303137655237675255636b4966366c6f447476342b514e4a4670766d74757077707774396a5a5974437a4b56743657726d6e36785837706658456251555434684f3758a201050803108703a201050804108103a20105080510c001a20105081d10cc01a2010408161078a20105080e10af01a201020815"
    )
    if thunderFF_pb2 is not None and hasattr(thunderFF_pb2, "StartMatch"):
        try:
            proto = thunderFF_pb2.StartMatch()
            proto.ParseFromString(raw_pkt)
            if hasattr(proto.main, 'region_list') and len(proto.main.region_list) > 0:
                proto.main.region_list[0].region = region
                if len(proto.main.region_list) > 1:
                    proto.main.region_list[1].region = region
            if hasattr(proto.main, 'client_version'):
                proto.main.client_version.remote_version = client_version
            raw_pkt = proto.SerializeToString()
        except Exception:
            pass

    encrypted_packet = (await aes_encrypt(raw_pkt, key, iv)).hex()
    packet_length = len(encrypted_packet) // 2
    hex_length = hex(packet_length)[2:]
    hex_length = hex_length if len(hex_length) > 1 else "0" + hex_length
    final_packet = "031400" + "0" * (6 - len(hex_length)) + hex_length + encrypted_packet
    writer.write(bytes.fromhex(final_packet))
    await writer.drain()


async def play_game(bot_ref, server_ip_port, thunder, sharma, udp_key, match_code,
                    account_id, player_region, client_version, match_index: int):
    global matches_completed_total
    match_start_time = time.time()
    ping_task = None
    sock = None
    ping_stop = asyncio.Event()
    completed_cleanly = False

    try:
        ip, port = server_ip_port.split(":")
        port = int(port)
        resolved_ip = await resolve_host_cloudflare(ip)

        loop = asyncio.get_running_loop()
        sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
        optimize_udp_socket(sock)
        sock.setblocking(False)

        udp_key_bytes = bytes.fromhex(udp_key)
        hello_packet = await build_hello_packet(f"{account_id}_2585", udp_key_bytes, match_code)
        await loop.sock_sendto(sock, bytes.fromhex(hello_packet), (resolved_ip, port))

        ack_state = "waiting_for_hello_reply"
        thunder_sent = False
        sharma_sent = False
        join_match_received = False
        local_closed = False
        send_lock = asyncio.Lock()

        ping_task = asyncio.create_task(
            keepalive_ping(sock, resolved_ip, port, udp_key_bytes, match_code, ping_stop)
        )
        last_activity = time.time()
        MAX_IDLE_BEFORE_HELLO_RESEND = 7.0

        push_log(f"[MATCH #{match_index}] UDP started -> {server_ip_port} (DNS: {resolved_ip})", "info")

        async def send_thunder_sharma_inline():
            nonlocal ack_state, thunder_sent, sharma_sent
            if thunder_sent:
                return
            async with send_lock:
                if thunder_sent:
                    return
                try:
                    await loop.sock_sendto(sock, bytes.fromhex(thunder), (resolved_ip, port))
                    thunder_sent = True
                    await asyncio.sleep(0.1)
                    prepare_ack = await build_packet(
                        0x68, (await layouts_from_mask(match_code))[1],
                        0, 2, None, 1, b"\x01\x00", udp_key_bytes
                    )
                    await loop.sock_sendto(sock, prepare_ack, (resolved_ip, port))
                    await asyncio.sleep(0.2)
                    await loop.sock_sendto(sock, bytes.fromhex(sharma), (resolved_ip, port))
                    sharma_sent = True
                    ack_state = "thunder_sharma_sent"
                    push_log(f"[MATCH #{match_index}] Thunder+Sharma sent!", "success")
                except Exception as e:
                    push_log(f"[MATCH #{match_index}] send error: {e}", "error")

        while not local_closed and not bot_ref.closed:
            if time.time() - match_start_time > MAX_MATCH_DURATION:
                break
            try:
                response, server_addr = await asyncio.wait_for(
                    loop.sock_recvfrom(sock, 65535), timeout=1.5
                )
                if response:
                    last_activity = time.time()
                    frame = await decode_packet(response, udp_key_bytes, match_code)
                    if frame:
                        ptype = await classify(frame)

                        if frame['cmd'] in [103, 107]:
                            push_log(f"[MATCH #{match_index}] Completed (cmd {frame['cmd']})", "success")
                            completed_cleanly = True
                            local_closed = True
                            continue

                        if frame['cmd'] == 101:
                            try:
                                ack_pkt = await build_packet(
                                    0x68, (await layouts_from_mask(match_code))[1],
                                    0, 2, None, 1, b"\x01\x00", udp_key_bytes
                                )
                                await loop.sock_sendto(sock, ack_pkt, server_addr)
                            except Exception:
                                pass
                            continue

                        if ptype in ["ACK", "PING", "HELLO", "JOIN_MATCH"]:
                            if ptype == "HELLO" and ack_state == "waiting_for_hello_reply":
                                _, reply = await reply_for(
                                    frame, udp_key_bytes, match_code, ack_style="short"
                                )
                                if reply:
                                    await loop.sock_sendto(sock, reply, server_addr)
                                ack_state = "ack_sent_waiting"
                            elif ptype == "ACK":
                                if ack_state == "waiting_for_hello_reply":
                                    _, reply = await reply_for(frame, udp_key_bytes, match_code)
                                    if reply:
                                        await loop.sock_sendto(sock, reply, server_addr)
                                    ack_state = "ready_to_send_thunder"
                                elif ack_state == "ack_sent_waiting":
                                    ack_state = "ready_to_send_thunder"
                                else:
                                    _, reply = await reply_for(frame, udp_key_bytes, match_code)
                                    if reply:
                                        await loop.sock_sendto(sock, reply, server_addr)
                            elif ptype == "PING":
                                _, reply = await reply_for(frame, udp_key_bytes, match_code)
                                if reply:
                                    await loop.sock_sendto(sock, reply, server_addr)
                            elif ptype == "JOIN_MATCH" and not join_match_received:
                                _, reply = await reply_for(frame, udp_key_bytes, match_code)
                                if reply:
                                    await loop.sock_sendto(sock, reply, server_addr)
                                    join_match_received = True
            except asyncio.TimeoutError:
                if ack_state == "ready_to_send_thunder" and not thunder_sent:
                    await send_thunder_sharma_inline()
                elif ack_state == "waiting_for_hello_reply":
                    if (time.time() - last_activity) > MAX_IDLE_BEFORE_HELLO_RESEND:
                        try:
                            pkt = await build_hello_packet(
                                f"{account_id}_2585", udp_key_bytes, match_code
                            )
                            await loop.sock_sendto(sock, bytes.fromhex(pkt), (resolved_ip, port))
                        except Exception:
                            pass
                        last_activity = time.time()
                    if (time.time() - match_start_time) > 25.0:
                        push_log(f"[MATCH #{match_index}] Handshake timeout", "warning")
                        break
                elif ack_state == "thunder_sharma_sent":
                    if (time.time() - last_activity) > MATCH_IDLE_TIMEOUT:
                        push_log(f"[MATCH #{match_index}] Finished naturally", "success")
                        completed_cleanly = True
                        break
                continue
            except BlockingIOError:
                await asyncio.sleep(0.05)
            except OSError:
                await asyncio.sleep(0.5)
                continue
            except Exception:
                await asyncio.sleep(0.5)
                continue

            if ack_state == "ready_to_send_thunder" and not thunder_sent:
                await send_thunder_sharma_inline()

        return f"match #{match_index} finished"
    except Exception as e:
        push_log(f"[MATCH #{match_index}] error: {e}", "error")
        return f"match #{match_index} error"
    finally:
        if completed_cleanly:
            bot_ref.matches_completed += 1
            matches_completed_total += 1
            exp_gain = 100
            bot_ref.gained_exp += exp_gain
            bot_ref.current_exp += exp_gain
        ping_stop.set()
        if ping_task:
            ping_task.cancel()
            try:
                await ping_task
            except asyncio.CancelledError:
                pass
        if sock:
            try:
                sock.close()
            except Exception:
                pass
        bot_ref.active_matches = max(0, bot_ref.active_matches - 1)
        if not bot_ref.closed:
            bot_ref.status = "PAUSED" if bot_ref.is_paused else ("IN_MATCH" if bot_ref.active_matches > 0 else "ONLINE")


# ==================== LEVEL-UP BOT WORKER ====================
class LevelUpBot:
    def __init__(self, login, on_close=None):
        global matches_started_total
        self.login = login
        self.auth_uid = str(login.get("auth_uid") or login["bot_uid"])
        self.uid = int(login["bot_uid"])
        self.token = login["token"]
        self.access_token = login.get("access_token") or ""
        self.key, self.iv = login["key"], login["iv"]
        self.ts = int(login["timestamp"])
        self.region = (login.get("region") or "ME")
        self.client_version = str(login.get("client_version") or "1.134.21")
        self.name = login.get("account_name") or "Bot"
        self.level = int(login.get("level") or 1)
        self.initial_exp = int(login.get("exp") or 0)
        self.current_exp = int(login.get("exp") or 0)
        self.gained_exp = 0
        self.matches_started = 0
        self.matches_completed = 0
        self.active_matches = 0
        self.status = "ONLINE"
        self.is_paused = False
        self.connected_at = time.time()
        self.paused_elapsed = 0.0
        self._pause_started_at = None
        self.on_close = on_close
        self.online_r = self.online_w = None
        self._online_buf = bytearray()
        self._play_matches: List[asyncio.Task] = []
        self._tasks: List[asyncio.Task] = []
        self.closed = False
        self.levelup_enabled = True
        self._last_start_time = 0.0
        self._search_attempts = 0
        self._consecutive_parse_failures = 0

    def _spawn(self, coro):
        t = asyncio.create_task(coro)
        self._tasks.append(t)
        return t

    @property
    def uptime_seconds(self):
        if self.is_paused and self._pause_started_at is not None:
            return max(0.0, self._pause_started_at - self.connected_at - self.paused_elapsed)
        return max(0.0, time.time() - self.connected_at - self.paused_elapsed)

    def pause(self):
        if not self.is_paused:
            self.is_paused = True
            self._pause_started_at = time.time()
            self.status = "PAUSED"

    def resume(self):
        if self.is_paused:
            if self._pause_started_at is not None:
                self.paused_elapsed += max(0.0, time.time() - self._pause_started_at)
                self._pause_started_at = None
            self.is_paused = False
            if not self.closed:
                self.status = "IN_MATCH" if self.active_matches > 0 else "ONLINE"

    def to_dict(self):
        return {
            "uid": str(self.uid),
            "auth_uid": str(self.auth_uid),
            "nickname": self.name,
            "region": self.region,
            "level": self.level,
            "initial_exp": self.initial_exp,
            "current_exp": self.current_exp,
            "gained_exp": self.gained_exp,
            "matches_started": self.matches_started,
            "matches_completed": self.matches_completed,
            "status": "PAUSED" if self.is_paused else self.status,
            "is_paused": self.is_paused,
            "active_matches": self.active_matches,
            "uptime_seconds": int(self.uptime_seconds),
        }

    async def connect(self):
        r = self.login
        resolved_ip = await resolve_host_cloudflare(r["online_ip"])
        self.online_r, self.online_w = await asyncio.wait_for(
            asyncio.open_connection(resolved_ip, int(r["online_port"])), 10
        )
        raw_sock = self.online_w.get_extra_info('socket')
        if raw_sock:
            optimize_tcp_socket(raw_sock)

        auth, _ = build_ob55_online_auth(self.uid, self.token, self.ts, self.key, self.iv)
        self.online_w.write(auth)
        await self.online_w.drain()

        try:
            init_ka = await send_keep_alive(self.region)
            if init_ka and self.online_w and not self.online_w.is_closing():
                self.online_w.write(init_ka)
                await asyncio.wait_for(self.online_w.drain(), timeout=3)
        except Exception:
            pass

        self._spawn(self._online_read_loop())
        self._spawn(self._keepalive(self.online_w))
        self._spawn(self._levelup_match_loop())
        self.status = "PAUSED" if self.is_paused else "ONLINE"

    async def _keepalive(self, writer):
        try:
            while not self.closed and not writer.is_closing():
                await asyncio.sleep(5)
                try:
                    ka = await send_keep_alive(self.region)
                    writer.write(ka)
                    await writer.drain()
                except Exception:
                    break
        except asyncio.CancelledError:
            pass

    async def trigger_start_match(self, region="BD"):
        global matches_started_total
        if self.closed or self.is_paused or not self.levelup_enabled:
            return False
        if not self.online_w or self.online_w.is_closing():
            return False
        self._search_attempts += 1
        target_reg = (region or "BD").upper()
        await asyncio.sleep(random.uniform(0.25, 0.55))
        await start_game_lone_wolf(
            target_reg, self.client_version, self.online_w, self.key, self.iv
        )
        self._last_start_time = asyncio.get_running_loop().time()
        matches_started_total += 1
        if not self.is_paused:
            self.status = "SEARCHING" if self.active_matches == 0 else "IN_MATCH"
        return True

    async def _levelup_match_loop(self):
        try:
            await asyncio.sleep(0.5)
            while not self.closed:
                self._play_matches[:] = [m for m in self._play_matches if not m.done()]
                if self.levelup_enabled and not self.is_paused:
                    now = asyncio.get_running_loop().time()
                    if now - self._last_start_time >= START_MATCH_INTERVAL:
                        await self.trigger_start_match("BD")
                await asyncio.sleep(0.5)
        except asyncio.CancelledError:
            pass

    async def _online_read_loop(self):
        try:
            while not self.closed:
                data = await asyncio.wait_for(self.online_r.read(8192), timeout=40.0)
                if not data:
                    break
                hex_data = data.hex()
                packet_length = len(data)

                if hex_data.startswith("0300") and 10 < packet_length < 30:
                    push_log(f"[{self.name}] Match starting, please wait...", "info")
                    continue

                if hex_data.startswith("0300") and packet_length >= 300:
                    push_log(f"[{self.name}] MATCH FOUND! Loading UDP match...", "success")
                    try:
                        parsed = Parser().parse(hex_data[10:])
                        res = await parse_results(parsed)
                        token = None
                        udp_key = None
                        match_code = None
                        server_ip_port = None
                        match_account_id = None
                        block_val = None

                        if '42' in res and 'data' in res['42']:
                            match_code = res['42']['data']
                        if '5' in res and 'data' in res['5']:
                            res_field5 = res['5']['data']
                            server_ip_port = res_field5.get('2', {}).get('data')
                            udp_key = res_field5.get('3', {}).get('data')
                            token = res_field5.get('4', {}).get('data')
                            if '42' in res_field5:
                                match_code = res_field5['42']['data']
                        if '1' in res and 'data' in res['1']:
                            match_account_id = res['1']['data']
                        if '5' in res and 'data' in res['5']:
                            block_val = res['5']['data'].get('1', {}).get('data')

                        effective_acc_id = match_account_id or self.uid
                        if token and udp_key and match_code and server_ip_port:
                            thunder, sharma = await build_match_startup_packets(
                                token, udp_key, match_code, effective_acc_id, block_val or 0,
                                server_ip=server_ip_port,
                                region=self.region,
                                client_version=self.client_version,
                                access_token=self.access_token
                            )
                            self.active_matches += 1
                            self.matches_started += 1
                            if not self.is_paused:
                                self.status = "IN_MATCH"
                            match_idx = self.matches_started
                            task = asyncio.create_task(
                                play_game(
                                    self,
                                    server_ip_port,
                                    thunder,
                                    sharma,
                                    udp_key,
                                    match_code,
                                    effective_acc_id,
                                    "BD",
                                    self.client_version,
                                    match_index=match_idx
                                )
                            )
                            self._play_matches.append(task)
                            self._consecutive_parse_failures = 0
                            await asyncio.sleep(NEW_MATCH_DELAY)
                        else:
                            self._consecutive_parse_failures += 1
                            if self._consecutive_parse_failures >= MAX_CONSECUTIVE_PARSE_FAILURES:
                                cache_invalidate(self.auth_uid)
                                self._consecutive_parse_failures = 0
                            await asyncio.sleep(NON_MATCH_RECONNECT_DELAY)
                    except Exception as e:
                        push_log(f"[{self.name}] Match packet parse error: {e}", "warning")
                        self._consecutive_parse_failures += 1
                        await asyncio.sleep(NON_MATCH_RECONNECT_DELAY)
        except asyncio.CancelledError:
            return
        except Exception as e:
            push_log(f"online loop ({self.uid}): {e}", "warning")
        await self.close()

    async def close(self):
        if self.closed:
            return
        self.closed = True
        self.active_matches = 0
        self.status = "PAUSED" if self.is_paused else "OFFLINE"
        for m in self._play_matches:
            if not m.done():
                m.cancel()
        if self.online_w:
            try:
                self.online_w.close()
            except Exception:
                pass
        me = asyncio.current_task()
        for t in self._tasks:
            if t is not me and not t.done():
                t.cancel()
        if self.on_close:
            try:
                self.on_close(self)
            except Exception:
                pass


class AsyncLoop:
    def __init__(self):
        self.loop = asyncio.new_event_loop()
        self.thread = threading.Thread(target=self._run, daemon=True)
        self.thread.start()

    def _run(self):
        asyncio.set_event_loop(self.loop)
        self.loop.run_forever()

    def run(self, coro, timeout=30):
        return asyncio.run_coroutine_threadsafe(coro, self.loop).result(timeout=timeout)

    def start_background(self, coro):
        return asyncio.run_coroutine_threadsafe(coro, self.loop)


async_loop = AsyncLoop()


def _accs_file_path():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    for candidate in ("accs.txt", os.path.join(base_dir, "accs.txt")):
        if os.path.exists(candidate):
            return candidate
    return os.path.join(base_dir, "accs.txt")


def append_account_to_file(uid, password):
    path = _accs_file_path()
    line = f"{str(uid).strip()}:{str(password).strip()}\n"
    existing = []
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            existing = [l.strip() for l in f if l.strip()]
    uid_prefix = f"{str(uid).strip()}:"
    if not any(l.startswith(uid_prefix) for l in existing):
        with open(path, "a", encoding="utf-8") as f:
            f.write(line)


def remove_account_from_file(uid, auth_uid=""):
    path = _accs_file_path()
    if not os.path.exists(path):
        return
    targets = {str(uid).strip()}
    if auth_uid:
        targets.add(str(auth_uid).strip())
    with open(path, "r", encoding="utf-8") as f:
        lines = f.readlines()
    kept = []
    for l in lines:
        s = l.strip()
        if not s or ":" not in s:
            kept.append(l)
            continue
        left = s.split(":", 1)[0].strip()
        if left not in targets:
            kept.append(l)
    with open(path, "w", encoding="utf-8") as f:
        f.writelines(kept)


class AccountPool:
    def __init__(self, concurrency=12):
        self.accounts: List[LevelUpBot] = []
        self.credentials = {}
        self.lock = asyncio.Lock()
        self.current_index = 0
        self.loading = False
        self.loaded = False
        self.concurrency = concurrency

    async def connect_single(self, uid, password, region="ME", token_override=None, persist=True):
        uid_s = str(uid).strip()
        pass_s = str(password or "").strip()
        reg_s = (region or "ME").upper()
        if persist and uid_s and pass_s and not token_override:
            self.credentials[uid_s] = (pass_s, reg_s)
            append_account_to_file(uid_s, pass_s)

        login = await do_login(uid_s, pass_s, reg_s, token_override=token_override)
        if not login:
            return None

        bot = LevelUpBot(login)
        bot.is_paused = all_paused_flag
        if bot.is_paused:
            bot.status = "PAUSED"
        await bot.connect()
        self.credentials[str(bot.uid)] = (pass_s, reg_s)
        self.credentials[uid_s] = (pass_s, reg_s)

        async with self.lock:
            self.accounts = [a for a in self.accounts if a.uid != bot.uid and str(a.auth_uid) != uid_s]
            self.accounts.append(bot)

        push_log(f"Account {uid_s} ({bot.name}) connected for Level-Up", "success")
        return bot

    async def load_and_connect(self):
        if self.loading or self.loaded:
            return
        self.loading = True
        path = _accs_file_path()
        if not os.path.exists(path):
            push_log("accs.txt not found", "warning")
            self.loading = False
            self.loaded = True
            return
        with open(path, "r", encoding="utf-8") as f:
            lines = [l.strip() for l in f if ":" in l]
        push_log(f"Loaded {len(lines)} accounts from accs.txt", "info")

        sem = asyncio.Semaphore(self.concurrency)

        async def _worker(line):
            async with sem:
                uid, password = line.split(":", 1)
                uid, password = uid.strip(), password.strip()
                try:
                    await self.connect_single(uid, password, "ME", persist=False)
                except Exception as e:
                    push_log(f"Account {uid} error: {e}", "error")

        await asyncio.gather(*[_worker(line) for line in lines], return_exceptions=True)
        self.loading = False
        self.loaded = True

    async def find_bot(self, uid):
        u = str(uid).strip()
        async with self.lock:
            for a in self.accounts:
                if str(a.uid) == u or str(a.auth_uid) == u:
                    return a
        return None

    async def remove_bot(self, uid, auth_uid=""):
        targets = {str(uid).strip()}
        if auth_uid:
            targets.add(str(auth_uid).strip())
        to_close = []
        async with self.lock:
            kept = []
            for a in self.accounts:
                if str(a.uid) in targets or str(a.auth_uid) in targets:
                    to_close.append(a)
                else:
                    kept.append(a)
            self.accounts = kept
        for k in targets:
            self.credentials.pop(k, None)
            cache_invalidate(k)
        remove_account_from_file(uid, auth_uid)
        for b in to_close:
            await b.close()
        push_log(f"Removed account {uid}", "warning")

    async def refresh_bot(self, uid):
        bot = await self.find_bot(uid)
        if not bot:
            return False, "Account not found"
        cred = self.credentials.get(str(bot.uid)) or self.credentials.get(str(bot.auth_uid))
        if not cred:
            return False, "No saved credentials for refresh"
        pw, reg = cred
        cache_invalidate(bot.auth_uid)
        await bot.close()
        reconnected = await self.connect_single(bot.auth_uid, pw, reg, persist=False)
        return (True, "Refreshed") if reconnected else (False, "Reconnect failed")

    async def restart_bot(self, uid):
        return await self.refresh_bot(uid)

    async def toggle_pause_bot(self, uid):
        bot = await self.find_bot(uid)
        if not bot:
            return False, False, "Account not found"
        if bot.is_paused:
            bot.resume()
            push_log(f"Resumed account {bot.uid}", "info")
            return True, False, "Resumed"
        bot.pause()
        push_log(f"Paused account {bot.uid}", "info")
        return True, True, "Paused"

    async def toggle_pause_all(self):
        global all_paused_flag
        async with self.lock:
            if not self.accounts:
                all_paused_flag = not all_paused_flag
                return all_paused_flag
            any_active = any(not a.is_paused for a in self.accounts)
            if any_active:
                for a in self.accounts:
                    a.pause()
                all_paused_flag = True
                push_log("All accounts paused", "warning")
            else:
                for a in self.accounts:
                    a.resume()
                all_paused_flag = False
                push_log("All accounts resumed", "success")
            return all_paused_flag


account_pool = AccountPool(concurrency=12)


class LevelUpManager:
    def __init__(self, pool: AccountPool):
        self.pool = pool
        self.auto_levelup_enabled = True
        self.lock = asyncio.Lock()

    async def start_levelup_all(self, region="BD"):
        async with self.lock:
            active = [b for b in self.pool.accounts if not b.closed and not b.is_paused]
            if not active:
                return {
                    "ok": False,
                    "error": "No active connected accounts available",
                    "started_count": 0,
                }
            started = 0
            for bot in active:
                bot.levelup_enabled = True
                if await bot.trigger_start_match(region=region):
                    started += 1
            push_log(f"Level-Up triggered on {started}/{len(active)} accounts (region: {region})", "success")
            return {
                "ok": True,
                "started_count": started,
                "total_active": len(active),
                "region": region,
            }

    async def toggle_auto(self, enabled=None):
        if enabled is None:
            self.auto_levelup_enabled = not self.auto_levelup_enabled
        else:
            self.auto_levelup_enabled = bool(enabled)
        for bot in self.pool.accounts:
            bot.levelup_enabled = self.auto_levelup_enabled
        push_log(f"Auto Level-Up: {'ENABLED' if self.auto_levelup_enabled else 'DISABLED'}", "info")
        return self.auto_levelup_enabled


levelup_manager = LevelUpManager(account_pool)


async def _create_levelup_accounts_worker(region, clan_id, count, password):
    push_log(f"Creating {count} guest accounts for Level-Up in {region} (Clan: {clan_id})...", "info")
    created = 0
    for _ in range(count):
        guest_uid = str(random.randint(3000000000, 4999999999))
        bot = await account_pool.connect_single(guest_uid, password, region, persist=True)
        if bot:
            created += 1
        await asyncio.sleep(0.4)
    push_log(f"Level-Up account creation finished: {created}/{count} in {region}", "success" if created else "warning")


app = Flask(__name__)
async_loop.start_background(account_pool.load_and_connect())


@app.route("/", methods=["GET"])
def index():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    html_path = os.path.join(base_dir, "index.html")
    if os.path.exists(html_path):
        return send_file(html_path)
    return jsonify({"status": "online", "mode": "level_up", "DEV": DEV_NAME}), 200


@app.route("/status_json", methods=["GET"])
@app.route("/status", methods=["GET"])
def status_route():
    return jsonify({
        "status": "online",
        "mode": "level_up",
        "accounts_loaded": len(account_pool.accounts),
        "loading": account_pool.loading,
        "auto_levelup_enabled": levelup_manager.auto_levelup_enabled,
        "DEV": DEV_NAME
    }), 200


@app.route("/api/stats", methods=["GET"])
def api_stats():
    accs = [a.to_dict() for a in account_pool.accounts]
    total_gained = sum(int(a.get("gained_exp") or 0) for a in accs)
    total_started = matches_started_total or sum(int(a.matches_started or 0) for a in account_pool.accounts)
    total_done = matches_completed_total or sum(int(a.matches_completed or 0) for a in account_pool.accounts)
    total_active = sum(int(a.get("active_matches") or 0) for a in accs)
    uptime_sec = max(1.0, time.time() - START_TIME)
    exp_per_hour = int(round((total_gained / uptime_sec) * 3600))
    with ui_logs_lock:
        logs_copy = list(ui_logs)
    return jsonify({
        "ok": True,
        "mode": "level_up",
        "total_accounts": len(accs),
        "total_matches_started": total_started,
        "total_matches": total_done,
        "total_gained_exp": total_gained,
        "total_active_matches": total_active,
        "exp_per_hour": exp_per_hour,
        "uptime": int(uptime_sec),
        "accounts": accs,
        "logs": logs_copy,
        "auto_levelup_enabled": levelup_manager.auto_levelup_enabled,
        "DEV": DEV_NAME,
    }), 200


@app.route("/api/account/add", methods=["POST"])
def api_account_add():
    body = request.get_json(silent=True) or {}
    token = str(body.get("token") or "").strip()
    uid = str(body.get("uid") or "").strip()
    password = str(body.get("password") or "").strip()
    region = str(body.get("region") or "ME").upper().strip()

    if token:
        acc_id = uid or str(random.randint(1000000000, 9999999999))
        bot = async_loop.run(account_pool.connect_single(acc_id, "", region, token_override=token, persist=False))
    else:
        if not uid or not password:
            return jsonify({"status": "error", "error": "UID and password are required"}), 400
        bot = async_loop.run(account_pool.connect_single(uid, password, region, persist=True))

    if not bot:
        return jsonify({"status": "error", "error": "Failed to login or connect account"}), 400
    return jsonify({"status": "ok", "uid": str(bot.uid), "nickname": bot.name}), 200


@app.route("/api/account/delete", methods=["POST"])
def api_account_delete():
    body = request.get_json(silent=True) or {}
    uid = str(body.get("uid") or "").strip()
    auth_uid = str(body.get("auth_uid") or "").strip()
    if not uid and not auth_uid:
        return jsonify({"status": "error", "error": "UID required"}), 400
    async_loop.run(account_pool.remove_bot(uid, auth_uid))
    return jsonify({"status": "ok"}), 200


@app.route("/api/account/refresh", methods=["POST"])
def api_account_refresh():
    body = request.get_json(silent=True) or {}
    uid = str(body.get("uid") or "").strip()
    if not uid:
        return jsonify({"status": "error", "error": "UID required"}), 400
    ok, msg = async_loop.run(account_pool.refresh_bot(uid))
    return jsonify({"status": "ok" if ok else "error", "message": msg, "error": None if ok else msg}), (200 if ok else 400)


@app.route("/api/account/restart", methods=["POST"])
def api_account_restart():
    body = request.get_json(silent=True) or {}
    uid = str(body.get("uid") or "").strip()
    if not uid:
        return jsonify({"status": "error", "error": "UID required"}), 400
    ok, msg = async_loop.run(account_pool.restart_bot(uid))
    return jsonify({"status": "ok" if ok else "error", "message": msg, "error": None if ok else msg}), (200 if ok else 400)


@app.route("/api/account/pause", methods=["POST"])
def api_account_pause():
    body = request.get_json(silent=True) or {}
    uid = str(body.get("uid") or "").strip()
    if not uid:
        return jsonify({"status": "error", "error": "UID required"}), 400
    ok, is_paused, msg = async_loop.run(account_pool.toggle_pause_bot(uid))
    if not ok:
        return jsonify({"status": "error", "error": msg}), 404
    return jsonify({"status": "ok", "is_paused": is_paused, "message": msg}), 200


@app.route("/api/account/pause_all", methods=["POST"])
def api_account_pause_all():
    all_p = async_loop.run(account_pool.toggle_pause_all())
    return jsonify({"status": "ok", "all_paused": all_p}), 200


@app.route("/api/create_team", methods=["POST"])
def api_create_team():
    body = request.get_json(silent=True) or {}
    region = str(body.get("region") or "ME").upper().strip()
    clan_id = str(body.get("clan_id") or "").strip()
    count = max(1, min(10, int(body.get("count") or 4)))
    password = str(body.get("password") or "RAFIN TxT").strip() or "RAFIN TxT"
    if not clan_id:
        return jsonify({"ok": False, "error": "Clan ID is required"}), 400
    async_loop.start_background(_create_levelup_accounts_worker(region, clan_id, count, password))
    return jsonify({"ok": True, "message": f"Started creating {count} accounts in {region}"}), 200


@app.route("/api/levelup/start", methods=["POST"])
def api_levelup_start():
    body = request.get_json(silent=True) or {}
    region = str(body.get("region") or "BD").upper().strip()
    res = async_loop.run(levelup_manager.start_levelup_all(region=region))
    return jsonify(res), (200 if res.get("ok") else 400)


@app.route("/api/levelup/toggle", methods=["POST"])
def api_levelup_toggle():
    body = request.get_json(silent=True) or {}
    enabled = body.get("enabled")
    state = async_loop.run(levelup_manager.toggle_auto(enabled=enabled))
    return jsonify({"ok": True, "auto_levelup_enabled": state}), 200


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 10000))
    app.run(host="0.0.0.0", port=port, threaded=True)
