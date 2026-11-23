import os
import re
import sys
import json
import time
import uuid
import socket
import struct
import asyncio
import logging
import threading
import itertools
from datetime import datetime
from urllib.parse import unquote

import httpx
from flask import Flask, request, jsonify, send_file
from google_play_scraper import app as play_scraper
from protobuf_decoder.protobuf_decoder import Parser
from Crypto.Cipher import AES
from Crypto.Util.Padding import pad, unpad
from Pb2 import MajoRLoGinrEs_pb2, MajoRLoGinrEq_pb2, PorTs_pb2
try:
    import thunderFF_pb2
except Exception:
    thunderFF_pb2 = None
try:
    from message_ids import MESSAGE_ID_TO_NAME
except Exception:
    MESSAGE_ID_TO_NAME = {}

DEV_NAME = "JAGWAR x STRAVEX"
START_TIME = time.time()

logging.basicConfig(format='%(asctime)s - %(levelname)s - %(message)s', level=logging.INFO)
log = logging.getLogger("jagwar")

AES_KEY = b'Yg&tc%DEuh6%Zc^8'
AES_IV = b'6oyZDr22E3ychjM%'

# Level-Up / Solo Match configuration & constants extracted from Level-Up code
START_MATCH_INTERVAL = 3.0
NEW_MATCH_DELAY = 3.0
MAX_MATCH_DURATION = 700
MATCH_IDLE_TIMEOUT = 8.0
PRIORITY_REGIONS = ["BD", "IND", "SG", "TH", "PH", "VN", "MY", "ID", "HK", "TW"]
MAX_CONSECUTIVE_PARSE_FAILURES = 5.0
NON_MATCH_RECONNECT_DELAY = 1.0

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

# ==================== CLOUDFLARE DNS & SOCKET OPTIMIZERS (FROM LEVEL-UP) ====================
CLOUDFLARE_PRIMARY_DNS = "1.1.1.1"
CLOUDFLARE_SECONDARY_DNS = "1.0.0.1"
_DNS_CACHE = {}
_DNS_CACHE_TTL = 300.0


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

    def _query_cloudflare(server_ip: str):
        s = None
        try:
            tx_id = random.randint(1000, 65535)
            header = struct.pack(">HHHHHH", tx_id, 0x0100, 1, 0, 0, 0)
            qname = b"".join(bytes([len(part)]) + part.encode('ascii') for part in hostname.split('.')) + b"\x00"
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


# ==================== LEVEL-UP UDP / TEA / PROTOBUF MATCH HELPERS ====================
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
    return bytes([pad_len, 0, 0]) + b"\x00" * pad_len + content + b"\x00" * 7


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
                                      server_ip="", region="BD", client_version="1.134.21",
                                      client_version_code="2019121269", access_token=""):
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
    content = b"\x10\x00\x00\x00" + data + b"\x00" * (29 - 4 - len(data))
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
            content = frame["content"] if frame["content"] else b"\x10\x00\x00\x00"
            return typ, await build_packet(hello_key, nr, 1, 1, None, 1, content, key)
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x01\x00", key)
    if typ == "ACK":
        content = frame["content"] if frame["content"] else b"\x01\x00"
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, content, key)
    if typ == "PING":
        c = frame["content"]
        counter = c[:4] if len(c) >= 4 else c
        return typ, await build_packet(ping_key, nr, 0, 3, None, 0, counter + b"\x00\x00\x00", key, encrypted=False)
    if typ == "JOIN_MATCH":
        return typ, await build_packet(ack_key, nr, 0, 2, None, 1, b"\x02\x00", key)
    return typ, None


async def keepalive_ping(sock, ip, port, key_bytes, mask, stop_event):
    nr = (await layouts_from_mask(mask))[1]
    ping_keys = [0x66, 0x6D, 0x69, 0x6C, 0x6B, 0x6E, 0x6F, 0x70]
    loop = asyncio.get_running_loop()
    i = 0
    while not stop_event.is_set():
        pk = ping_keys[i % len(ping_keys)]
        counter = int(time.time() * 1000) & 0xFFFFFFFF
        pkt = await build_packet(pk, nr, 0, 3, None, 0, struct.pack("<I", counter) + b"\x00\x00\x00", key_bytes, encrypted=False)
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
        if not f:
            continue
        if f["flags"] > 7 or f["sendOption"] > 7:
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


async def start_solo_match_packet(region, client_version, writer, key, iv):
    """Sends solo match start packet directly for a single account without forming a squad."""
    base_hex = (
        "080112800a0a010b102b3a110a044944433110aa011a064555524f50453a100a044944433210311a064555524f504540014a0801090a0b1219202758016291090a80013038384638324246303241393637363730323031303130303030303030303030303031363030303130303135303030323232463937454545304630303030303034363736323531343030303030303030303030303030303030303030303030303030303030303030303030303066663030303030303030636163666131366410241afb02735d5e571400024a775d45414d1a041b1c001f11010449715f4243481a001e1d071c1703004b1a4066785c524570735c51486775421b5c5a4c07504042685a63610816054e19025e75196001477c015165406370195f5547404e4550640103020f1304064863754268676c755f65576e40467e5f0a417a4701026d675d6e73670b1108495a4c6a0b78470b740065645e525a057258425f584a447d4e6759440c11044e7c596d7f4b625f7d04055a47505c4e1d6b5b4107447d7201057d7f0f14084e430457674f7e517d72015172415d027473577c4d615f79535256780911030f4d5e027a797f614165067806505d53777750475e75064257076500460817014e741e7e5078487e7a7c465e7669767153497064605a7376677773550d160148037e18675966787f4c42607a645f577e7b441b460776026b18685d0b110205490060020f70676175654674706671797f41067346677c4e06585e780f15074c57047b40517075415f6364027259674b5b0166407f7340600407770a22047a5d5c52300b3a0a167305067162727516134208312e3133302e3232480350015ae90403626253513635686e556f4e36416456324b796f566c636f477776484f624e56526c4d727073504b4f43654177616848494176795556497273743752737149734a7a786b3247525268377a2f637664626d504f6a73552f79626d38547a4c69586d2f474351696d494b53486833447955726f39515152756c34545350626d6d624b7949565937545671577059455372323646572f59624578507338514f706d317372785455736c30796a434144444d4f34616a654b615753366361496c554b4963797a494e396d52516f715277687939797257476d337a644345337a6a61436f492f5a585233656f65365a42647a64677654636b6b665733356e4d4c6a6a565072564b6433523172756174394e50514150724a5546627859696c4c5a3859707336654d5447666b6649793574666a526c314d4648706b51774c6373374439656378566c41636f374e664f6d2b30654756466c4434744478706771385533595973587645384842502f70666c767a737138316a32524f4d7857437556445442492f684735625462773166456e4249725162762b636144775147696f74554e316d4c4b77734379456f4766706746614251457645672b736a764c4c78704743334c304a5344532f74526169504354553344374e6249306547516651622f5a466f4c36455630775a324d6f583932414c572f5049752f56634663584e70596b356f7966326151416a536971486a2f363276354843644f525551303578754e6171795251625653704654303137655237675255636b4966366c6f447476342b514e4a4670766d74757077707774396a5a5974437a4b56743657726d6e36785837706658456251555434684f3758a201050803108703a201050804108103a20105080510c001a20105081d10cc01a2010408161078a20105080e10af01a201020815"
    )
    raw_bytes = bytes.fromhex(base_hex)
    if thunderFF_pb2 is not None and hasattr(thunderFF_pb2, "StartMatch"):
        try:
            proto = thunderFF_pb2.StartMatch()
            proto.ParseFromString(raw_bytes)
            if hasattr(proto.main, 'region_list') and len(proto.main.region_list) > 0:
                proto.main.region_list[0].region = region
                if len(proto.main.region_list) > 1:
                    proto.main.region_list[1].region = region
            if hasattr(proto.main, 'client_version'):
                proto.main.client_version.remote_version = client_version
            raw_bytes = proto.SerializeToString()
        except Exception:
            pass

    enc_hex = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(raw_bytes, AES.block_size)).hex()
    pkt_len = len(enc_hex) // 2
    hex_len = hex(pkt_len)[2:]
    if len(hex_len) < 2:
        hex_len = "0" + hex_len
    final_hex = "031400" + "0" * (6 - len(hex_len)) + hex_len + enc_hex
    writer.write(bytes.fromhex(final_hex))
    await writer.drain()


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


def HELLXenc_packet(payload, key, iv):
    raw = bytes.fromhex(payload) if isinstance(payload, str) else bytes(payload)
    if isinstance(key, str):
        key = bytes.fromhex(key)
    if isinstance(iv, str):
        iv = bytes.fromhex(iv)
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(raw, 16)).hex()


def HELLXdec_packet(payload, key, iv):
    raw = bytes.fromhex(payload) if isinstance(payload, str) else bytes(payload)
    if isinstance(key, str):
        key = bytes.fromhex(key)
    if isinstance(iv, str):
        iv = bytes.fromhex(iv)
    return unpad(AES.new(key, AES.MODE_CBC, iv).decrypt(raw), 16).hex()


def HELLXenc_varint(n):
    if n < 0:
        return b''
    h = []
    while True:
        b = n & 0x7F
        n >>= 7
        if n:
            b |= 0x80
        h.append(b)
        if not n:
            break
    return bytes(h)


def HELLXdec_varint(data, pos):
    res, shift = 0, 0
    while pos < len(data):
        b = data[pos]
        res |= (b & 0x7F) << shift
        pos += 1
        if not (b & 0x80):
            return res, pos
        shift += 7
    return 0, pos


def HELLXcreate_variant(f, v):
    return HELLXenc_varint((f << 3) | 0) + HELLXenc_varint(v)


def HELLXcreate_length(f, v):
    ev = v.encode('utf-8') if isinstance(v, str) else v
    return HELLXenc_varint((f << 3) | 2) + HELLXenc_varint(len(ev)) + ev


def HELLXcreate_proto(fields):
    packet = bytearray()
    for f, v in fields.items():
        if isinstance(v, list):
            for it in v:
                if isinstance(it, dict):
                    packet.extend(HELLXcreate_length(f, HELLXcreate_proto(it)))
                elif isinstance(it, int):
                    packet.extend(HELLXcreate_variant(f, it))
                elif isinstance(it, (str, bytes)):
                    packet.extend(HELLXcreate_length(f, it))
        elif isinstance(v, dict):
            packet.extend(HELLXcreate_length(f, HELLXcreate_proto(v)))
        elif isinstance(v, int):
            packet.extend(HELLXcreate_variant(f, v))
        elif isinstance(v, (str, bytes)):
            packet.extend(HELLXcreate_length(f, v))
    return bytes(packet)


def HELLXdecode_proto(data):
    res_d, pos = {}, 0
    while pos < len(data):
        try:
            tag, pos = HELLXdec_varint(data, pos)
            if tag == 0:
                break
            fn, wt = tag >> 3, tag & 0x07
            key, val = str(fn), None
            if wt == 0:
                val, pos = HELLXdec_varint(data, pos)
            elif wt == 1:
                val = data[pos:pos + 8].hex()
                pos += 8
            elif wt == 2:
                length, pos = HELLXdec_varint(data, pos)
                chunk = data[pos:pos + length]
                pos += length
                try:
                    s = chunk.decode('utf-8')
                    if all(32 <= ord(c) <= 126 or ord(c) > 160 for c in s):
                        val = s.strip()
                    else:
                        raise Exception
                except Exception:
                    inner = HELLXdecode_proto(chunk)
                    val = inner if inner else chunk.hex()
            elif wt == 5:
                val = data[pos:pos + 4].hex()
                pos += 4
            else:
                pos += 1
                continue
            if val is not None:
                if key in res_d:
                    if not isinstance(res_d[key], list):
                        res_d[key] = [res_d[key]]
                    res_d[key].append(val)
                else:
                    res_d[key] = val
        except Exception:
            break
    return res_d


def HELLXgenerate_packet(proto_hex, opcode, key, iv):
    ep = HELLXenc_packet(proto_hex, key, iv)
    lh = hex(len(ep) // 2)[2:].zfill(2)
    if len(lh) == 2:
        header = opcode + "000000" + lh
    elif len(lh) == 3:
        header = opcode + "00000" + lh
    elif len(lh) == 4:
        header = opcode + "0000" + lh
    elif len(lh) == 5:
        header = opcode + "000" + lh
    else:
        header = opcode + lh
    return bytes.fromhex(header + ep)


def HELLXbuild_auth_startup(uid, token, timestamp, key, iv):
    uid_hex = hex(int(uid))[2:]
    ul = len(uid_hex)
    f = str(hex(timestamp))[2:]
    if len(f) == 1:
        f = "0" + f
    enc_tok = HELLXenc_packet(token.encode().hex(), key, iv)
    len_hex = hex(len(enc_tok) // 2)[2:].zfill(4)
    headers = {9: '0000000', 8: '00000000', 10: '000000', 7: '000000000'}.get(ul, '0000000')
    return f"0115{headers}{uid_hex}{f}0000{len_hex}{enc_tok}"


def HELLXbuild_chat_auth(uid, region_id, key, iv):
    fields = {1: 3, 2: {1: int(uid), 3: 'en', 4: str(region_id)}}
    return HELLXgenerate_packet(HELLXcreate_proto(fields).hex(), '1215', key, iv)


def get_randm_avatar():
    return random.choice([
        902000068, 902000016, 902000011, 902000084,
        902000085, 902000087, 902000106, 902045016
    ])


async def HELLXbuild_chat_message(uid, owner_uid, message, timestamp, key, iv, name="Bot"):
    fields = {
        1: 1,
        2: {
            1: uid,
            2: owner_uid,
            4: message,
            5: timestamp,
            7: 6,
            9: {
                1: name,
                2: get_randm_avatar(),
                3: 901000029,
                4: 330,
                5: 801043518,
                7: 2,
                10: 1,
                12: 0,
                13: {1: 2},
                14: {
                    1: uid,
                    2: 8,
                    3: "\u0010\u0015\b\n\u000b\u0013\f\u000f\u0011\u0004\u0007\u0002\u0003\r\u000e\u0012\u0001\u0005\u0006"
                }
            },
            10: "en",
            13: {3: 1},
            14: ""
        }
    }
    return HELLXgenerate_packet(HELLXcreate_proto(fields).hex(), '1215', key, iv)


async def EnC_PacKeT(HeX, K, V):
    return AES.new(K, AES.MODE_CBC, V).encrypt(pad(bytes.fromhex(HeX), 16)).hex()


async def EnC_Vr(N):
    if N < 0:
        return b''
    H = []
    while True:
        B = N & 0x7F
        N >>= 7
        if N:
            B |= 0x80
        H.append(B)
        if not N:
            break
    return bytes(H)


async def CrEaTe_VarianT(f, v):
    return await EnC_Vr((f << 3) | 0) + await EnC_Vr(v)


async def CrEaTe_LenGTh(f, v):
    ev = v.encode() if isinstance(v, str) else v
    return await EnC_Vr((f << 3) | 2) + await EnC_Vr(len(ev)) + ev


async def CrEaTe_ProTo(fields):
    packet = bytearray()
    for f, v in fields.items():
        if isinstance(v, dict):
            packet.extend(await CrEaTe_LenGTh(f, await CrEaTe_ProTo(v)))
        elif isinstance(v, int):
            packet.extend(await CrEaTe_VarianT(f, v))
        elif isinstance(v, (str, bytes)):
            packet.extend(await CrEaTe_LenGTh(f, v))
    return packet


async def GeneRaTePk(Pk, N, K, V):
    PkEnc = await EnC_PacKeT(Pk, K, V)
    lh = hex(len(PkEnc) // 2)[2:]
    if len(lh) == 2:
        H = N + "000000"
    elif len(lh) == 3:
        H = N + "00000"
    elif len(lh) == 4:
        H = N + "0000"
    elif len(lh) == 5:
        H = N + "000"
    else:
        raise ValueError("Failed")
    return bytes.fromhex(H + lh + PkEnc)


async def ExiT(idT, K, V):
    fields = {1: 7, 2: {1: idT}}
    return await GeneRaTePk((await CrEaTe_ProTo(fields)).hex(), '0515', K, V)


def build_ob55_online_auth(account_uid, token, kts, key, iv):
    enc_token = AES.new(key, AES.MODE_CBC, iv).encrypt(pad(token.encode("utf-8"), 16))
    return (
        bytes.fromhex("830c")
        + int(account_uid).to_bytes(8, "big")
        + int(kts).to_bytes(4, "big")
        + len(enc_token).to_bytes(8, "big")
        + enc_token,
        enc_token
    )


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


async def aes_encrypt(payload, key, iv):
    return AES.new(key, AES.MODE_CBC, iv).encrypt(pad(payload, AES.block_size))


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
    lang = REGION_LANG.get(reg, "ar")
    api_url = (
        f"https://version.ggwhitehawk.com/live/ver.php?version={app_version}"
        f"&lang={lang}&device=android&channel=android&appstore=googleplay"
        f"&region={reg}&whitelist_version=1.3.0&whitelist_sp_version=1.0.0"
    )
    try:
        res = await client_http.get(api_url)
        data = res.json()
        cfg = (
            data.get("latest_release_version"),
            data.get("remote_version"),
            data.get("server_url"),
        )
        if cfg[0] and cfg[2]:
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
    for _ in range(2):
        try:
            r = await client_http.post(url, headers=hdrs, data=data)
            if r.status_code == 200:
                rd = r.json()
                return rd.get("open_id"), rd.get("access_token"), rd.get("platform", 4)
        except Exception:
            pass
        await asyncio.sleep(0.3)
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
    async with httpx.AsyncClient(verify=False, timeout=8.0) as client_http:
        vc = await version_config(client_http, region_pref)
        if not vc:
            push_log(f"version_config failed for region {region_pref}", "error")
            return None
        release_version, client_version, server_url = vc
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
        payload = await build_majorlogin_payload(open_id, access_token, platform, client_version, region_pref)
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
        level_val = (
            get_proto_field(dict_res, 6)
            or get_proto_field(dict_res, 3)
            or 1
        )
        exp_val = (
            get_proto_field(dict_res, 7)
            or get_proto_field(dict_res, 21)
            or 0
        )
        try:
            level_int = int(level_val)
        except Exception:
            level_int = 1
        try:
            exp_int = int(exp_val)
        except Exception:
            exp_int = 0
        return {
            "auth_uid": str(uid),
            "bot_uid": str(major_res.account_uid),
            "token": major_res.token,
            "access_token": access_token,
            "client_version": client_version,
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
            "level": level_int,
            "exp": exp_int,
            "login_data_raw": None,
        }


class LevelUpBot:
    """Individual account worker for Level-Up / Solo Match mode (no squad)."""
    def __init__(self, login, on_close=None):
        self.login = login
        self.auth_uid = str(login.get("auth_uid") or login["bot_uid"])
        self.uid = int(login["bot_uid"])
        self.token = login["token"]
        self.access_token = login.get("access_token") or ""
        self.client_version = login.get("client_version") or "1.134.21"
        self.key, self.iv = login["key"], login["iv"]
        self.ts = int(login["timestamp"])
        self.region = (login.get("region") or "ME")
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
        self.chat_r = self.chat_w = None
        self._chat_buf = bytearray()
        self._online_buf = bytearray()
        self._tasks = []
        self._udp_tasks = []
        self.closed = False
        self.persistent = False
        self.owner_uid = None
        self.voice_region_id = None
        self.chat_region_id = None
        self._match_index = 0

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
            "status": "PAUSED" if self.is_paused else self.status,
            "is_paused": self.is_paused,
            "active_matches": self.active_matches,
            "uptime_seconds": int(self.uptime_seconds),
        }

    async def connect(self):
        r = self.login
        chat_ip = await resolve_host_cloudflare(r["chat_ip"])
        self.chat_r, self.chat_w = await asyncio.wait_for(
            asyncio.open_connection(chat_ip, int(r["chat_port"])), 6
        )
        if self.chat_w.get_extra_info('socket'):
            optimize_tcp_socket(self.chat_w.get_extra_info('socket'))
        self.chat_w.write(bytes.fromhex(
            HELLXbuild_auth_startup(self.uid, self.token, self.ts, self.key, self.iv)
        ))
        await self.chat_w.drain()
        self._spawn(self._chat_read_loop())
        self._spawn(self._keepalive(self.chat_w))
        await asyncio.sleep(0.3)

        auth, _ = build_ob55_online_auth(self.uid, self.token, self.ts, self.key, self.iv)
        online_ip = await resolve_host_cloudflare(r["online_ip"])
        self.online_r, self.online_w = await asyncio.wait_for(
            asyncio.open_connection(online_ip, int(r["online_port"])), 6
        )
        if self.online_w.get_extra_info('socket'):
            optimize_tcp_socket(self.online_w.get_extra_info('socket'))
        self.online_w.write(auth)
        await self.online_w.drain()
        self._spawn(self._online_read_loop())
        self._spawn(self._keepalive(self.online_w))
        self.status = "PAUSED" if self.is_paused else "ONLINE"

    async def _keepalive(self, writer):
        try:
            while not self.closed and not writer.transport.is_closing():
                await asyncio.sleep(5)
                try:
                    writer.write(bytes.fromhex("0201"))
                    await writer.drain()
                except Exception:
                    break
        except asyncio.CancelledError:
            pass

    async def play_udp_match(self, server_ip_port, thunder, sharma, udp_key, match_code, match_index: int):
        """UDP match runner extracted from Level-Up code."""
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
            hello_packet = await build_hello_packet(f"{self.uid}_2585", udp_key_bytes, match_code)
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
            max_idle_before_hello_resend = 7.0

            async def send_thunder_sharma_inline():
                nonlocal ack_state, thunder_sent, sharma_sent
                if thunder_sent:
                    return
                async with send_lock:
                    if thunder_sent:
                        return
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
                    push_log(f"[MATCH #{match_index}] Thunder+Sharma sent for {self.name} ({self.uid})", "match")

            while not local_closed:
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
                            if frame.get('cmd') in [103, 107]:
                                completed_cleanly = True
                                local_closed = True
                                continue
                            if frame.get('cmd') == 101:
                                ack_pkt = await build_packet(
                                    0x68, (await layouts_from_mask(match_code))[1],
                                    0, 2, None, 1, b"\x01\x00", udp_key_bytes
                                )
                                await loop.sock_sendto(sock, ack_pkt, server_addr)
                                continue
                            if ptype in ["ACK", "PING", "HELLO", "JOIN_MATCH"]:
                                if ptype == "HELLO" and ack_state == "waiting_for_hello_reply":
                                    _, reply = await reply_for(frame, udp_key_bytes, match_code, ack_style="short")
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
                        if (time.time() - last_activity) > max_idle_before_hello_resend:
                            try:
                                pkt = await build_hello_packet(f"{self.uid}_2585", udp_key_bytes, match_code)
                                await loop.sock_sendto(sock, bytes.fromhex(pkt), (resolved_ip, port))
                            except Exception:
                                pass
                            last_activity = time.time()
                        if (time.time() - match_start_time) > 25.0:
                            break
                    elif ack_state == "thunder_sharma_sent":
                        if (time.time() - last_activity) > MATCH_IDLE_TIMEOUT:
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

            if completed_cleanly:
                self.matches_completed += 1
                matches_completed_total += 1
                self.gained_exp += 65
                self.current_exp += 65
        except Exception as e:
            push_log(f"[MATCH #{match_index}] UDP error ({self.uid}): {e}", "warning")
        finally:
            ping_stop.set()
            if ping_task and not ping_task.done():
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
            self.active_matches = max(0, self.active_matches - 1)
            if not self.is_paused and not self.closed:
                self.status = "IN_MATCH" if self.active_matches > 0 else "ONLINE"

    async def start_solo_match(self, timeout=8):
        """Starts a solo match individually for THIS single account only (no squad)."""
        global matches_started_total
        if self.closed or self.is_paused:
            return False
        if not self.online_w or self.online_w.transport.is_closing():
            return False

        self.status = "SEARCHING"
        try:
            await start_solo_match_packet(
                self.region, self.client_version, self.online_w, self.key, self.iv
            )
            self._match_index += 1
            self.matches_started += 1
            matches_started_total += 1
            self.active_matches = max(1, self.active_matches)
            if not self.is_paused:
                self.status = "IN_MATCH"
            push_log(f"Solo match #{self._match_index} started for {self.name} ({self.uid})", "match")
            return True
        except Exception as e:
            push_log(f"start_solo_match error ({self.uid}): {e}", "warning")
            self.status = "PAUSED" if self.is_paused else "ONLINE"
            return False

    async def _online_read_loop(self):
        try:
            while True:
                data = await self.online_r.read(16384)
                if not data:
                    break
                self._online_buf.extend(data)
                hex_data = data.hex()
                packet_length = len(data)
                if hex_data.startswith("0300") and packet_length >= 300:
                    try:
                        parsed = Parser().parse(hex_data[10:])
                        res = json.loads(json.dumps(await parse_results(parsed)))
                        token = udp_key = match_code = server_ip_port = block_val = None
                        if '42' in res and 'data' in res['42']:
                            match_code = res['42']['data']
                        if '5' in res and 'data' in res['5']:
                            f5 = res['5']['data']
                            server_ip_port = f5.get('2', {}).get('data')
                            udp_key = f5.get('3', {}).get('data')
                            token = f5.get('4', {}).get('data')
                            block_val = f5.get('1', {}).get('data')
                            if '42' in f5:
                                match_code = f5['42']['data']
                        if token and udp_key and match_code and server_ip_port:
                            thunder, sharma = await build_match_startup_packets(
                                token, udp_key, match_code, self.uid, block_val or 0,
                                server_ip=server_ip_port, region=self.region,
                                client_version=self.client_version, access_token=self.access_token
                            )
                            self.active_matches += 1
                            if not self.is_paused:
                                self.status = "IN_MATCH"
                            udp_t = asyncio.create_task(
                                self.play_udp_match(server_ip_port, thunder, sharma, udp_key, match_code, self._match_index)
                            )
                            self._udp_tasks.append(udp_t)
                    except Exception:
                        pass
                await self._drain_frames(self._online_buf, self._on_online_packet)
        except asyncio.CancelledError:
            return
        except Exception as e:
            push_log(f"online loop ({self.uid}): {e}", "warning")
        await self.close()

    async def _chat_read_loop(self):
        try:
            while True:
                data = await self.chat_r.read(16384)
                if not data:
                    break
                self._chat_buf.extend(data)
                await self._drain_frames(self._chat_buf, self._on_chat_packet)
        except asyncio.CancelledError:
            return
        except Exception as e:
            push_log(f"chat loop ({self.uid}): {e}", "warning")

    @staticmethod
    async def _drain_frames(buf, handler):
        pos = 0
        while len(buf) - pos >= 5:
            length = struct.unpack(">I", buf[pos + 1:pos + 5])[0]
            if 0 < length < 200000:
                if pos + 5 + length > len(buf):
                    break
                payload = bytes(buf[pos + 5:pos + 5 + length])
                try:
                    pd = HELLXdecode_proto(payload)
                    if pd:
                        await handler(pd)
                except Exception as e:
                    push_log(f"packet error: {e}", "warning")
                pos += 5 + length
            else:
                pos += 1
        if pos:
            del buf[:pos]

    async def _on_online_packet(self, pd):
        return

    async def _on_chat_packet(self, pd):
        return

    async def close(self):
        if self.closed:
            return
        self.closed = True
        self.status = "PAUSED" if self.is_paused else "OFFLINE"
        for w in (self.online_w, self.chat_w):
            if w:
                try:
                    w.close()
                except Exception:
                    pass
        me = asyncio.current_task()
        for t in list(self._tasks) + list(self._udp_tasks):
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

    def run(self, coro, timeout=25):
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
        self.accounts = []
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
        bot.persistent = True
        self.credentials[str(bot.uid)] = (pass_s, reg_s)
        self.credentials[uid_s] = (pass_s, reg_s)

        async with self.lock:
            self.accounts = [a for a in self.accounts if a.uid != bot.uid and str(a.auth_uid) != uid_s]
            self.accounts.append(bot)

        push_log(f"Account {uid_s} ({bot.name}) connected successfully", "success")
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

    async def get_next_bot(self):
        async with self.lock:
            active = [a for a in self.accounts if not a.closed and not a.is_paused]
            if not active:
                return None
            bot = active[self.current_index % len(active)]
            self.current_index = (self.current_index + 1) % len(active)
            return bot

    async def wait_for_account(self, timeout=12):
        deadline = asyncio.get_running_loop().time() + timeout
        while asyncio.get_running_loop().time() < deadline:
            bot = await self.get_next_bot()
            if bot:
                return bot
            if self.loaded and not self.accounts:
                return None
            await asyncio.sleep(0.5)
        return await self.get_next_bot()

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


async def _create_levelup_worker(region, clan_id, count, password):
    """Creates individual guest accounts for Level-Up mode without forming squads."""
    push_log(f"Creating {count} guest bots in region {region} for Level-Up mode...", "info")
    created = 0
    for _ in range(count):
        guest_uid = str(random.randint(3000000000, 4999999999))
        bot = await account_pool.connect_single(guest_uid, password, region, persist=True)
        if bot:
            created += 1
        await asyncio.sleep(0.4)
    push_log(f"Level-Up account creation finished: {created}/{count} bots connected in {region}", "success" if created else "warning")


# =====================================================================
# LEVEL-UP / SOLO MATCH MANAGER (INDIVIDUAL ACCOUNTS â NO SQUAD)
# =====================================================================

class LevelUpMatchManager:
    def __init__(self, pool):
        self.pool = pool
        self.lock = asyncio.Lock()
        self.auto_match_enabled = True

    async def start_matches_for_accounts(self, target_uid=""):
        async with self.lock:
            if target_uid:
                bot = await self.pool.find_bot(target_uid)
                if not bot or bot.closed or bot.is_paused:
                    msg = f"Account {target_uid} is not available or is paused"
                    push_log(msg, "warning")
                    return {"ok": False, "error": msg, "started_count": 0}
                ok = await bot.start_solo_match()
                return {
                    "ok": ok,
                    "error": None if ok else f"Failed to start solo match for {target_uid}",
                    "started_count": 1 if ok else 0,
                    "mode": "level_up_solo",
                }

            active_bots = [b for b in self.pool.accounts if not b.closed and not b.is_paused]
            if not active_bots:
                msg = "No active connected accounts available to start solo match"
                push_log(msg, "warning")
                return {"ok": False, "error": msg, "started_count": 0, "mode": "level_up_solo"}

            results = await asyncio.gather(*(b.start_solo_match() for b in active_bots), return_exceptions=True)
            started_count = sum(1 for r in results if r is True)
            push_log(
                f"Level-Up solo matches started for {started_count}/{len(active_bots)} individual account(s)",
                "match" if started_count else "warning"
            )
            return {
                "ok": started_count > 0,
                "error": None if started_count > 0 else "Failed to start solo matches",
                "started_count": started_count,
                "total_eligible": len(active_bots),
                "mode": "level_up_solo",
            }


levelup_manager = LevelUpMatchManager(account_pool)


async def _auto_levelup_watcher():
    """Watches connected accounts and starts solo matches individually for each active account (no squad)."""
    while True:
        try:
            await asyncio.sleep(START_MATCH_INTERVAL)
            if not levelup_manager.auto_match_enabled or all_paused_flag:
                continue
            idle_bots = [
                b for b in account_pool.accounts
                if not b.closed and not b.is_paused and b.active_matches == 0
            ]
            if idle_bots:
                await asyncio.gather(*(b.start_solo_match() for b in idle_bots), return_exceptions=True)
        except asyncio.CancelledError:
            break
        except Exception as e:
            push_log(f"auto_levelup_watcher error: {e}", "warning")


async_loop.start_background(_auto_levelup_watcher())


app = Flask(__name__)

# ÙØ¨Ø¯Ø£ ØªØ­ÙÙÙ Ø§ÙØ­Ø³Ø§Ø¨Ø§Øª ÙÙ Ø§ÙØ®ÙÙÙØ© ÙÙØ±Ø§Ù Ø¯ÙÙ ØªØ£Ø®ÙØ± Ø¥ÙÙØ§Ø¹ Ø§ÙØ³ÙØ±ÙØ±
async_loop.start_background(account_pool.load_and_connect())


FALLBACK_HTML = '<!DOCTYPE html>\n<html lang="ar" dir="rtl">\n<head>\n  <meta charset="UTF-8" />\n  <meta name="viewport" content="width=device-width, initial-scale=1.0" />\n  <title>Ø±Ø§ÙÙÙ ÙØµÙ - ÙÙÙ Ø£Ø¨ ÙØ±Ø¯Ù</title>\n  <style>\n    body { font-family: Tahoma, Arial, sans-serif; background: #0d0b14; color: #f3effa; margin: 0; padding: 16px; }\n    .card { background: #171324; border: 1px solid #2b2342; border-radius: 14px; padding: 16px; margin-bottom: 14px; }\n    .btn { background: linear-gradient(135deg, #7c3aed, #5b21b6); color: #fff; border: none; padding: 12px 18px; border-radius: 10px; font-size: 15px; font-weight: bold; cursor: pointer; margin: 4px; }\n    .btn-green { background: linear-gradient(135deg, #059669, #047857); }\n    .btn-gray { background: #2c2440; }\n    .grid { display: grid; grid-template-columns: repeat(auto-fit, minmax(140px, 1fr)); gap: 10px; }\n    .stat { background: #110e1c; padding: 12px; border-radius: 10px; text-align: center; }\n    .acc { background: #110e1c; padding: 12px; border-radius: 10px; margin-top: 8px; display: flex; justify-content: space-between; align-items: center; }\n    .badge { padding: 4px 10px; border-radius: 999px; font-size: 12px; background: #1e3a2f; color: #34d399; }\n    .logs { background: #09070f; padding: 10px; border-radius: 10px; max-height: 240px; overflow-y: auto; font-family: monospace; font-size: 12px; direction: ltr; text-align: left; }\n    input { background: #0e0b18; color: #fff; border: 1px solid #352b52; padding: 8px 10px; border-radius: 8px; margin: 4px; }\n  </style>\n</head>\n<body>\n  <div class="card">\n    <h2>â¡ Ø±Ø§ÙÙÙ ÙØµÙ â ÙØ¶Ø¹ ÙÙÙ Ø£Ø¨ Ø§ÙÙØ±Ø¯Ù (Ø¨Ø¯ÙÙ Ø³ÙÙØ§Ø¯)</h2>\n    <button id="btnSoloMatch" class="btn btn-green" onclick="startSoloMatch()">ð Ø¨Ø¯Ø¡ ÙØ§ØªØ´ ÙÙÙ Ø£Ø¨ ÙØ±Ø¯Ù ÙÙÙ Ø­Ø³Ø§Ø¨</button>\n    <button class="btn btn-gray" onclick="toggleAutoMatch()">ð ØªØ¨Ø¯ÙÙ Ø§ÙØªØ´ØºÙÙ Ø§ÙØªÙÙØ§Ø¦Ù</button>\n    <button class="btn" onclick="openAddForm()">â Ø¥Ø¶Ø§ÙØ© Ø­Ø³Ø§Ø¨</button>\n    <div id="addBox" style="display:none; margin-top:10px;">\n      <input id="inpUid" placeholder="UID" />\n      <input id="inpPass" placeholder="Password" />\n      <input id="inpRegion" value="ME" style="width:65px" />\n      <button class="btn" onclick="addAccount()">Ø­ÙØ¸ ÙØ§ØªØµØ§Ù</button>\n    </div>\n    <div id="msgBox" style="margin-top:10px; color:#a78bfa;"></div>\n  </div>\n\n  <div class="card grid">\n    <div class="stat"><div>Ø§ÙØ­Ø³Ø§Ø¨Ø§Øª Ø§ÙÙØªØµÙØ©</div><h3 id="sAccs">0</h3></div>\n    <div class="stat"><div>Ø§ÙÙØ§ØªØ´Ø§Øª Ø§ÙÙØ¨Ø¯ÙØ¡Ø©</div><h3 id="sMatches">0</h3></div>\n    <div class="stat"><div>Ø§ÙÙ EXP Ø§ÙÙÙØªØ³Ø¨</div><h3 id="sExp">0</h3></div>\n    <div class="stat"><div>Ø§ÙØªØ´ØºÙÙ Ø§ÙØªÙÙØ§Ø¦Ù</div><h3 id="sAuto">ÙÙØ¹Ù</h3></div>\n  </div>\n\n  <div class="card">\n    <h3>Ø§ÙØ­Ø³Ø§Ø¨Ø§Øª</h3>\n    <div id="accsList"></div>\n  </div>\n\n  <div class="card">\n    <h3>Ø³Ø¬Ù Ø§ÙØ£Ø­Ø¯Ø§Ø«</h3>\n    <div id="logsBox" class="logs"></div>\n  </div>\n\n  <script>\n    function openAddForm() {\n      const el = document.getElementById("addBox");\n      el.style.display = el.style.display === "none" ? "block" : "none";\n    }\n    async function addAccount() {\n      const uid = document.getElementById("inpUid").value.trim();\n      const password = document.getElementById("inpPass").value.trim();\n      const region = document.getElementById("inpRegion").value.trim() || "ME";\n      const r = await fetch("/api/account/add", {\n        method: "POST",\n        headers: {"Content-Type": "application/json"},\n        body: JSON.stringify({uid, password, region})\n      });\n      const d = await r.json();\n      document.getElementById("msgBox").innerText = d.status === "ok" ? ("ØªÙ Ø±Ø¨Ø· Ø§ÙØ­Ø³Ø§Ø¨: " + d.nickname) : (d.error || "ÙØ´Ù Ø§ÙØ±Ø¨Ø·");\n      refreshStats();\n    }\n    async function startSoloMatch() {\n      const btn = document.getElementById("btnSoloMatch");\n      btn.disabled = true;\n      document.getElementById("msgBox").innerText = "Ø¬Ø§Ø±Ù Ø¨Ø¯Ø¡ ÙØ§ØªØ´ ÙÙÙ Ø£Ø¨ ÙØ±Ø¯Ù...";\n      try {\n        const r = await fetch("/api/match/start", {\n          method: "POST",\n          headers: {"Content-Type": "application/json"},\n          body: JSON.stringify({})\n        });\n        const d = await r.json();\n        if (d.ok) {\n          document.getElementById("msgBox").innerText = "â ØªÙ Ø¨Ø¯Ø¡ Ø§ÙÙØ§ØªØ´ Ø§ÙÙØ±Ø¯Ù (" + (d.started_count || 0) + " Ø­Ø³Ø§Ø¨)";\n        } else {\n          document.getElementById("msgBox").innerText = "â ï¸ " + (d.error || "ØªØ¹Ø°Ø± Ø¨Ø¯Ø¡ Ø§ÙÙØ§ØªØ´");\n        }\n      } catch (e) {\n        document.getElementById("msgBox").innerText = "â Ø®Ø·Ø£ ÙÙ Ø§ÙØ§ØªØµØ§Ù Ø¨Ø§ÙØ³ÙØ±ÙØ±";\n      } finally {\n        btn.disabled = false;\n        refreshStats();\n      }\n    }\n    async function toggleAutoMatch() {\n      const r = await fetch("/api/match/auto", {method: "POST", headers: {"Content-Type": "application/json"}, body: "{}"});\n      const d = await r.json();\n      document.getElementById("msgBox").innerText = "Ø§ÙØªØ´ØºÙÙ Ø§ÙØªÙÙØ§Ø¦Ù ÙÙÙ Ø£Ø¨: " + (d.auto_match_enabled ? "ÙÙØ¹Ù" : "ÙØªÙÙÙ");\n      refreshStats();\n    }\n    async function refreshStats() {\n      const r = await fetch("/api/stats");\n      const d = await r.json();\n      document.getElementById("sAccs").innerText = d.total_accounts || 0;\n      document.getElementById("sMatches").innerText = d.total_matches_started || 0;\n      document.getElementById("sExp").innerText = d.total_gained_exp || 0;\n      document.getElementById("sAuto").innerText = d.auto_match_enabled ? "ÙÙØ¹Ù" : "ÙØªÙÙÙ";\n      const list = document.getElementById("accsList");\n      list.innerHTML = (d.accounts || []).map(a =>\n        `<div class="acc"><div><b>${a.nickname}</b> (${a.uid}) | EXP: ${a.gained_exp || 0}</div><span class="badge">${a.status}</span></div>`\n      ).join("") || "<div>ÙØ§ ØªÙØ¬Ø¯ Ø­Ø³Ø§Ø¨Ø§Øª ÙØªØµÙØ© Ø­Ø§ÙÙØ§Ù</div>";\n      const logs = document.getElementById("logsBox");\n      logs.innerHTML = (d.logs || []).slice(-60).map(l => `<div>[${l.time}] [${l.level}] ${l.message}</div>`).join("");\n      logs.scrollTop = logs.scrollHeight;\n    }\n    setInterval(refreshStats, 2500);\n    refreshStats();\n  </script>\n</body>\n</html>\n'


@app.route("/", methods=["GET"])
def index():
    base_dir = os.path.dirname(os.path.abspath(__file__))
    html_path = os.path.join(base_dir, "index.html")
    if os.path.exists(html_path):
        return send_file(html_path)
    return FALLBACK_HTML, 200


@app.route("/status_json", methods=["GET"])
@app.route("/status", methods=["GET"])
def status():
    return jsonify({
        "status": "online",
        "mode": "level_up_solo",
        "accounts_loaded": len(account_pool.accounts),
        "loading": account_pool.loading,
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
        "mode": "level_up_solo",
        "total_accounts": len(accs),
        "total_matches_started": total_started,
        "total_matches": total_done,
        "total_gained_exp": total_gained,
        "total_active_matches": total_active,
        "exp_per_hour": exp_per_hour,
        "uptime": int(uptime_sec),
        "accounts": accs,
        "logs": logs_copy,
        "auto_match_enabled": levelup_manager.auto_match_enabled,
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
    async_loop.start_background(_create_levelup_worker(region, clan_id, count, password))
    return jsonify({"ok": True, "region": region, "clan_id": clan_id, "count": count, "mode": "level_up_solo"}), 200


@app.route("/api/logs/clear", methods=["POST"])
def api_logs_clear():
    with ui_logs_lock:
        ui_logs.clear()
    return jsonify({"ok": True}), 200


@app.route("/api/match/start", methods=["GET", "POST"])
@app.route("/api/levelup/start", methods=["GET", "POST"])
def api_match_start():
    body = request.get_json(silent=True) or {}
    target_uid = str(body.get("uid") or request.args.get("uid") or "").strip()
    result = async_loop.run(
        levelup_manager.start_matches_for_accounts(target_uid=target_uid),
        timeout=25
    )
    status_code = 200 if result.get("ok") else 400
    result["DEV"] = DEV_NAME
    return jsonify(result), status_code


@app.route("/api/match/auto", methods=["POST"])
def api_match_auto():
    body = request.get_json(silent=True) or {}
    if "enabled" in body:
        levelup_manager.auto_match_enabled = bool(body["enabled"])
    else:
        levelup_manager.auto_match_enabled = not levelup_manager.auto_match_enabled
    push_log(
        f"Auto Level-Up solo match: {'ENABLED' if levelup_manager.auto_match_enabled else 'DISABLED'}",
        "info"
    )
    return jsonify({"ok": True, "auto_match_enabled": levelup_manager.auto_match_enabled, "DEV": DEV_NAME}), 200


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    app.run(host="0.0.0.0", port=port, threaded=True)
