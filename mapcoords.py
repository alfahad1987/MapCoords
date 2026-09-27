# -*- coding: utf-8 -*-
"""
MapCoords — محدد الإحداثيات على الخرائط
========================================
تطبيق ويندوز (Python + Tkinter) لتحديد الإحداثيات على صورة خريطة.

المتطلبات :  Python 3.9+   و   pip install pillow
التشغيل    :  python mapcoords.py
بناء EXE   :  شغّل ملف build_exe.bat

طريقة العمل باختصار
-------------------
1) ملف ← فتح خريطة  (صورة PNG / JPG / TIF ...)
2) أداة «معايرة الخريطة»: انقر على نقطتين (أو أكثر) معروفتي الإحداثيات
   واكتب إحداثيات كل نقطة بأي صيغة.
3) بعدها يعرض التطبيق إحداثيات المؤشر بجميع الصيغ، وتستطيع وضع العلامات
   والرسم والقياس من شريط الأدوات الجانبي.
"""
import os
import sys
import re
import time
import threading
import io
import csv
import copy
import json
import math
from xml.sax.saxutils import escape as xml_escape

import tkinter as tk
from tkinter import ttk, filedialog, messagebox, simpledialog, colorchooser

from PIL import Image, ImageTk, ImageDraw, ImageFont

Image.MAX_IMAGE_PIXELS = None
RS = getattr(Image, "Resampling", Image)

# ────────────────────────────────────────────────────────────────────────────
#  إعدادات عامة
# ────────────────────────────────────────────────────────────────────────────
TOOLBAR_SIDE = "right"      # "right" أو "left"  ← مكان شريط الأدوات
APP_TITLE = "MapCoords – محدد الإحداثيات على الخرائط"

# رقم الإصدار الحالي — زِده مع كل بناء جديد ترفعه إلى GitHub Releases
APP_VERSION = "1.0.0"

# مستودع GitHub الذي يستضيف الإصدارات (Releases)
UPDATE_OWNER = "alfahad1987"
UPDATE_REPO = "MapCoords"
UPDATE_ASSET_NAME = "MapCoords.exe"       # اسم الملف المرفوع في Release

# ────────────────────────────────────────────────────────────────────────────
#  1) الرياضيات الجيوديسية وصيغ الإحداثيات
# ────────────────────────────────────────────────────────────────────────────
A_WGS = 6378137.0
F_WGS = 1 / 298.257223563
E2 = F_WGS * (2 - F_WGS)
EARTH_R = 6371008.8
ECC = math.sqrt(E2)
NM = 1852.0   # الميل البحري بالمتر


def haversine(lat1, lon1, lat2, lon2):
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dp = p2 - p1
    dl = math.radians(lon2 - lon1)
    a = math.sin(dp / 2) ** 2 + math.cos(p1) * math.cos(p2) * math.sin(dl / 2) ** 2
    return 2 * EARTH_R * math.asin(min(1.0, math.sqrt(a)))


def geodesic(lat1, lon1, lat2, lon2):
    """المسافة بالمتر والاتجاه الأولي بالدرجات على مجسم WGS84 (Vincenty)"""
    if lat1 == lat2 and lon1 == lon2:
        return 0.0, 0.0
    a, f = A_WGS, F_WGS
    b = a * (1 - f)
    U1 = math.atan((1 - f) * math.tan(math.radians(lat1)))
    U2 = math.atan((1 - f) * math.tan(math.radians(lat2)))
    L = math.radians(lon2 - lon1)
    sU1, cU1, sU2, cU2 = math.sin(U1), math.cos(U1), math.sin(U2), math.cos(U2)
    lam = L
    for _ in range(200):
        sl, cl = math.sin(lam), math.cos(lam)
        ss = math.hypot(cU2 * sl, cU1 * sU2 - sU1 * cU2 * cl)
        if ss == 0:
            return 0.0, 0.0
        cs = sU1 * sU2 + cU1 * cU2 * cl
        sigma = math.atan2(ss, cs)
        sa = cU1 * cU2 * sl / ss
        c2a = 1 - sa * sa
        c2sm = cs - 2 * sU1 * sU2 / c2a if c2a != 0 else 0.0
        C = f / 16 * c2a * (4 + f * (4 - 3 * c2a))
        prev = lam
        lam = L + (1 - C) * f * sa * (sigma + C * ss * (c2sm + C * cs * (-1 + 2 * c2sm * c2sm)))
        if abs(lam - prev) < 1e-12:
            break
    else:
        return haversine(lat1, lon1, lat2, lon2), bearing(lat1, lon1, lat2, lon2)
    u2 = c2a * (a * a - b * b) / (b * b)
    A = 1 + u2 / 16384 * (4096 + u2 * (-768 + u2 * (320 - 175 * u2)))
    B = u2 / 1024 * (256 + u2 * (-128 + u2 * (74 - 47 * u2)))
    dsig = B * ss * (c2sm + B / 4 * (cs * (-1 + 2 * c2sm * c2sm)
                                     - B / 6 * c2sm * (-3 + 4 * ss * ss) * (-3 + 4 * c2sm * c2sm)))
    dist = b * A * (sigma - dsig)
    az = math.atan2(cU2 * math.sin(lam), cU1 * sU2 - sU1 * cU2 * math.cos(lam))
    return dist, (math.degrees(az) + 360) % 360


def bearing(lat1, lon1, lat2, lon2):
    p1, p2 = math.radians(lat1), math.radians(lat2)
    dl = math.radians(lon2 - lon1)
    y = math.sin(dl) * math.cos(p2)
    x = math.cos(p1) * math.sin(p2) - math.sin(p1) * math.cos(p2) * math.cos(dl)
    return (math.degrees(math.atan2(y, x)) + 360) % 360


# ---- UTM (سلسلة كروجر، WGS84) -------------------------------------------
_n = F_WGS / (2 - F_WGS)
_A = A_WGS / (1 + _n) * (1 + _n ** 2 / 4 + _n ** 4 / 64 + _n ** 6 / 256)
_ALPHA = (_n / 2 - 2 * _n ** 2 / 3 + 5 * _n ** 3 / 16 + 41 * _n ** 4 / 180,
          13 * _n ** 2 / 48 - 3 * _n ** 3 / 5 + 557 * _n ** 4 / 1440,
          61 * _n ** 3 / 240 - 103 * _n ** 4 / 140,
          49561 * _n ** 4 / 161280)
_BETA = (_n / 2 - 2 * _n ** 2 / 3 + 37 * _n ** 3 / 96 - _n ** 4 / 360,
         _n ** 2 / 48 + _n ** 3 / 15 - 437 * _n ** 4 / 1440,
         17 * _n ** 3 / 480 - 37 * _n ** 4 / 840,
         4397 * _n ** 4 / 161280)
_DELTA = (2 * _n - 2 * _n ** 2 / 3 - 2 * _n ** 3 + 116 * _n ** 4 / 45,
          7 * _n ** 2 / 3 - 8 * _n ** 3 / 5 - 227 * _n ** 4 / 45,
          56 * _n ** 3 / 15 - 136 * _n ** 4 / 35,
          4279 * _n ** 4 / 630)
K0 = 0.9996
BANDS = "CDEFGHJKLMNPQRSTUVWX"


def utm_band(lat):
    if lat < -80 or lat > 84:
        raise ValueError("خارج نطاق UTM")
    return BANDS[min(19, int((lat + 80) // 8))]


def utm_zone_for(lat, lon):
    lon = ((lon + 180) % 360) - 180
    zone = int((lon + 180) // 6) + 1
    if 56 <= lat < 64 and 3 <= lon < 12:
        zone = 32
    elif 72 <= lat <= 84:
        if 0 <= lon < 9:
            zone = 31
        elif 9 <= lon < 21:
            zone = 33
        elif 21 <= lon < 33:
            zone = 35
        elif 33 <= lon < 42:
            zone = 37
    return zone


def latlon_to_utm(lat, lon, zone=None):
    """يرجع (zone, band, easting, northing)"""
    band = utm_band(lat)
    if zone is None:
        zone = utm_zone_for(lat, lon)
    lon0 = math.radians((zone - 1) * 6 - 180 + 3)
    phi = math.radians(lat)
    lam = math.radians(lon) - lon0
    lam = (lam + math.pi) % (2 * math.pi) - math.pi
    e = math.sqrt(E2)
    t = math.sinh(math.atanh(math.sin(phi)) - e * math.atanh(e * math.sin(phi)))
    xi_p = math.atan2(t, math.cos(lam))
    eta_p = math.asinh(math.sin(lam) / math.hypot(t, math.cos(lam)))
    xi = xi_p + sum(_ALPHA[j - 1] * math.sin(2 * j * xi_p) * math.cosh(2 * j * eta_p) for j in range(1, 5))
    eta = eta_p + sum(_ALPHA[j - 1] * math.cos(2 * j * xi_p) * math.sinh(2 * j * eta_p) for j in range(1, 5))
    E = 500000.0 + K0 * _A * eta
    N = K0 * _A * xi
    if lat < 0:
        N += 10000000.0
    return zone, band, E, N


def utm_to_latlon(zone, northern, E, N):
    lon0 = math.radians((zone - 1) * 6 - 180 + 3)
    if not northern:
        N -= 10000000.0
    xi = N / (K0 * _A)
    eta = (E - 500000.0) / (K0 * _A)
    xi_p = xi - sum(_BETA[j - 1] * math.sin(2 * j * xi) * math.cosh(2 * j * eta) for j in range(1, 5))
    eta_p = eta - sum(_BETA[j - 1] * math.cos(2 * j * xi) * math.sinh(2 * j * eta) for j in range(1, 5))
    chi = math.asin(math.sin(xi_p) / math.cosh(eta_p))
    phi = chi + sum(_DELTA[j - 1] * math.sin(2 * j * chi) for j in range(1, 5))
    lam = lon0 + math.atan2(math.sinh(eta_p), math.cos(xi_p))
    return math.degrees(phi), math.degrees(lam)


# ---- MGRS ------------------------------------------------------------------
_MGRS_COL = ("ABCDEFGH", "JKLMNPQR", "STUVWXYZ")
_MGRS_ROW = "ABCDEFGHJKLMNPQRSTUV"


def utm_to_mgrs(zone, band, E, N, digits=5):
    col = _MGRS_COL[(zone - 1) % 3][int(E // 100000) - 1]
    off = 5 if zone % 2 == 0 else 0
    row = _MGRS_ROW[(int(N // 100000) + off) % 20]
    div = 10 ** (5 - digits)
    e = int((E % 100000) // div)
    n = int((N % 100000) // div)
    return f"{zone:02d}{band} {col}{row} {e:0{digits}d} {n:0{digits}d}"


def mgrs_to_latlon(zone, band, col, row, e_str, n_str):
    digits = len(e_str)
    mult = 10 ** (5 - digits)
    e = int(e_str) * mult
    n = int(n_str) * mult
    E = (_MGRS_COL[(zone - 1) % 3].index(col) + 1) * 100000 + e
    off = 5 if zone % 2 == 0 else 0
    n100 = (_MGRS_ROW.index(row) - off) % 20
    base_n = n100 * 100000 + n
    idx = BANDS.index(band)
    lat_min = -80 + 8 * idx
    lon_c = (zone - 1) * 6 - 180 + 3
    _, _, _, min_n = latlon_to_utm(max(lat_min, -80), lon_c, zone)
    Nn = base_n
    while Nn < min_n - 20000:
        Nn += 2000000
    return utm_to_latlon(zone, band >= "N", E, Nn)


# ---- Web Mercator ----------------------------------------------------------
def latlon_to_webmerc(lat, lon):
    if abs(lat) > 85.0511287798:
        raise ValueError("خارج النطاق")
    x = A_WGS * math.radians(lon)
    y = A_WGS * math.log(math.tan(math.pi / 4 + math.radians(lat) / 2))
    return x, y


# ---- Geohash ---------------------------------------------------------------
_B32 = "0123456789bcdefghjkmnpqrstuvwxyz"


def geohash(lat, lon, precision=10):
    lat_i = [-90.0, 90.0]
    lon_i = [-180.0, 180.0]
    bits = (16, 8, 4, 2, 1)
    bit = ch = 0
    even = True
    out = ""
    while len(out) < precision:
        if even:
            mid = (lon_i[0] + lon_i[1]) / 2
            if lon > mid:
                ch |= bits[bit]
                lon_i[0] = mid
            else:
                lon_i[1] = mid
        else:
            mid = (lat_i[0] + lat_i[1]) / 2
            if lat > mid:
                ch |= bits[bit]
                lat_i[0] = mid
            else:
                lat_i[1] = mid
        even = not even
        if bit < 4:
            bit += 1
        else:
            out += _B32[ch]
            bit = ch = 0
    return out


# ---- Plus Code (Open Location Code) ----------------------------------------
_OLC = "23456789CFGHJMPQRVWX"


def plus_code(lat, lon):
    lat = min(max(lat, -90.0), 90.0 - 1e-9) + 90.0
    lon = ((lon + 180.0) % 360.0)
    lat_i = int(math.floor(round(lat * 8000, 6)))
    lon_i = int(math.floor(round(lon * 8000, 6)))
    ld, gd = [], []
    for _ in range(5):
        ld.insert(0, lat_i % 20)
        lat_i //= 20
        gd.insert(0, lon_i % 20)
        lon_i //= 20
    code = "".join(_OLC[ld[i]] + _OLC[gd[i]] for i in range(5))
    return code[:8] + "+" + code[8:]


# ---- Maidenhead -------------------------------------------------------------
def maidenhead(lat, lon):
    lon = lon + 180.0
    lat = lat + 90.0
    s = chr(65 + int(lon // 20)) + chr(65 + int(lat // 10))
    lon %= 20
    lat %= 10
    s += str(int(lon // 2)) + str(int(lat // 1))
    lon %= 2
    lat %= 1
    s += chr(97 + int(lon * 12)) + chr(97 + int(lat * 24))
    return s


# ---- تنسيقات DMS / DDM -----------------------------------------------------
def _dms_parts(v):
    v = abs(v)
    d = int(v)
    m = int((v - d) * 60)
    s = round((v - d - m / 60) * 3600, 2)
    if s >= 60:
        s -= 60
        m += 1
    if m >= 60:
        m -= 60
        d += 1
    return d, m, s


def _ddm_parts(v):
    v = abs(v)
    d = int(v)
    m = round((v - d) * 60, 4)
    if m >= 60:
        m -= 60
        d += 1
    return d, m


def fmt_dms(lat, lon):
    def one(v, pos, neg):
        d, m, s = _dms_parts(v)
        return f"{d}°{m:02d}′{s:05.2f}″ {pos if v >= 0 else neg}"
    return f"{one(lat, 'N', 'S')}, {one(lon, 'E', 'W')}"


def fmt_ddm(lat, lon):
    def one(v, pos, neg):
        d, m = _ddm_parts(v)
        return f"{d}°{m:07.4f}′ {pos if v >= 0 else neg}"
    return f"{one(lat, 'N', 'S')}, {one(lon, 'E', 'W')}"


# صفوف الحقول:  (المفتاح, العنوان, [(الحقل, الوصف, الوزن)])
FIELD_ROWS = [
    ("dd", "عشرية DD", [("lat", "العرض Lat", 1), ("lon", "الطول Lon", 1)]),
    ("dms", "DMS د/ق/ث", [("lat", "العرض", 1), ("lon", "الطول", 1)]),
    ("ddm", "DDM د/ق عشرية", [("lat", "العرض", 1), ("lon", "الطول", 1)]),
    ("utm", "UTM  WGS84", [("zone", "المنطقة", 1), ("e", "شرقاً  E", 2), ("n", "شمالاً  N", 2)]),
    ("mgrs", "MGRS", [("sq", "المنطقة والمربع", 2), ("e", "شرقاً", 2), ("n", "شمالاً", 2)]),
    ("merc", "Web Mercator", [("x", "X  شرقاً", 1), ("y", "Y  شمالاً", 1)]),
    ("pix", "بكسل الصورة", [("x", "x", 1), ("y", "y", 1)]),
    ("code", "رموز مختصرة", [("plus", "Plus Code", 3), ("geohash", "Geohash", 3), ("mh", "Maidenhead", 2)]),
]
ALL_KEYS = [f"{r}.{k}" for r, _, cells in FIELD_ROWS for k, _, _ in cells]
ROW_TITLES = {r: t for r, t, _ in FIELD_ROWS}


def format_all(lat, lon):
    out = {
        "dd": f"{lat:.6f}, {lon:.6f}",
        "lat": f"{lat:.8f}",
        "lon": f"{lon:.8f}",
        "dms": fmt_dms(lat, lon),
        "ddm": fmt_ddm(lat, lon),
    }
    try:
        z, b, E, N = latlon_to_utm(lat, lon)
        out["utm"] = f"{z}{b} {E:.0f}E {N:.0f}N"
        out["mgrs"] = utm_to_mgrs(z, b, E, N)
    except Exception:
        out["utm"] = out["mgrs"] = "خارج نطاق UTM"
    try:
        x, y = latlon_to_webmerc(lat, lon)
        out["merc"] = f"{x:.2f}, {y:.2f}"
    except Exception:
        out["merc"] = "خارج النطاق"
    out["plus"] = plus_code(lat, lon)
    out["geohash"] = geohash(lat, lon)
    out["mh"] = maidenhead(lat, lon)
    return out


def format_parts(lat, lon):
    """كل حقل على حدة (العرض منفصل عن الطول في كل الصيغ)"""
    a = format_all(lat, lon)
    d = {"dd.lat": f"{lat:.6f}", "dd.lon": f"{lon:.6f}"}
    dl, dn = a["dms"].split(", ")
    d["dms.lat"], d["dms.lon"] = dl, dn
    dl, dn = a["ddm"].split(", ")
    d["ddm.lat"], d["ddm.lon"] = dl, dn
    try:
        z, b, E, N = latlon_to_utm(lat, lon)
        d["utm.zone"], d["utm.e"], d["utm.n"] = f"{z}{b}", f"{E:.0f}", f"{N:.0f}"
        zb, sq, me, mn = utm_to_mgrs(z, b, E, N).split(" ")
        d["mgrs.sq"], d["mgrs.e"], d["mgrs.n"] = f"{zb} {sq}", me, mn
    except Exception:
        for k in ("utm.zone", "utm.e", "utm.n", "mgrs.sq", "mgrs.e", "mgrs.n"):
            d[k] = "—"
    try:
        x, y = latlon_to_webmerc(lat, lon)
        d["merc.x"], d["merc.y"] = f"{x:.2f}", f"{y:.2f}"
    except Exception:
        d["merc.x"] = d["merc.y"] = "—"
    d["code.plus"], d["code.geohash"], d["code.mh"] = a["plus"], a["geohash"], a["mh"]
    return d


# ---- محللات عكسية للكتابة اليدوية في الحقول ----------------------------------
def webmerc_to_latlon(x, y):
    return (math.degrees(2 * math.atan(math.exp(y / A_WGS)) - math.pi / 2), math.degrees(x / A_WGS))


def geohash_decode(txt):
    t = txt.strip().lower()
    if not t or any(c not in _B32 for c in t):
        raise ValueError("رمز Geohash غير صحيح")
    lat_i, lon_i, even = [-90.0, 90.0], [-180.0, 180.0], True
    for ch in t:
        v = _B32.index(ch)
        for bit in (16, 8, 4, 2, 1):
            iv = lon_i if even else lat_i
            mid = (iv[0] + iv[1]) / 2
            if v & bit:
                iv[0] = mid
            else:
                iv[1] = mid
            even = not even
    return (lat_i[0] + lat_i[1]) / 2, (lon_i[0] + lon_i[1]) / 2


def maidenhead_decode(txt):
    m = re.match(r"^([A-Ra-r])([A-Ra-r])(\d)(\d)(?:([A-Xa-x])([A-Xa-x]))?$", txt.strip())
    if not m:
        raise ValueError("رمز Maidenhead غير صحيح (مثل LL39xj)")
    lon = (ord(m.group(1).upper()) - 65) * 20 - 180 + int(m.group(3)) * 2
    lat = (ord(m.group(2).upper()) - 65) * 10 - 90 + int(m.group(4))
    if m.group(5):
        lon += (ord(m.group(5).upper()) - 65) / 12 + 1 / 24
        lat += (ord(m.group(6).upper()) - 65) / 24 + 1 / 48
    else:
        lon += 1
        lat += 0.5
    return lat, lon


def _plus_decode_full(digits):
    """يفك رموز Plus Code حتى 15 رمزاً (الأزواج ثم شبكة التدقيق 4×5)"""
    n = min(len(digits), 10)
    n -= n % 2
    if n < 2:
        raise ValueError("Plus Code قصير جداً")
    lat, lon, res = -90.0, -180.0, 20.0
    for i in range(0, n, 2):
        lat += _OLC.index(digits[i]) * res
        lon += _OLC.index(digits[i + 1]) * res
        last = res
        res /= 20
    lat_res = lon_res = last
    if len(digits) > 10:
        for ch in digits[10:15]:
            idx = _OLC.index(ch)
            lat_res /= 5
            lon_res /= 4
            lat += (idx // 4) * lat_res
            lon += (idx % 4) * lon_res
    return lat + lat_res / 2, lon + lon_res / 2, last


def plus_decode(txt, ref=None):
    """Plus Code كامل (7HXCC6R9+X5) أو مختصر (CC6R+9X) فيُكمَّل من أقرب موقع لمركز العرض"""
    c = txt.strip().upper().split()[0] if txt.strip() else ""
    if "+" not in c:
        raise ValueError("Plus Code يجب أن يحتوي على + مثل 7HXCC6R9+X5")
    a, b = c.split("+", 1)
    digits = a + b
    if any(ch not in _OLC for ch in digits):
        raise ValueError("Plus Code يحتوي على حروف غير صحيحة")
    if len(a) == 8:
        return _plus_decode_full(digits)[:2]
    missing = 8 - len(a)
    if len(a) in (2, 4, 6) and ref:
        prefix = plus_code(ref[0], ref[1])[:missing]
        lat, lon, _ = _plus_decode_full(prefix + digits)
        pairs = missing // 2
        res = 20.0 / (20 ** (pairs - 1))
        half = res / 2
        if lat - ref[0] > half:
            lat -= res
        elif ref[0] - lat > half:
            lat += res
        if lon - ref[1] > half:
            lon -= res
        elif ref[1] - lon > half:
            lon += res
        return lat, lon
    raise ValueError("الرمز المختصر يحتاج خريطة معايَرة، أو أدخل الرمز كاملاً")


def _num(txt, what):
    t = re.sub(r"[^\d.\-+]", "", (txt or "").translate(_TRANS))
    try:
        return float(t)
    except ValueError:
        raise ValueError(f"قيمة {what} غير صحيحة")


def _single(txt, kind):
    """حقل واحد: عرض أو طول بأي صيغة (DD/DMS/DDM) مع N/S/E/W أو إشارة سالبة"""
    t = (txt or "").strip().translate(_TRANS).upper()
    try:
        v, h = _parse_part(t.replace("''", '"'))
    except ValueError:
        raise ValueError("العرض غير مفهوم" if kind == "lat" else "الطول غير مفهوم")
    if kind == "lat" and h in ("E", "W"):
        raise ValueError("حقل العرض يقبل N أو S فقط")
    if kind == "lon" and h in ("N", "S"):
        raise ValueError("حقل الطول يقبل E أو W فقط")
    if abs(v) > (90 if kind == "lat" else 180):
        raise ValueError("العرض يجب ألا يتجاوز 90°" if kind == "lat" else "الطول يجب ألا يتجاوز 180°")
    return v


def parse_row(row, vals, field=None, ref=None):
    """يحوّل حقول صف واحد إلى ('ll', lat, lon) أو ('px', x, y)"""
    g = lambda k: (vals.get(k) or "").strip()
    if row in ("dd", "dms", "ddm"):
        return ("ll", _single(g("lat"), "lat"), _single(g("lon"), "lon"))
    if row == "utm":
        m = re.match(r"^(\d{1,2})\s*([C-HJ-NP-X])$", g("zone").upper())
        if not m or not 1 <= int(m.group(1)) <= 60:
            raise ValueError("المنطقة مثل 38R")
        E, N = _num(g("e"), "الشرق"), _num(g("n"), "الشمال")
        return ("ll",) + utm_to_latlon(int(m.group(1)), m.group(2) >= "N", E, N)
    if row == "mgrs":
        m = re.match(r"^(\d{1,2})\s*([C-HJ-NP-X])\s*([A-HJ-NP-Z])([A-HJ-NP-V])$", g("sq").upper())
        e, n = re.sub(r"\s", "", g("e")), re.sub(r"\s", "", g("n"))
        if not m:
            raise ValueError("المنطقة والمربع مثل 38R QT")
        if not (e.isdigit() and n.isdigit() and len(e) == len(n) and 1 <= len(e) <= 5):
            raise ValueError("الشرق والشمال أرقام بنفس الطول (حتى 5 خانات)")
        return ("ll",) + mgrs_to_latlon(int(m.group(1)), m.group(2), m.group(3), m.group(4), e, n)
    if row == "merc":
        lat, lon = webmerc_to_latlon(_num(g("x"), "X"), _num(g("y"), "Y"))
        return ("ll", lat, lon)
    if row == "pix":
        return ("px", _num(g("x"), "x"), _num(g("y"), "y"))
    if row == "code":
        if field == "plus":
            return ("ll",) + tuple(plus_decode(g("plus"), ref))
        if field == "geohash":
            return ("ll",) + geohash_decode(g("geohash"))
        return ("ll",) + maidenhead_decode(g("mh"))
    raise ValueError("صيغة غير معروفة")


# ---- قراءة الإحداثيات بأي صيغة ---------------------------------------------
_TRANS = str.maketrans({
    "٠": "0", "١": "1", "٢": "2", "٣": "3", "٤": "4",
    "٥": "5", "٦": "6", "٧": "7", "٨": "8", "٩": "9",
    "٫": ".", "،": ",", "؛": ";", "′": "'", "’": "'", "‘": "'",
    "″": '"', "”": '"', "“": '"', "º": "°", "˚": "°", "−": "-", "–": "-",
})


def _parse_part(part):
    hem = re.findall(r"[NSEW]", part)
    nums = re.findall(r"\d+(?:\.\d+)?", part)
    if not nums or len(nums) > 3:
        raise ValueError
    d = float(nums[0])
    m = float(nums[1]) if len(nums) > 1 else 0.0
    s = float(nums[2]) if len(nums) > 2 else 0.0
    if m >= 60 or s >= 60:
        raise ValueError
    v = d + m / 60 + s / 3600
    neg = ("-" in part) or (hem and hem[0] in "SW")
    return (-v if neg else v), (hem[0] if hem else None)


def parse_coords(text):
    """يقرأ إحداثيات بصيغ: DD / DMS / DDM / UTM / MGRS ويرجع (lat, lon)"""
    s = (text or "").strip().translate(_TRANS)
    if not s:
        raise ValueError("لم تُدخل إحداثيات")
    up = s.upper()

    # UTM:  39R 785432 3245678
    m = re.match(r"^(\d{1,2})\s*([C-HJ-NP-X])\s+(\d+(?:\.\d+)?)\s*M?E?[\s,;]+(\d+(?:\.\d+)?)\s*M?N?$", up)
    if m:
        z, b = int(m.group(1)), m.group(2)
        return utm_to_latlon(z, b >= "N", float(m.group(3)), float(m.group(4)))

    # MGRS:  39R XH 85432 45678
    m = re.match(r"^(\d{1,2})\s*([C-HJ-NP-X])\s*([A-HJ-NP-Z])([A-HJ-NP-V])\s*([\d\s]{2,22})$", up)
    if m:
        digs = re.sub(r"\s", "", m.group(5))
        if len(digs) % 2 == 0 and 2 <= len(digs) <= 10:
            h = len(digs) // 2
            return mgrs_to_latlon(int(m.group(1)), m.group(2), m.group(3), m.group(4), digs[:h], digs[h:])

    up = up.replace("''", '"')
    letters = [(mm.start(), mm.group()) for mm in re.finditer(r"[NSEW]", up)]
    has_sym = bool(letters) or any(ch in up for ch in "°'\"")
    v1 = v2 = h1 = h2 = None

    if not has_sym:
        nums = re.findall(r"[-+]?\d+(?:\.\d+)?", up)
        if len(nums) == 6:
            p1, p2 = " ".join(nums[:3]), " ".join(nums[3:])
        elif len(nums) == 4:
            p1, p2 = " ".join(nums[:2]), " ".join(nums[2:])
        elif len(nums) >= 2:
            return _check(float(nums[0]), float(nums[1]), None, None)
        else:
            raise ValueError("تعذّر فهم الإحداثيات")
        v1, h1 = _parse_part(p1)
        v2, h2 = _parse_part(p2)
    else:
        sep = re.search(r"[;,]", up)
        if sep:
            p1, p2 = up[:sep.start()], up[sep.end():]
        elif len(letters) == 2:
            if up.lstrip()[:1] in "NSEW":
                cut = letters[1][0]
            else:
                cut = letters[0][0] + 1
            p1, p2 = up[:cut], up[cut:]
        elif up.count("°") >= 2:
            idx2 = [i for i, ch in enumerate(up) if ch == "°"][1]
            st = idx2
            while st > 0 and up[st - 1] in "0123456789. -+":
                st -= 1
            p1, p2 = up[:st], up[st:]
        else:
            raise ValueError("تعذّر فهم الإحداثيات")
        v1, h1 = _parse_part(p1)
        v2, h2 = _parse_part(p2)
    return _check(v1, v2, h1, h2)


def _check(a, b, ha, hb):
    if (ha in ("E", "W")) or (hb in ("N", "S")):
        lat, lon = b, a
    else:
        lat, lon = a, b
        if ha is None and hb is None and abs(lat) > 90 and abs(lon) <= 90:
            lat, lon = lon, lat
    if not (-90 <= lat <= 90 and -180 <= lon <= 180):
        raise ValueError("قيم الإحداثيات خارج النطاق المسموح")
    return lat, lon


# ────────────────────────────────────────────────────────────────────────────
#  2) المعايرة (ربط بكسلات الصورة بالإحداثيات)
# ────────────────────────────────────────────────────────────────────────────
def _solve3(M, v):
    n = 3
    A = [row[:] + [v[i]] for i, row in enumerate(M)]
    for i in range(n):
        piv = max(range(i, n), key=lambda r: abs(A[r][i]))
        if abs(A[piv][i]) < 1e-12:
            raise ValueError("نقاط المعايرة على استقامة واحدة — اختر نقاطاً غير متراصفة")
        A[i], A[piv] = A[piv], A[i]
        for r in range(i + 1, n):
            f = A[r][i] / A[i][i]
            for c in range(i, n + 1):
                A[r][c] -= f * A[i][c]
    x = [0.0] * n
    for i in range(n - 1, -1, -1):
        x[i] = (A[i][n] - sum(A[i][j] * x[j] for j in range(i + 1, n))) / A[i][i]
    return x


class GeoRef:
    """تحويل أفيني بين البكسل والإحداثيات (ميركاتور أو خطي)"""

    def __init__(self):
        self.pts = []            # (px, py, lat, lon)
        self.mode = "web"        # web | wgs84 | linear
        self.coef = None
        self.rms = None

    @property
    def ok(self):
        return self.coef is not None

    def _proj(self, lat, lon):
        if self.mode == "linear":
            return (lon, lat)
        lat = max(min(lat, 85.0511), -85.0511)
        ph = math.radians(lat)
        x = A_WGS * math.radians(lon)
        if self.mode == "wgs84":          # ميركاتور بيضاوي (الخرائط البحرية / Admiralty)
            sn = math.sin(ph)
            y = A_WGS * (math.atanh(sn) - ECC * math.atanh(ECC * sn))
        else:                             # ميركاتور كروي (Google / OSM)
            y = A_WGS * math.log(math.tan(math.pi / 4 + ph / 2))
        return (x, y)

    def _unproj(self, X, Y):
        if self.mode == "linear":
            return (Y, X)
        lon = math.degrees(X / A_WGS)
        t = math.exp(Y / A_WGS)
        if self.mode == "wgs84":
            ph = 2 * math.atan(t) - math.pi / 2
            for _ in range(8):
                sn = math.sin(ph)
                ph = 2 * math.atan(t * ((1 + ECC * sn) / (1 - ECC * sn)) ** (ECC / 2)) - math.pi / 2
            return (math.degrees(ph), lon)
        return (math.degrees(2 * math.atan(t) - math.pi / 2), lon)

    def fit(self):
        self.coef = None
        self.rms = None
        n = len(self.pts)
        if n < 2:
            return
        P = [self._proj(p[2], p[3]) for p in self.pts]
        if n == 2:
            (x1, y1), (x2, y2) = (self.pts[0][0], self.pts[0][1]), (self.pts[1][0], self.pts[1][1])
            dx, dy = x2 - x1, y2 - y1
            if abs(dx) < 3 and abs(dy) < 3:
                raise ValueError("النقطتان متقاربتان جداً")
            sx = (P[1][0] - P[0][0]) / dx if abs(dx) >= 3 else None
            sy = (P[1][1] - P[0][1]) / dy if abs(dy) >= 3 else None
            if sx is not None and sy is not None and min(abs(dx), abs(dy)) < 0.25 * max(abs(dx), abs(dy)):
                if abs(dx) > abs(dy):
                    sy = -abs(sx)
                else:
                    sx = abs(sy)
            if sx is None:
                sx = abs(sy)
            if sy is None:
                sy = -abs(sx)
            a, e = sx, sy
            self.coef = (a, 0.0, P[0][0] - a * x1, 0.0, e, P[0][1] - e * y1)
        else:
            Sxx = Sxy = Sx = Syy = Sy = 0.0
            bE = [0.0] * 3
            bN = [0.0] * 3
            for (px, py, _, _), (E, N) in zip(self.pts, P):
                Sxx += px * px; Sxy += px * py; Sx += px
                Syy += py * py; Sy += py
                bE[0] += px * E; bE[1] += py * E; bE[2] += E
                bN[0] += px * N; bN[1] += py * N; bN[2] += N
            M = [[Sxx, Sxy, Sx], [Sxy, Syy, Sy], [Sx, Sy, float(n)]]
            a, b, c = _solve3(M, bE)
            d, e, f = _solve3(M, bN)
            self.coef = (a, b, c, d, e, f)
            errs = []
            for (px, py, lat, lon) in self.pts:
                la, lo = self.px_to_ll(px, py)
                errs.append(haversine(lat, lon, la, lo))
            self.rms = math.sqrt(sum(x * x for x in errs) / len(errs))

    def px_to_ll(self, px, py):
        a, b, c, d, e, f = self.coef
        return self._unproj(a * px + b * py + c, d * px + e * py + f)

    def ll_to_px(self, lat, lon):
        a, b, c, d, e, f = self.coef
        X, Y = self._proj(lat, lon)
        det = a * e - b * d
        return ((e * (X - c) - b * (Y - f)) / det, (-d * (X - c) + a * (Y - f)) / det)


# ────────────────────────────────────────────────────────────────────────────
#  3) أدوات هندسية مساعدة
# ────────────────────────────────────────────────────────────────────────────
def fmt_len(m):
    if m >= 1000:
        return f"{m / 1000:.3f} كم ({m / NM:.2f} م.ب)"
    return f"{m:.1f} م ({m / NM:.3f} م.ب)"


def fmt_area(a):
    s = f"{a / 1e6:.4f} كم²" if a >= 1e6 else f"{a:,.1f} م²"
    if a >= 1000:
        s += f"  ({a / 1e4:,.2f} هكتار)"
    return s


def geo_area(latlons):
    if len(latlons) < 3:
        return 0.0
    zone = utm_zone_for(latlons[0][0], latlons[0][1])
    xy = []
    for la, lo in latlons:
        try:
            _, _, E, N = latlon_to_utm(la, lo, zone)
        except Exception:
            return 0.0
        xy.append((E, N))
    s = 0.0
    for i in range(len(xy)):
        x1, y1 = xy[i]
        x2, y2 = xy[(i + 1) % len(xy)]
        s += x1 * y2 - x2 * y1
    return abs(s) / 2


def seg_dist(px, py, ax, ay, bx, by):
    dx, dy = bx - ax, by - ay
    if dx == 0 and dy == 0:
        return math.hypot(px - ax, py - ay)
    t = max(0, min(1, ((px - ax) * dx + (py - ay) * dy) / (dx * dx + dy * dy)))
    return math.hypot(px - (ax + t * dx), py - (ay + t * dy))


def point_in_poly(x, y, poly):
    inside = False
    n = len(poly)
    j = n - 1
    for i in range(n):
        xi, yi = poly[i]
        xj, yj = poly[j]
        if (yi > y) != (yj > y) and x < (xj - xi) * (y - yi) / (yj - yi + 1e-12) + xi:
            inside = not inside
        j = i
    return inside


def rect_corners(p):
    (x0, y0), (x1, y1) = p[0], p[1]
    return [[x0, y0], [x1, y0], [x1, y1], [x0, y1]]


def circle_ring(p, n=72):
    cx, cy = p[0]
    r = math.hypot(p[1][0] - cx, p[1][1] - cy)
    return [[cx + r * math.cos(2 * math.pi * i / n), cy + r * math.sin(2 * math.pi * i / n)] for i in range(n)]


# خرائط معروفة: تُعاير تلقائياً عند التعرف عليها من حجم الصورة
PRESETS = [
    {
        "name": "Admiralty Chart 2884 — Maritime Zones of the State of Kuwait (WGS84)",
        "size": (12371, 8662),
        "proj": "wgs84",
        "calib": [[566.54, 631.3, 30.416667, 47.75],
                  [11959.61, 631.3, 30.416667, 51.166667],
                  [11959.61, 7934.81, 28.5, 51.166667],
                  [566.54, 7934.81, 28.5, 47.75],
                  [6402.01, 4141.69, 29.5, 49.5]],
    },
]


DEFAULT_MAP = "Kuwait_Chart_2884.png"      # الخريطة المدمجة (تُفتح تلقائياً عند التشغيل)


def resource_path(name):
    """مسار ملف مدمج داخل البرنامج (EXE) أو بجانب السكربت"""
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    return os.path.join(base, name)


def user_data_dir():
    base = os.environ.get("APPDATA") or os.path.expanduser("~")
    d = os.path.join(base, "MapCoords")
    try:
        os.makedirs(d, exist_ok=True)
    except Exception:
        pass
    return d


def load_pdf_page(path):
    """يفتح الصفحة الأولى من PDF: يستخرج الصورة الممسوحة الأصلية إن وُجدت (بدقتها الكاملة)
    وإلا يرسم الصفحة بدقة 300 dpi كحد أقصى.  يحتاج:  pip install pypdfium2"""
    try:
        import pypdfium2 as pdfium
    except ImportError:
        raise RuntimeError("لفتح ملفات PDF ثبّت المكتبة أولاً:\n\n    pip install pypdfium2\n\nأو حوّل الصفحة إلى صورة PNG.")
    pdf = pdfium.PdfDocument(path)
    page = pdf[0]
    try:
        import pypdfium2.raw as raw
        objs = list(page.get_objects(filter=(raw.FPDF_PAGEOBJ_IMAGE,)))
        if len(objs) == 1:
            im = objs[0].get_bitmap().to_pil()
            wpt, hpt = page.get_size()
            if im.width * im.height >= 0.5 * (wpt * hpt):
                return im if im.mode == "RGB" else im.convert("RGB")
    except Exception:
        pass
    wpt, hpt = page.get_size()
    scale = min(300 / 72.0, 16000.0 / max(wpt, hpt))
    im = page.render(scale=scale).to_pil()
    return im if im.mode == "RGB" else im.convert("RGB")


def load_image_any(path):
    if path.lower().endswith(".pdf"):
        return load_pdf_page(path)
    im = Image.open(path)
    im.load()
    return im if im.mode == "RGB" else im.convert("RGB")


def shape_metrics_geo(s, geo):
    t = s["type"]
    pts = s["pts"]
    if t in ("point", "text") or not pts:
        return ""
    if not geo.ok:
        if t in ("line", "measure", "free") and len(pts) > 1:
            L = sum(math.hypot(b[0] - a[0], b[1] - a[1]) for a, b in zip(pts, pts[1:]))
            return f"{L:.0f} px"
        return ""
    G = lambda p: geo.px_to_ll(p[0], p[1])
    try:
        if t in ("line", "measure", "free"):
            if len(pts) < 2:
                return ""
            L = sum(geodesic(*G(a), *G(b))[0] for a, b in zip(pts, pts[1:]))
            txt = "الطول: " + fmt_len(L)
            if t == "measure":
                txt += f"   الاتجاه: {geodesic(*G(pts[-2]), *G(pts[-1]))[1]:.1f}°"
            return txt
        if t in ("polygon", "rect"):
            poly = pts if t == "polygon" else (rect_corners(pts) if len(pts) >= 2 else [])
            if len(poly) < 3:
                return ""
            ll = [G(p) for p in poly]
            per = sum(geodesic(*ll[i], *ll[(i + 1) % len(ll)])[0] for i in range(len(ll)))
            return f"المحيط: {fmt_len(per)}   المساحة: {fmt_area(geo_area(ll))}"
        if t == "circle" and len(pts) >= 2:
            r = geodesic(*G(pts[0]), *G(pts[1]))[0]
            return f"نصف القطر: {fmt_len(r)}   المساحة: {fmt_area(math.pi * r * r)}"
    except Exception:
        return ""
    return ""


def route_leg_texts(s, geo):
    pts = s["pts"]
    pairs = list(zip(pts, pts[1:]))
    if s["type"] == "polygon" and len(pts) > 2:
        pairs.append((pts[-1], pts[0]))
    out = []
    for a, b in pairs:
        d, az = geodesic(*geo.px_to_ll(*a), *geo.px_to_ll(*b))
        out.append(f"{d / NM:.2f} م.ب  {az:03.0f}°")
    return out


def clip_segment(p0, p1, xmin, ymin, xmax, ymax):
    """قصّ قطعة مستقيمة داخل مستطيل (Liang–Barsky). يرجع ((x0,y0),(x1,y1)) أو None"""
    x0, y0 = p0
    x1, y1 = p1
    dx, dy = x1 - x0, y1 - y0
    t0, t1 = 0.0, 1.0
    for pp, qq in ((-dx, x0 - xmin), (dx, xmax - x0), (-dy, y0 - ymin), (dy, ymax - y0)):
        if pp == 0:
            if qq < 0:
                return None
        else:
            r = qq / pp
            if pp < 0:
                if r > t1:
                    return None
                t0 = max(t0, r)
            else:
                if r < t0:
                    return None
                t1 = min(t1, r)
    return (x0 + t0 * dx, y0 + t0 * dy), (x0 + t1 * dx, y0 + t1 * dy)


def gline_label(kind, value):
    """نص خط الطول/العرض بالدرجات والدقائق العشرية: 48°30.000′ E"""
    v = abs(value)
    d = int(v)
    m = (v - d) * 60
    if round(m, 3) >= 60:
        d, m = d + 1, 0.0
    hemi = ("E" if value >= 0 else "W") if kind == "lon" else ("N" if value >= 0 else "S")
    return f"{d}°{m:06.3f}′ {hemi}"


def gline_pts(kind, value, geo, W, H):
    """نقطتا خط الطول (kind='lon') أو العرض (kind='lat') مقصوصتين على حدود صورة الخريطة"""
    if not geo.ok or (kind == "lat" and abs(value) > 85) or (kind == "lon" and abs(value) > 180):
        return None
    lat0, lon0 = geo.px_to_ll(W / 2, H / 2)
    if kind == "lon":
        a = geo.ll_to_px(max(-80.0, lat0 - 20), value)
        b = geo.ll_to_px(min(80.0, lat0 + 20), value)
    else:
        a = geo.ll_to_px(value, lon0 - 20)
        b = geo.ll_to_px(value, lon0 + 20)
    seg = clip_segment(a, b, 0, 0, W, H)
    return [list(seg[0]), list(seg[1])] if seg else None


def type_label(s):
    if s["type"] == "gline":
        return "خط طول" if s.get("kind") == "lon" else "خط عرض"
    return TYPE_NAMES.get(s["type"], s["type"])


def parse_gline_text(text, default_kind="lon"):
    """كل سطر = قيمة خط طول أو عرض:  48°30'E  أو  29.5 N  (الحرف يحدد النوع، وبدونه يُستخدم default_kind)
    يرجع ([(kind, value, النص)], [(رقم السطر, النص, السبب)])"""
    out, errs = [], []
    for i, raw in enumerate((text or "").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        up = line.translate(_TRANS).upper()
        letters = set(re.findall(r"[NSEW]", up))
        if letters & set("NS") and letters & set("EW"):
            errs.append((i, raw.strip(), "السطر يجمع خط طول وخط عرض معاً — اكتب كل واحد في سطر"))
            continue
        kind = default_kind
        if letters & set("NS"):
            kind = "lat"
        elif letters & set("EW"):
            kind = "lon"
        try:
            out.append((kind, _single(line, kind), raw.strip()))
        except Exception as ex:
            errs.append((i, raw.strip(), str(ex) or "قيمة غير مفهومة"))
    return out, errs


def parse_route_text(text):
    """كل سطر = إحداثية بأي صيغة، واختيارياً اسم قبلها:  اسم | إحداثية
    يرجع (نقاط [(اسم, lat, lon)], أخطاء [(رقم السطر, النص, السبب)])"""
    pts, errs = [], []
    for i, raw in enumerate((text or "").splitlines(), 1):
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        mm0 = re.match(r"^\s*\d+\s*[.):]\s+(.*)$", line)               # رقم البند مثل  1)  أو  2.  يُحذف أولاً
        if mm0:
            line = mm0.group(1)
        name = ""
        if "|" in line:
            name, line = [x.strip() for x in line.split("|", 1)]
        try:
            lat, lon = parse_coords(line)
        except Exception as ex:
            lat = None
            mm = re.match(r"^\s*\d+\s*[.)\-:]\s+(.*)$", line)          # ترقيم مثل  1) أو 2.
            if mm:
                try:
                    lat, lon = parse_coords(mm.group(1))
                except Exception:
                    lat = None
            if lat is None and ":" in line and not name:                 # اسم: إحداثية
                nm, rest = line.split(":", 1)
                try:
                    lat, lon = parse_coords(rest)
                    name = nm.strip()
                except Exception:
                    lat = None
            if lat is None:
                errs.append((i, raw.strip(), str(ex) or "صيغة غير مفهومة"))
                continue
        pts.append((name, lat, lon))
    return pts, errs


def route_rows(pts, closed=False):
    """جدول المقاطع: المسافة والاتجاه الحقيقي لكل مقطع والمسافة التراكمية (WGS84)"""
    rows, cum = [], 0.0
    for i, (name, lat, lon) in enumerate(pts):
        if i == 0:
            leg = brg = None
        else:
            leg, brg = geodesic(pts[i - 1][1], pts[i - 1][2], lat, lon)
            cum += leg
        rows.append({"n": str(i + 1), "name": name, "lat": lat, "lon": lon, "leg": leg, "brg": brg, "cum": cum})
    if closed and len(pts) > 2:
        leg, brg = geodesic(pts[-1][1], pts[-1][2], pts[0][1], pts[0][2])
        cum += leg
        rows.append({"n": "↺ 1", "name": pts[0][0], "lat": pts[0][1], "lon": pts[0][2],
                     "leg": leg, "brg": brg, "cum": cum})
    return rows


TOOLS = [
    ("select", "✋", "تحديد / تحريك"),
    ("point", "⌖", "علامة موقع"),
    ("measure", "↔", "قياس مسافة"),
    ("meridian", "│", "خط طول"),
    ("parallel", "─", "خط عرض"),
    ("line", "╱", "خط متعدد"),
    ("polygon", "⬠", "مضلع + مساحة"),
    ("rect", "▭", "مستطيل"),
    ("circle", "◯", "دائرة"),
    ("free", "✎", "رسم حر"),
    ("text", "A", "نص"),
]
TOOL_TIPS = {
    "meridian": "انقر لرسم خط طول (Meridian) يمر بالنقطة ويمتد على كامل الخريطة • Shift = التقريب لأقرب دقيقة • اسحب الخط بأداة التحديد لتحريكه",
    "parallel": "انقر لرسم خط عرض (Parallel) يمر بالنقطة ويمتد على كامل الخريطة • Shift = التقريب لأقرب دقيقة • اسحب الخط بأداة التحديد لتحريكه",
    "select": "انقر لتحديد موقع/عنصر وقفل الإحداثيات عليه • اسحب الفراغ لتحريك الخريطة • عجلة الفأرة للتكبير",
    "point": "انقر لوضع علامة موقع (يُقفل عرض الإحداثيات عليها)",
    "measure": "انقر لإضافة نقاط القياس • نقر مزدوج أو Enter أو زر أيمن للإنهاء",
    "line": "انقر لإضافة نقاط الخط • نقر مزدوج أو Enter أو زر أيمن للإنهاء",
    "polygon": "انقر لإضافة رؤوس المضلع • نقر مزدوج أو Enter أو زر أيمن للإنهاء",
    "rect": "اسحب لرسم مستطيل",
    "circle": "اسحب من المركز إلى الحافة لرسم دائرة",
    "free": "اسحب للرسم الحر",
    "text": "انقر حيث تريد كتابة النص",
    "calib": "انقر على نقطة معروفة الإحداثيات ثم اكتب إحداثياتها (نقطتان على الأقل — والأفضل 3 فأكثر)",
}
TYPE_NAMES = {"gline": "خط طول/عرض", "point": "موقع", "line": "خط", "measure": "قياس", "polygon": "مضلع",
              "rect": "مستطيل", "circle": "دائرة", "free": "رسم حر", "text": "نص"}

HELP_TEXT = """طريقة الاستخدام
─────────────
١) عند تشغيل البرنامج تُفتح خريطة Admiralty 2884 (الكويت) تلقائياً وهي مُعايَرة.
   لفتح خريطة أخرى: ملف ← فتح خريطة أخرى (PNG / JPG / TIF) أو ملف PDF
   (لملفات PDF ثبّت مرة واحدة:  pip install pypdfium2).
   العلامات والرسومات تُحفظ بـ Ctrl+S وتعود تلقائياً في المرة القادمة.

٢) المعايرة (مرة واحدة لكل خريطة):
   • اختر أداة «معايرة الخريطة» ◎
   • انقر على نقطة معروفة الإحداثيات (تقاطع شارع، معلم، شبكة إحداثيات على الخريطة…)
   • اكتب إحداثياتها بأي صيغة، مثل:
        29.3759, 47.9774
        29°22'33.2"N 47°58'38.6"E
        N 29 22.554  E 47 58.644
        38R 789011 3253319      (UTM)
   • كرّر مع نقطة ثانية بعيدة عن الأولى (نقطتان ⇐ خريطة متجهة للشمال،
     ثلاث نقاط فأكثر ⇐ تدعم الدوران ويظهر متوسط الخطأ بالمتر).
   • لقطة من Google/OSM ⇐ «ميركاتور كروي».  خريطة بحرية/Admiralty ⇐ «ميركاتور WGS84».
     خريطة بشبكة طول/عرض منتظمة ⇐ «خطي».  (قائمة معايرة ← نوع الإسقاط)

٣) اللوحة اليسرى تعرض إحداثيات المؤشر مباشرة، والعرض منفصل عن الطول في كل صيغة
   (UTM وMGRS: المنطقة / شرقاً / شمالاً).
   • مربع «متابعة المؤشر مباشرة»: أوقفه لتثبيت القيم. ينطفئ تلقائياً عند النقر على الخريطة
     أو عند وضع المؤشر داخل أي حقل.
   • اكتب إحداثية في أي صف ثم اضغط «اذهب» (أو Enter، أو زر «الذهاب إلى الموقع» أسفل الحقول):
     يعلّم البرنامج الموقع على الخريطة بدائرة بنفسجية ويحدّث بقية الصيغ.
     زر «علامة على هذه النقطة» يحفظها كعلامة دائمة.
   • إذا كان الموقع خارج الخريطة وكان العرض والطول مقلوبين، يقترح عليك البرنامج تبديلهما.
   • في أي حقل: زر الفأرة الأيمن ← لصق / قص / نسخ / تحديد الكل / مسح (وفي «لصق إحداثيات كاملة» أيضاً «لصق وانتقال»).
     اختصارات Ctrl+V / C / X / A تعمل حتى مع لوحة المفاتيح العربية.
   • انقر على اسم الصيغة (مثل DMS) لنسخ القيمتين معاً، أو ⧉ بجانب كل حقل لنسخه وحده.
   • «حجم علامة الموقع»: أزرار ＋ － أو المزلاج لتكبير/تصغير علامة الموقع ونصها وعلاماتك المحفوظة
     (نقرتان على النسبة المئوية تعيدانه إلى 100%).

٤) المسافات بالكيلومتر والميل البحري (م.ب)، وأداة القياس تعرض الاتجاه الحقيقي بالدرجات.
   شريط الأدوات الجانبي: علامات، قياس مسافات، خطوط، مضلعات (مع المساحة)،
   مستطيل، دائرة، رسم حر، نصوص. اللون والسماكة أسفل الشريط.

٥) «لصق إحداثيات كاملة»: الصق نصاً كاملاً بأي صيغة ثم Enter للانتقال إليه.

٥ب) أداتا «│ خط طول» و«─ خط عرض» في الشريط: انقر على الخريطة فيمتد خط الطول (أو العرض) المار بالنقطة
   على كامل الخريطة ويحمل قيمته (48°30.000′ E). معاينة أثناء التحريك، وShift = التقريب لأقرب دقيقة.
   اسحب الخط بأداة التحديد لتحريكه (تتغير قيمته). ولقيم دقيقة: أدوات ← خطوط طول وعرض بقيم محددة.

٦) «مسار من قائمة إحداثيات» (قائمة أدوات، أو زر ⇢ في الشريط، أو زر «مسار من قائمة…»):
   اكتب/الصق عدة إحداثيات، كل واحدة في سطر، فيوصل البرنامج بينها بالترتيب بخط (أو مضلع مغلق)،
   ويرقّم النقاط، ويعرض المسافة (كم / ميل بحري) والاتجاه لكل مقطع وجدولاً بالمجموع.
   لتسمية نقطة:  اسم | إحداثية

٧) حفظ PDF: زر «⬇ حفظ PDF» أو Ctrl+P (أو ملف ← حفظ الخريطة مع العلامات كـ PDF): يحفظ الخريطة
   بكل علاماتك ورسوماتك ومساراتك، مع خيار «المنطقة الظاهرة فقط» وصفحة جدول بالإحداثيات.

٨) تصدير: CSV و KML (Google Earth) و GeoJSON وصورة الخريطة مع الرسومات.

تحريك تلقائي: أثناء الرسم أو القياس أو نقل عنصر، قرّب المؤشر من حافة منطقة الخريطة
(أو اسحب خارجها وأنت ضاغط الزر) فتتحرك الخريطة نحو المنطقة غير الظاهرة والشكل يتبعك.
مع أداة رسم بدون رسم جارٍ يبدأ التحريك بعد لحظة قصيرة. يمكن إيقافه من عرض ← تحريك الخريطة تلقائياً.

اختصارات: Ctrl+O فتح • Ctrl+S حفظ المشروع • Ctrl+Z تراجع • Delete حذف • Esc إلغاء
الفأرة: عجلة = تكبير/تصغير • الزر الأيمن أو الأوسط + سحب = تحريك
"""


# ────────────────────────────────────────────────────────────────────────────
#  4) التطبيق
# ────────────────────────────────────────────────────────────────────────────
# ────────────────────────────────────────────────────────────────────────────
#  تصدير الخريطة مع العلامات (PDF / PNG) — رسم بدقة عالية باستخدام Pillow
# ────────────────────────────────────────────────────────────────────────────
try:
    from PIL import features as _pil_features
    _USE_RAQM = bool(_pil_features.check("raqm"))
except Exception:
    _USE_RAQM = False
try:
    import arabic_reshaper as _arabic_reshaper
    try:
        from bidi import get_display as _bidi_display
    except Exception:
        from bidi.algorithm import get_display as _bidi_display
    _AR_OK = True
except Exception:
    _AR_OK = False
_AR_RE = re.compile(r"[\u0600-\u06FF]")
AR_MISSING = {"hit": False}


def shape_ar(text):
    """يجهّز النص العربي للرسم بـ Pillow (وصل الحروف + الاتجاه)"""
    if not text or not _AR_RE.search(text):
        return text
    if _USE_RAQM:
        return text
    if _AR_OK:
        try:
            return _bidi_display(_arabic_reshaper.reshape(text))
        except Exception:
            return text
    AR_MISSING["hit"] = True
    return text


_FONT_CACHE = {}


def pil_font(px, bold=False):
    px = max(6, int(round(px)))
    key = (px, bold)
    f = _FONT_CACHE.get(key)
    if f is None:
        names = (("tahomabd.ttf", "segoeuib.ttf", "arialbd.ttf", "DejaVuSans-Bold.ttf") if bold
                 else ("tahoma.ttf", "segoeui.ttf", "arial.ttf", "DejaVuSans.ttf"))
        for nm in names:
            try:
                f = ImageFont.truetype(nm, px) if _USE_RAQM else ImageFont.truetype(
                    nm, px, layout_engine=ImageFont.Layout.BASIC)
                break
            except Exception:
                f = None
        if f is None:
            f = ImageFont.load_default()
        _FONT_CACHE[key] = f
    return f


def _draw_text(d, xy, text, font, fill, anchor="sw", halo=True, R=1.0, spacing=1.25):
    x, y = xy
    lines = [shape_ar(ln) for ln in str(text).split("\n")]
    h = "l" if "w" in anchor else ("r" if "e" in anchor else "m")
    v = "d" if "s" in anchor else ("a" if "n" in anchor else "m")
    n = len(lines)
    lh = getattr(font, "size", 12) * spacing
    for i, ln in enumerate(lines):
        if v == "d":
            yy = y - (n - 1 - i) * lh
        elif v == "a":
            yy = y + i * lh
        else:
            yy = y - n * lh / 2 + (i + 0.5) * lh
        kw = {"fill": fill, "font": font, "anchor": h + v}
        if halo:
            kw.update(stroke_width=max(1, int(round(R * 1.3))), stroke_fill="white")
        d.text((x, yy), ln, **kw)


def _dashed(d, pts, dash, gap, fill, width):
    for a, b in zip(pts, pts[1:]):
        L = math.hypot(b[0] - a[0], b[1] - a[1])
        if L == 0:
            continue
        ux, uy = (b[0] - a[0]) / L, (b[1] - a[1]) / L
        pos = 0.0
        while pos < L:
            e = min(pos + dash, L)
            d.line([(a[0] + ux * pos, a[1] + uy * pos), (a[0] + ux * e, a[1] + uy * e)], fill=fill, width=width)
            pos += dash + gap


def _fill_alpha(im, pts, color, alpha):
    xs, ys = [p[0] for p in pts], [p[1] for p in pts]
    x0, y0 = max(0, int(min(xs)) - 1), max(0, int(min(ys)) - 1)
    x1, y1 = min(im.width, int(max(xs)) + 2), min(im.height, int(max(ys)) + 2)
    if x1 <= x0 or y1 <= y0:
        return
    w, h = x1 - x0, y1 - y0
    sc = 1.0 if w * h < 4e6 else 0.25
    mask = Image.new("L", (max(1, int(w * sc)), max(1, int(h * sc))), 0)
    ImageDraw.Draw(mask).polygon([((x - x0) * sc, (y - y0) * sc) for x, y in pts], fill=alpha)
    if sc != 1.0:
        mask = mask.resize((w, h), RS.BILINEAR)
    im.paste(color, (x0, y0, x1, y1), mask)


def render_annotations(im, shapes, geo, box, T, R, k=1.0, target=None, target_dd=""):
    """يرسم كل العلامات والرسومات فوق الصورة im.
    box = المنطقة من الخريطة (بكسلات الأصل) • T = بكسل الإخراج لكل بكسل أصل • R = مقياس حجم الرسومات • k = حجم العلامات"""
    d = ImageDraw.Draw(im)
    bx0, by0 = box[0], box[1]
    tr = lambda p: ((p[0] - bx0) * T, (p[1] - by0) * T)
    fpx = lambda pt, kk=1.0: pt * 1.333 * R * kk
    for s in shapes:
        t, col = s["type"], s["color"]
        w = max(1, int(round(int(s["width"]) * R)))
        P = [tr(p) for p in s["pts"]]
        if not P:
            continue
        if t == "point":
            x, y = P[0]
            r = 8 * k * R
            d.ellipse([x - r, y - r, x + r, y + r], fill="white", outline=col, width=max(2, round(3 * k ** 0.7 * R)))
            r2 = 3 * k * R
            d.ellipse([x - r2, y - r2, x + r2, y + r2], fill=col)
            lw = max(2, round(2 * k ** 0.7 * R))
            d.line([(x - 15 * k * R, y), (x - 9 * k * R, y)], fill=col, width=lw)
            d.line([(x + 9 * k * R, y), (x + 15 * k * R, y)], fill=col, width=lw)
            d.line([(x, y - 15 * k * R), (x, y - 9 * k * R)], fill=col, width=lw)
            d.line([(x, y + 9 * k * R), (x, y + 15 * k * R)], fill=col, width=lw)
            _draw_text(d, (x + 12 * k * R, y - 10 * k * R), s.get("name", ""), pil_font(fpx(9, k), True), col, "sw", R=R)
            continue
        if t == "text":
            _draw_text(d, P[0], s.get("text", ""), pil_font(fpx(10 + 2 * int(s["width"])), True), col, "w", R=R)
            continue
        if t == "gline":
            seg = clip_segment(P[0], P[1], 0, 0, im.width, im.height) if len(P) >= 2 else None
            if seg:
                d.line(list(seg), fill="white", width=w + max(2, int(2 * R)))
                _dashed(d, list(seg), 12 * R, 6 * R, col, w)
                lab = gline_label(s.get("kind", "lon"), s.get("value", 0.0))
                f = pil_font(fpx(10, k), True)
                if s.get("kind") == "lon":
                    top, bot = sorted(seg, key=lambda q: q[1])
                    _draw_text(d, (top[0] + 6 * R, top[1] + 6 * R), lab, f, col, "nw", R=R)
                    _draw_text(d, (bot[0] + 6 * R, bot[1] - 6 * R), lab, f, col, "sw", R=R)
                else:
                    lf, rt = sorted(seg, key=lambda q: q[0])
                    _draw_text(d, (lf[0] + 6 * R, lf[1] - 5 * R), lab, f, col, "sw", R=R)
                    _draw_text(d, (rt[0] - 6 * R, rt[1] - 5 * R), lab, f, col, "se", R=R)
            continue
        lab_pt = P[-1]
        if t in ("line", "measure", "free"):
            if len(P) >= 2:
                if t == "measure":
                    _dashed(d, P, 7 * R, 4 * R, col, w)
                else:
                    d.line(P, fill=col, width=w, joint="curve")
            if t != "free":
                for x, y in P:
                    rr = 3 * R
                    d.ellipse([x - rr, y - rr, x + rr, y + rr], fill="white", outline=col, width=max(1, int(R)))
        elif t == "polygon":
            if len(P) >= 3:
                _fill_alpha(im, P, col, 64)
            d.line(P + ([P[0]] if len(P) >= 3 else []), fill=col, width=w, joint="curve")
            lab_pt = (sum(p[0] for p in P) / len(P), sum(p[1] for p in P) / len(P))
        elif t == "rect" and len(P) >= 2:
            x0_, y0_, x1_, y1_ = P[0][0], P[0][1], P[1][0], P[1][1]
            _fill_alpha(im, [(x0_, y0_), (x1_, y0_), (x1_, y1_), (x0_, y1_)], col, 31)
            d.rectangle([min(x0_, x1_), min(y0_, y1_), max(x0_, x1_), max(y0_, y1_)], outline=col, width=w)
            lab_pt = ((x0_ + x1_) / 2, (y0_ + y1_) / 2)
        elif t == "circle" and len(P) >= 2:
            r = math.hypot(P[1][0] - P[0][0], P[1][1] - P[0][1])
            ring = [(P[0][0] + r * math.cos(2 * math.pi * i / 96), P[0][1] + r * math.sin(2 * math.pi * i / 96)) for i in range(96)]
            _fill_alpha(im, ring, col, 31)
            d.ellipse([P[0][0] - r, P[0][1] - r, P[0][0] + r, P[0][1] + r], outline=col, width=w)
            _dashed(d, [P[0], P[1]], 3 * R, 3 * R, col, max(1, int(R)))
            lab_pt = P[0]
        else:
            continue
        if s.get("vnames") is not None and t in ("line", "polygon") and geo.ok:
            names = s["vnames"]
            if s.get("legs"):
                pairs = list(zip(P, P[1:]))
                if t == "polygon" and len(P) > 2:
                    pairs.append((P[-1], P[0]))
                for (a, b), txt in zip(pairs, route_leg_texts(s, geo)):
                    dx, dy = b[0] - a[0], b[1] - a[1]
                    if math.hypot(dx, dy) / R >= 95 * max(0.7, k):
                        mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
                        f = pil_font(fpx(8, k), True)
                        if abs(dx) >= abs(dy):
                            _draw_text(d, (mx, my - (6 + 3 * k) * R), txt, f, "#0d47a1", "s", R=R)
                        else:
                            _draw_text(d, (mx + (8 + 3 * k) * R, my), txt, f, "#0d47a1", "w", R=R)
            for i, (x, y) in enumerate(P):
                if s.get("vlabels"):
                    r = 10 * k * R
                    d.ellipse([x - r, y - r, x + r, y + r], fill="white", outline=col, width=max(2, int(2 * R)))
                    d.text((x, y), str(i + 1), fill=col, font=pil_font(fpx(9, k), True), anchor="mm")
                if i < len(names) and names[i]:
                    _draw_text(d, (x + 12 * k * R, y - 8 * k * R), names[i], pil_font(fpx(9, k), True), col, "sw", R=R)
        elif t == "measure" or (t in ("line", "polygon", "rect", "circle") and False):
            pass
        if t == "measure":
            txt = shape_metrics_geo(s, geo)
            if txt:
                _draw_text(d, (lab_pt[0] + 10 * R, lab_pt[1] - 8 * R), txt, pil_font(fpx(9), True), "#0d47a1", "sw", R=R)
    if target is not None:
        x, y = tr(target)
        r, arm, gap = 18 * k * R, 40 * k * R, 8 * k * R
        lw = max(2, round(3 * k ** 0.7 * R))
        for colr, ww in (("white", lw + 3), ("#d500f9", lw)):
            d.ellipse([x - r, y - r, x + r, y + r], outline=colr, width=ww)
            for x1, y1, x2, y2 in ((x - arm, y, x - gap, y), (x + gap, y, x + arm, y),
                                   (x, y - arm, x, y - gap), (x, y + gap, x, y + arm)):
                d.line([(x1, y1), (x2, y2)], fill=colr, width=ww)
        rr = 3 * k * R
        d.ellipse([x - rr, y - rr, x + rr, y + rr], fill="#d500f9", outline="white")
        _draw_text(d, (x + r + 8 * R, y - r - 8 * R), "الموقع المحدد\n" + target_dd,
                   pil_font(fpx(10, k), True), "#6a00b8", "sw", R=R)
    return im


def render_table_pages(shapes, geo, title, dpi):
    """صفحات A4 أفقية بجداول: العلامات، المسارات، القياسات"""
    sc = dpi / 150.0
    PW, PH = int(round(1754 * sc)), int(round(1240 * sc))
    M = int(round(60 * sc))
    f_title = pil_font(40 * sc, True)
    f_sub = pil_font(28 * sc, True)
    f_head = pil_font(23 * sc, True)
    f_row = pil_font(22 * sc)
    row_h = int(round(44 * sc))
    pages = []
    state = {}

    def new_page():
        im = Image.new("RGB", (PW, PH), "white")
        state["im"], state["d"], state["y"] = im, ImageDraw.Draw(im), M
        pages.append(im)
        _draw_text(state["d"], (PW - M, state["y"]), title, f_title, "#1e3a5f", "ne", halo=False)
        state["y"] += int(round(70 * sc))

    def need(h):
        if not pages or state["y"] + h > PH - M:
            new_page()

    def cell(x0, x1, y, txt, font, fill="black"):
        _draw_text(state["d"], ((x0 + x1) / 2, y + row_h / 2), txt, font, fill, "c", halo=False)

    def block(block_title, headers, widths, rows):
        need(row_h * 3 + int(round(50 * sc)))
        _draw_text(state["d"], (PW - M, state["y"]), block_title, f_sub, "#0d47a1", "ne", halo=False)
        state["y"] += int(round(50 * sc))
        tw = PW - 2 * M
        xs = [M]
        for wd in widths:
            xs.append(xs[-1] + tw * wd)

        def header():
            d = state["d"]
            d.rectangle([M, state["y"], PW - M, state["y"] + row_h], fill="#e8eef7")
            for i, h in enumerate(headers):
                cell(xs[i], xs[i + 1], state["y"], h, f_head, "#1e3a5f")
            state["y"] += row_h

        header()
        for j, r in enumerate(rows):
            if state["y"] + row_h > PH - M:
                new_page()
                header()
            d = state["d"]
            if j % 2:
                d.rectangle([M, state["y"], PW - M, state["y"] + row_h], fill="#f7f9fc")
            d.line([(M, state["y"] + row_h), (PW - M, state["y"] + row_h)], fill="#d5dbe5", width=max(1, int(sc)))
            for i, c in enumerate(r):
                cell(xs[i], xs[i + 1], state["y"], str(c), f_row)
            state["y"] += row_h
        state["y"] += int(round(36 * sc))

    ddm = lambda la, lo: fmt_ddm(la, lo).split(", ")
    markers = [x for x in shapes if x["type"] == "point"]
    routes = [x for x in shapes if x.get("vnames") is not None and x["type"] in ("line", "polygon")]
    others = [x for x in shapes if x["type"] in ("measure", "line", "polygon", "rect", "circle", "free", "gline")
              and x.get("vnames") is None]
    if markers:
        rows = []
        for i, m in enumerate(markers, 1):
            if geo.ok:
                la, lo = geo.px_to_ll(*m["pts"][0])
                a = format_parts(la, lo)
                d1, d2 = ddm(la, lo)
                rows.append([i, m.get("name", ""), d1, d2, f"{a['utm.zone']} {a['utm.e']} {a['utm.n']}",
                             f"{a['mgrs.sq']} {a['mgrs.e']} {a['mgrs.n']}"])
            else:
                rows.append([i, m.get("name", ""), f"{m['pts'][0][0]:.0f}", f"{m['pts'][0][1]:.0f}", "", ""])
        block("العلامات (المواقع)", ["#", "الاسم", "العرض", "الطول", "UTM", "MGRS"],
              [0.05, 0.21, 0.17, 0.17, 0.20, 0.20], rows)
    for r in routes:
        if not geo.ok:
            continue
        pts = [(r["vnames"][i] if i < len(r["vnames"]) else "", *geo.px_to_ll(*p)) for i, p in enumerate(r["pts"])]
        closed = r["type"] == "polygon"
        rr = route_rows(pts, closed)
        rows = []
        for x in rr:
            la, lo = ddm(x["lat"], x["lon"])
            rows.append([x["n"], x["name"], la, lo,
                         "—" if x["leg"] is None else f"{x['leg'] / NM:.2f}",
                         "—" if x["brg"] is None else f"{x['brg']:.1f}°", f"{x['cum'] / NM:.2f}"])
        tot = rr[-1]["cum"] if rr else 0
        head = f"{'مضلع' if closed else 'مسار'}: {r.get('name', '')}   —   الإجمالي {tot / 1000:.3f} كم ({tot / NM:.2f} م.ب)"
        if closed and len(pts) > 2:
            head += "   —   المساحة " + fmt_area(geo_area([(a, b) for _, a, b in pts])).split("  (")[0]
        block(head, ["#", "الاسم", "العرض", "الطول", "المقطع م.ب", "الاتجاه", "التراكمي م.ب"],
              [0.06, 0.20, 0.18, 0.18, 0.13, 0.11, 0.14], rows)
    if others:
        rows = [[type_label(o), o.get("name", ""),
                 gline_label(o["kind"], o["value"]) if o["type"] == "gline" else shape_metrics_geo(o, geo)] for o in others]
        block("القياسات والرسومات", ["النوع", "الاسم", "التفاصيل"], [0.14, 0.24, 0.62], rows)
    return pages


def export_map_file(path, fmt, base_levels, W, H, shapes, geo, k, box, T, R, target, target_dd,
                    with_table, title, status=None):
    """الدالة التي يستدعيها الخيط الخلفي: تجهّز الصورة وترسم العلامات وتكتب الملف"""
    say = status or (lambda m: None)
    ow, oh = max(1, int(round((box[2] - box[0]) * T))), max(1, int(round((box[3] - box[1]) * T)))
    lk = 0
    while lk < 10 and T * (2 ** (lk + 1)) <= 1.0 + 1e-9:
        lk += 1
    lvl = base_levels(lk)
    sx, sy = lvl.width / W, lvl.height / H
    say("جارٍ تجهيز صورة الخريطة…")
    cb = (box[0] * sx, box[1] * sy, box[2] * sx, box[3] * sy)
    if abs(ow - (cb[2] - cb[0])) < 0.51 and abs(oh - (cb[3] - cb[1])) < 0.51 \
            and all(abs(v - round(v)) < 1e-6 for v in cb):
        im = lvl.crop(tuple(int(round(v)) for v in cb))
        im.load()
    else:
        im = lvl.resize((ow, oh), RS.BICUBIC if T * (2 ** lk) > 1.0 else RS.BILINEAR, box=cb)
    say("جارٍ رسم العلامات والمسارات…")
    render_annotations(im, shapes, geo, box, T, R, k, target, target_dd)
    if fmt == "png":
        say("جارٍ كتابة الملف…")
        im.save(path)
        return
    dpi = 300.0 if ow >= 6000 else 150.0
    pages = [im]
    if with_table and shapes:
        say("جارٍ إنشاء جدول الإحداثيات…")
        pages += render_table_pages(shapes, geo, title, dpi)
    say("جارٍ كتابة ملف PDF…")
    q = 90 if ow >= 6000 else 88
    pages[0].save(path, "PDF", save_all=len(pages) > 1, append_images=pages[1:], resolution=dpi,
                  quality=q, title=title, author="MapCoords")


# ── قراءة ملفات Excel / CSV ───────────────────────────────────────────────────
def _xlsx_col_idx(ref):
    m = re.match(r"([A-Z]+)", ref)
    if not m:
        return 0
    n = 0
    for c in m.group(1):
        n = n * 26 + (ord(c) - ord("A") + 1)
    return n - 1


def _xlsx_read_sheet_rows(zf, sheet_path, strings, ns):
    import xml.etree.ElementTree as ET
    with zf.open(sheet_path) as fh:
        root = ET.parse(fh).getroot()
    rows = []
    for row in root.iter(ns + "row"):
        r = []
        for c in row:
            if c.tag != ns + "c":
                continue
            ref = c.get("r", "")
            ci = _xlsx_col_idx(ref) if ref else len(r)
            while len(r) < ci:
                r.append("")
            t = c.get("t")
            v = c.find(ns + "v")
            is_ = c.find(ns + "is")
            if t == "s" and v is not None:
                try:
                    val = strings[int(v.text)]
                except (ValueError, IndexError, TypeError):
                    val = v.text or ""
            elif t == "inlineStr" and is_ is not None:
                val = "".join((x.text or "") for x in is_.iter(ns + "t"))
            elif t == "b" and v is not None:
                val = "TRUE" if v.text == "1" else "FALSE"
            elif v is not None:
                val = v.text or ""
            else:
                val = ""
            r.append(val)
        rows.append(r)
    return rows


def _split_header_data(rows):
    """يحدّد صف العناوين وأوّل صف بيانات، مُتخطياً الأسطر الفارغة والعناوين المزخرفة."""
    if not rows:
        return [], []
    header_idx = 0
    for i, r in enumerate(rows[:20]):
        if sum(1 for x in r if str(x or "").strip()) >= 2:
            header_idx = i
            break
    headers = [str(h or "").replace("\n", " ").replace("\r", " ").strip()
               for h in rows[header_idx]]
    data = [r for r in rows[header_idx + 1:] if any(str(x or "").strip() for x in r)]
    return headers, data


def parse_xlsx_all(path):
    """يرجع {sheet_name: (headers, rows)} لكل أوراق ملف xlsx."""
    import zipfile
    import xml.etree.ElementTree as ET
    ns = "{http://schemas.openxmlformats.org/spreadsheetml/2006/main}"
    ns_r = "{http://schemas.openxmlformats.org/officeDocument/2006/relationships}"
    result = {}
    with zipfile.ZipFile(path) as z:
        strings = []
        try:
            with z.open("xl/sharedStrings.xml") as fh:
                root = ET.parse(fh).getroot()
            for si in root:
                strings.append("".join((t.text or "") for t in si.iter(ns + "t")))
        except KeyError:
            pass
        sheets = []
        try:
            with z.open("xl/workbook.xml") as fh:
                wb = ET.parse(fh).getroot()
            with z.open("xl/_rels/workbook.xml.rels") as fh:
                rels = {r.get("Id"): r.get("Target") for r in ET.parse(fh).getroot()}
            for sh in wb.iter(ns + "sheet"):
                nm = sh.get("name") or f"Sheet{len(sheets) + 1}"
                rid = sh.get(ns_r + "id")
                tgt = rels.get(rid, "")
                if tgt.startswith("/"):
                    sp = tgt.lstrip("/")           # مسار مطلق داخل ملف zip
                elif tgt.startswith("xl/"):
                    sp = tgt
                else:
                    sp = "xl/" + tgt               # مسار نسبي إلى مجلد xl/
                sheets.append((nm, sp))
        except Exception:
            for n in z.namelist():
                if n.startswith("xl/worksheets/") and n.endswith(".xml"):
                    sheets.append((os.path.basename(n), n))
        if not sheets:
            raise ValueError("لا توجد أوراق داخل الملف")
        for nm, sp in sheets:
            if sp not in z.namelist():
                continue
            rows = _xlsx_read_sheet_rows(z, sp, strings, ns)
            result[nm] = _split_header_data(rows)
    if not result:
        raise ValueError("تعذّر قراءة أي ورقة من الملف")
    return result


def parse_xlsx(path):
    """توافقاً مع الاستدعاءات السابقة: يرجع أول ورقة."""
    all_ = parse_xlsx_all(path)
    first = next(iter(all_.values()))
    return first


def parse_csv_file(path):
    """يرجع (headers, rows) من ملف CSV مع اكتشاف الترميز والفاصل تلقائياً."""
    data = None
    for enc in ("utf-8-sig", "utf-8", "cp1256", "cp1252", "latin-1"):
        try:
            with open(path, "r", encoding=enc, newline="") as fh:
                data = fh.read()
            break
        except UnicodeDecodeError:
            continue
    if data is None:
        raise ValueError("تعذّر فتح الملف بأي ترميز معروف")
    try:
        dialect = csv.Sniffer().sniff(data[:4096], delimiters=",;\t|")
    except csv.Error:
        dialect = csv.excel
    rdr = csv.reader(io.StringIO(data), dialect)
    rows = [r for r in rdr if any((x or "").strip() for x in r)]
    return _split_header_data(rows)


def _xls_to_xlsx_via_excel(xls_path):
    """يحوّل .xls / .xlsb القديم إلى .xlsx مؤقت عبر Excel COM (يتطلب Excel مثبّتاً)."""
    import subprocess
    import tempfile
    fd, out = tempfile.mkstemp(suffix=".xlsx", prefix="mc_conv_")
    os.close(fd)
    try:
        os.remove(out)
    except OSError:
        pass
    env = os.environ.copy()
    env["MC_XLS_IN"] = os.path.abspath(xls_path)
    env["MC_XLS_OUT"] = out
    ps = (
        "$ErrorActionPreference='Stop';"
        "try { $e = New-Object -ComObject Excel.Application } "
        "catch { Write-Error 'EXCEL_NOT_INSTALLED'; exit 2 };"
        "$e.Visible = $false; $e.DisplayAlerts = $false;"
        "try {"
        "  $wb = $e.Workbooks.Open($env:MC_XLS_IN, 0, $true);"
        "  $wb.SaveAs($env:MC_XLS_OUT, 51);"
        "  $wb.Close($false)"
        "} finally {"
        "  $e.Quit();"
        "  [System.Runtime.Interopservices.Marshal]::ReleaseComObject($e) | Out-Null"
        "}"
    )
    try:
        r = subprocess.run(
            ["powershell", "-NoProfile", "-NonInteractive", "-Command", ps],
            env=env, capture_output=True, text=True, timeout=180,
            creationflags=getattr(subprocess, "CREATE_NO_WINDOW", 0))
    except FileNotFoundError:
        raise RuntimeError("لم يتم العثور على PowerShell على النظام.")
    except Exception as ex:
        raise RuntimeError(f"تعذّر تشغيل PowerShell: {ex}")
    if r.returncode != 0 or not os.path.exists(out):
        err = (r.stderr or r.stdout or "").strip()
        if "EXCEL_NOT_INSTALLED" in err or "80040154" in err or "COMException" in err:
            raise RuntimeError("هذه صيغة Excel القديمة (.xls) وتحتاج Microsoft Excel مثبّتاً "
                               "لتحويلها تلقائياً.\nافتح الملف في Excel واحفظه بصيغة .xlsx أو .csv ثم أعد المحاولة.")
        raise RuntimeError("فشل تحويل الملف بواسطة Excel:\n" + (err[:400] or "خطأ غير معروف"))
    return out


def read_coord_file(path):
    """يفتح xlsx / xlsm / xls / xlsb / csv ويرجع {sheet_name: (headers, rows)}."""
    ext = os.path.splitext(path)[1].lower()
    try:
        with open(path, "rb") as fh:
            head = fh.read(8)
    except OSError:
        head = b""
    ole2 = head[:8] == b"\xd0\xcf\x11\xe0\xa1\xb1\x1a\xe1"
    zipped = head[:4] == b"PK\x03\x04"
    if zipped or ext in (".xlsx", ".xlsm"):
        return parse_xlsx_all(path)
    if ole2 or ext in (".xls", ".xlsb"):
        conv = _xls_to_xlsx_via_excel(path)
        try:
            return parse_xlsx_all(conv)
        finally:
            try:
                os.remove(conv)
            except OSError:
                pass
    h, r = parse_csv_file(path)
    return {"CSV": (h, r)}


def _num_or_none(v):
    try:
        return float(str(v).replace(",", ".").translate(_TRANS))
    except Exception:
        return None


def detect_compound_dms(headers, sample_rows, lat_i, lon_i):
    """يكتشف صيغة DDM/DMS المركّبة (درجات + دقائق + [ثوان] + N/S) عند فهارس lat/lon.
    يرجع 'dmm' أو 'dms' أو None."""
    if lat_i < 0 or lon_i < 0 or not sample_rows:
        return None
    hem_lat = ("N", "S")
    hem_lon = ("E", "W")

    def try_len(n, hem_set, base_i):
        """يجرّب: تكامل الدرجات + (n-1) قيم رقمية + رمز الاتجاه.
        يتخطّى الصفوف الفارغة ويشترط أن يمرّ صفّ واحد على الأقل بلا مخالفات."""
        passed = 0
        for r in sample_rows:
            if base_i + n > len(r):
                continue
            deg_v = r[base_i]
            if str(deg_v or "").strip() == "":
                continue  # صف مفقود القيمة الرئيسية — تجاهل
            deg = _num_or_none(deg_v)
            if deg is None or abs(deg) > 180:
                return False
            vals_ok = True
            for off in range(1, n - 1):
                mn = _num_or_none(r[base_i + off])
                if mn is None or mn < 0 or mn >= 60:
                    vals_ok = False
                    break
            if not vals_ok:
                return False
            hem = str(r[base_i + n - 1] or "").strip().upper()
            if hem not in hem_set:
                return False
            passed += 1
            if passed >= 3:
                break
        if passed == 0:
            return False
        # العناوين المتوسّطة فارغة أو مكوّنات DMS
        for off in range(1, n):
            if base_i + off < len(headers):
                h = str(headers[base_i + off] or "").strip().lower()
                if h and not any(k in h for k in ("min", "sec", "deg", "n/s", "e/w",
                                                   "درجة", "دقيقة", "ثانية", "hem")):
                    return False
        return True

    # DMS = 4 أعمدة (deg, min, sec, hem)، DMM = 3 (deg, min, hem)
    for n in (4, 3):
        if try_len(n, hem_lat, lat_i) and try_len(n, hem_lon, lon_i):
            return "dms" if n == 4 else "dmm"
    return None


def parse_compound_row(r, base_i, mode, is_lat):
    """يبني قيمة عرض/طول عشرية من الأعمدة المركّبة."""
    deg = _num_or_none(r[base_i])
    if deg is None:
        raise ValueError("درجات غير صحيحة")
    if mode == "dmm":
        mn = _num_or_none(r[base_i + 1]) or 0.0
        sc = 0.0
        hem = str(r[base_i + 2] or "").strip().upper()
    else:  # dms
        mn = _num_or_none(r[base_i + 1]) or 0.0
        sc = _num_or_none(r[base_i + 2]) or 0.0
        hem = str(r[base_i + 3] or "").strip().upper()
    val = abs(deg) + mn / 60.0 + sc / 3600.0
    if is_lat and hem == "S":
        val = -val
    elif (not is_lat) and hem == "W":
        val = -val
    elif deg < 0:
        val = -val
    return val


def score_sheet_for_coords(headers, rows):
    """يعطي رقماً يمثّل مدى ملاءمة الورقة كمصدر إحداثيات — لاختيار الورقة الافتراضية."""
    if not rows:
        return 0
    d = detect_coord_cols(headers)
    compound = detect_compound_dms(headers, rows[:40], d["lat"], d["lon"])
    ok = 0
    for r in rows[:200]:
        try:
            if d["full"] >= 0 and d["full"] < len(r):
                parse_coords(str(r[d["full"]]))
                ok += 1
                continue
            if compound and d["lat"] >= 0 and d["lon"] >= 0:
                la = parse_compound_row(r, d["lat"], compound, True)
                lo = parse_compound_row(r, d["lon"], compound, False)
                if abs(la) <= 90 and abs(lo) <= 180:
                    ok += 1
                continue
            if d["lat"] >= 0 and d["lon"] >= 0 and d["lat"] < len(r) and d["lon"] < len(r):
                la = _num_or_none(r[d["lat"]])
                lo = _num_or_none(r[d["lon"]])
                if la is not None and lo is not None and abs(la) <= 90 and abs(lo) <= 180:
                    if abs(la) >= 1 or abs(lo) >= 1:
                        ok += 1
        except Exception:
            pass
    return ok


def detect_coord_cols(headers):
    """يرشّح أعمدة الاسم/العرض/الطول/الإحداثي الكامل بنظام تنقيط."""
    hn = [((h or "").strip().lower()) for h in headers]
    # كلمات تدلّ على مكوّن DMS جزئي فقط — نتجنّبها كعمود إحداثي رئيسي
    dms_bad = ("deg", "degree", "degrees", "min", "minute", "minutes",
               "sec", "second", "seconds", "درجة", "دقيقة", "ثانية",
               "n/s", "e/w", "hem", "hemisphere")

    def has_dms_bad(h):
        return any(w in h for w in dms_bad)

    def score_lat(h):
        if not h or has_dms_bad(h):
            return 0
        if h in ("lat", "latitude", "خط العرض"):
            return 100
        if "latitude" in h and ("dd" in h or "decimal" in h or "عشري" in h):
            return 95
        if "عرض" in h and ("dd" in h or "decimal" in h or "عشري" in h):
            return 95
        if "latitude" in h or "خط العرض" in h:
            return 80
        if re.search(r"\blat\b", h):
            return 70
        if "عرض" in h:
            return 60
        if h.startswith("lat"):
            return 40
        if h == "y":
            return 30
        return 0

    def score_lon(h):
        if not h or has_dms_bad(h):
            return 0
        if h in ("lon", "lng", "long", "longitude", "خط الطول"):
            return 100
        if "longitude" in h and ("dd" in h or "decimal" in h or "عشري" in h):
            return 95
        if "طول" in h and ("dd" in h or "decimal" in h or "عشري" in h):
            return 95
        if "longitude" in h or "خط الطول" in h:
            return 80
        if re.search(r"\b(lon|lng|long)\b", h):
            return 70
        if "طول" in h:
            return 60
        if h.startswith("lon") or h.startswith("lng") or h.startswith("long"):
            return 40
        if h == "x":
            return 30
        return 0

    def score_full(h):
        if not h:
            return 0
        for w in ("coord", "coordinate", "coordinates", "إحداثي", "احداثي",
                  "إحداثيات", "احداثيات", "wkt"):
            if w in h:
                return 80
        for w in ("position",):
            if w in h:
                return 40
        return 0

    def score_name(h):
        if not h:
            return 0
        if h in ("name", "اسم", "الاسم"):
            return 100
        if "name" in h or "اسم" in h:
            return 80
        if h in ("label", "title", "comment", "description", "وصف", "تعليق"):
            return 60
        if "label" in h or "title" in h:
            return 55
        if "comment" in h or "description" in h or "وصف" in h or "تعليق" in h:
            return 50
        if h in ("id", "point", "نقطة", "site", "location", "موقع", "station", "محطة"):
            return 40
        if "location" in h or "موقع" in h:
            return 35
        if "id" in h:
            return 25
        return 0

    # عند تكرار العناوين، فضّل الأولى (الأقرب لبداية الجدول)

    def best(scorer, exclude=()):
        scored = [(i, scorer(h)) for i, h in enumerate(hn)]
        scored = [(i, s) for i, s in scored if s > 0 and i not in exclude]
        if not scored:
            return -1
        scored.sort(key=lambda x: (-x[1], x[0]))
        return scored[0][0]

    lat = best(score_lat)
    lon = best(score_lon)
    full = best(score_full, exclude=(lat, lon))
    name = best(score_name, exclude=(lat, lon, full))
    return {"name": name, "lat": lat, "lon": lon, "full": full}


# ── التحقق من التحديثات (GitHub Releases) ────────────────────────────────────
def _parse_ver(s):
    """يحوّل 'v1.2.3' أو '1.2.3.4' إلى tuple من أعداد صحيحة للمقارنة."""
    s = re.sub(r"[^\d.]", "", str(s or "0"))
    parts = [p for p in s.split(".") if p]
    try:
        return tuple(int(p) for p in parts) if parts else (0,)
    except ValueError:
        return (0,)


def _is_newer_version(remote, local):
    return _parse_ver(remote) > _parse_ver(local)


def _https_context():
    """يبني SSL context موثوقاً بشهادات — يفضّل certifi، وإلا نظام التشغيل."""
    import ssl
    try:
        import certifi
        return ssl.create_default_context(cafile=certifi.where())
    except ImportError:
        pass
    try:
        import truststore
        return truststore.SSLContext(ssl.PROTOCOL_TLS_CLIENT)
    except ImportError:
        pass
    return ssl.create_default_context()


def _https_open(url, timeout=8):
    import urllib.request
    req = urllib.request.Request(url, headers={
        "User-Agent": f"MapCoords/{APP_VERSION}",
        "Accept": "application/vnd.github+json",
    })
    return urllib.request.urlopen(req, timeout=timeout, context=_https_context())


def check_for_update(timeout=8):
    """يستفسر GitHub Releases عن آخر إصدار. يرجع dict عند وجود تحديث، وإلا None.
    يرمي استثناء عند فشل الاتصال."""
    if not UPDATE_OWNER or "your-github-username" in UPDATE_OWNER:
        raise RuntimeError("لم يُضبط اسم مستودع GitHub في UPDATE_OWNER / UPDATE_REPO داخل الكود.")
    import json
    url = f"https://api.github.com/repos/{UPDATE_OWNER}/{UPDATE_REPO}/releases/latest"
    with _https_open(url, timeout=timeout) as resp:
        data = json.load(resp)
    tag = data.get("tag_name", "")
    if not _is_newer_version(tag, APP_VERSION):
        return None
    asset = None
    for a in data.get("assets", []):
        if (a.get("name") or "").lower() == UPDATE_ASSET_NAME.lower():
            asset = a
            break
    if asset is None:
        raise RuntimeError(f"لا يوجد ملف باسم {UPDATE_ASSET_NAME} في آخر Release.")
    return {
        "version": tag.lstrip("vV"),
        "notes": (data.get("body") or "").strip(),
        "url": asset.get("browser_download_url"),
        "name": asset.get("name"),
        "size": int(asset.get("size") or 0),
    }


class App:
    def __init__(self, root):
        self.root = root
        root.title(APP_TITLE)
        root.geometry("1440x860")
        root.minsize(1150, 660)
        try:
            root.state("zoomed")          # ملء الشاشة على ويندوز
        except Exception:
            pass

        self.img = None
        self.img_path = None
        self.tkimg = None
        self.zoom = 1.0
        self.off = [0.0, 0.0]
        self.geo = GeoRef()
        self.shapes = []
        self.next_id = 1
        self.undo_stack = []
        self.sel = None
        self.cur = None
        self.color = "#e53935"
        self.width = tk.IntVar(value=3)
        self.tool = tk.StringVar(value="select")
        self.proj = tk.StringVar(value="web")
        self.locked = False
        self.last_px = None
        self.cursor_s = None
        self._pan = None
        self._drag = None
        self._dragging_draw = False
        self._redraw_pending = False
        self._sync = False
        self.auto_fit = True
        self.dirty = False
        self.pyr = []
        self.field_vars = {k: tk.StringVar() for k in ALL_KEYS}
        self.track_var = tk.BooleanVar(value=True)
        self.target = None
        self.target_label = ""
        self._coord_file_win = None
        self._update_info = None
        self._update_btn = None
        self._update_dialog = None
        self.edit_row = None
        self.mark_scale = tk.DoubleVar(value=1.0)
        self.autopan_var = tk.BooleanVar(value=True)
        self._leg_cache = {}
        self._export_busy = False
        self._route_win = None
        self.win_keys = sys.platform.startswith("win")
        self._edge_since = None
        self._rpan = None
        self.edit_field = {}

        self.build_menu()
        self.build_ui()
        root.protocol("WM_DELETE_WINDOW", self.on_close)
        self.bind_keys()
        self.tool.trace_add("write", lambda *a: self.on_tool_change())
        self.on_tool_change()
        self.root.after(300, self.edge_tick)
        self.update_calib_label()
        self.show_coords(None)
        # افحص التحديثات في الخلفية بعد ثوانٍ من الإقلاع (فشل الشبكة صامت)
        self.root.after(3500, self._start_update_check_bg)

    # ── القوائم ────────────────────────────────────────────────────────────
    def build_menu(self):
        m = tk.Menu(self.root)
        f = tk.Menu(m, tearoff=0)
        f.add_command(label="الخريطة المدمجة: Admiralty 2884 (الكويت)", command=self.open_default_map)
        f.add_command(label="فتح خريطة أخرى (صورة أو PDF)…", accelerator="Ctrl+O", command=self.open_image_dialog)
        f.add_command(label="فتح مشروع…", command=self.load_project_dialog)
        f.add_command(label="فتح ملف إحداثيات (Excel / CSV)…", accelerator="Ctrl+E",
                      command=self.open_coord_file_dialog)
        f.add_command(label="حفظ المشروع", accelerator="Ctrl+S", command=self.save_project)
        f.add_command(label="حفظ الخريطة مع العلامات كـ PDF…", accelerator="Ctrl+P", command=self.save_pdf)
        f.add_separator()
        ex = tk.Menu(f, tearoff=0)
        ex.add_command(label="جدول النقاط CSV", command=self.export_csv)
        ex.add_command(label="KML (Google Earth)", command=self.export_kml)
        ex.add_command(label="GeoJSON", command=self.export_geojson)
        ex.add_command(label="الخريطة مع الرسومات كـ PDF…", command=self.save_pdf)
        ex.add_command(label="الخريطة مع الرسومات كصورة PNG…", command=self.export_png)
        f.add_cascade(label="تصدير", menu=ex)
        f.add_separator()
        f.add_command(label="خروج", command=self.root.destroy)
        m.add_cascade(label="ملف", menu=f)

        e = tk.Menu(m, tearoff=0)
        e.add_command(label="تراجع", accelerator="Ctrl+Z", command=self.undo)
        e.add_command(label="حذف المحدد", accelerator="Del", command=self.delete_selected)
        e.add_command(label="مسح كل الرسومات", command=self.clear_all)
        m.add_cascade(label="تحرير", menu=e)

        v = tk.Menu(m, tearoff=0)
        v.add_command(label="ملاءمة الشاشة", accelerator="F", command=self.fit_view)
        v.add_command(label="تكبير", accelerator="+", command=lambda: self.zoom_by(1.4))
        v.add_command(label="تصغير", accelerator="-", command=lambda: self.zoom_by(1 / 1.4))
        v.add_command(label="حجم 100%", command=lambda: self.zoom_to(1.0))
        v.add_separator()
        v.add_checkbutton(label="تحريك الخريطة تلقائياً عند اقتراب المؤشر من الحافة", variable=self.autopan_var)
        m.add_cascade(label="عرض", menu=v)

        tl = tk.Menu(m, tearoff=0)
        tl.add_command(label="مسار من قائمة إحداثيات…", command=self.open_route_dialog)
        tl.add_command(label="خطوط طول وعرض بقيم محددة…", command=self.open_gline_dialog)
        m.add_cascade(label="أدوات", menu=tl)

        c = tk.Menu(m, tearoff=0)
        c.add_command(label="بدء المعايرة", command=lambda: self.tool.set("calib"))
        c.add_command(label="حذف آخر نقطة معايرة", command=self.calib_undo)
        c.add_command(label="مسح المعايرة", command=self.calib_clear)
        c.add_separator()
        c.add_radiobutton(label="ميركاتور كروي (لقطات Google / OSM)", variable=self.proj,
                          value="web", command=self.on_proj_change)
        c.add_radiobutton(label="ميركاتور WGS84 بيضاوي (الخرائط البحرية / Admiralty)", variable=self.proj,
                          value="wgs84", command=self.on_proj_change)
        c.add_radiobutton(label="إسقاط خطي (شبكة طول/عرض منتظمة)", variable=self.proj,
                          value="linear", command=self.on_proj_change)
        m.add_cascade(label="معايرة", menu=c)

        h = tk.Menu(m, tearoff=0)
        h.add_command(label="طريقة الاستخدام", command=self.show_help)
        h.add_separator()
        h.add_command(label="بحث عن تحديث الآن…", command=self.check_update_manual)
        h.add_command(label=f"الإصدار الحالي: {APP_VERSION}", state="disabled")
        m.add_cascade(label="مساعدة", menu=h)
        self.root.config(menu=m)

    # ── الواجهة ────────────────────────────────────────────────────────────
    def build_ui(self):
        # شريط الحالة
        sb = tk.Frame(self.root, bd=1, relief="sunken")
        sb.pack(side="bottom", fill="x")
        self.status_bar = sb
        self.st_tip = tk.Label(sb, anchor="e", justify="right")
        self.st_tip.pack(side="right", padx=8)
        self.st_zoom = tk.Label(sb, anchor="w", width=34)
        self.st_zoom.pack(side="left", padx=8)
        # مؤشّر الإصدار — يستبدله زرّ تحديث ملوّن عند توفّر تحديث
        self.st_version = tk.Label(sb, anchor="w", text=f"v{APP_VERSION}", fg="#78909c",
                                   font=("Segoe UI", 8))
        self.st_version.pack(side="left", padx=4)

        main = tk.Frame(self.root)
        main.pack(fill="both", expand=True)

        # ─ شريط الأدوات الجانبي ─
        tb = tk.Frame(main, bg="#2b2f36", width=138)
        tb.pack(side=TOOLBAR_SIDE, fill="y")
        tb.pack_propagate(False)
        tk.Label(tb, text="الأدوات", bg="#2b2f36", fg="#9aa4b2", font=("Segoe UI", 9, "bold")).pack(pady=(8, 2))
        for key, icon, label in TOOLS:
            tk.Radiobutton(
                tb, text=f"{icon}  {label}", variable=self.tool, value=key, indicatoron=False,
                height=1, font=("Segoe UI", 9), bg="#3a3f47", fg="white",
                selectcolor="#1e88e5", activebackground="#4a505a", activeforeground="white",
                bd=0, relief="flat", cursor="hand2",
            ).pack(fill="x", padx=6, pady=2, ipady=3)

        tk.Frame(tb, height=1, bg="#555b66").pack(fill="x", padx=6, pady=6)
        self.color_btn = tk.Button(tb, text="اللون", bg=self.color, fg="white", bd=0,
                                   command=self.pick_color, cursor="hand2", font=("Segoe UI", 9, "bold"))
        self.color_btn.pack(fill="x", padx=6, pady=(0, 4))
        row = tk.Frame(tb, bg="#2b2f36")
        row.pack(fill="x", padx=6)
        tk.Label(row, text="السماكة", bg="#2b2f36", fg="#c5ccd6", font=("Segoe UI", 9)).pack(side="right")
        tk.Spinbox(row, from_=1, to=12, textvariable=self.width, width=4).pack(side="left")

        tk.Frame(tb, height=1, bg="#555b66").pack(fill="x", padx=6, pady=6)
        for txt, cmd in (("↶  تراجع", self.undo), ("✖  حذف المحدد", self.delete_selected),
                         ("⇢  مسار من قائمة", self.open_route_dialog),
                         ("⬇  حفظ PDF", self.save_pdf),
                         ("┼  خطوط بقيم", self.open_gline_dialog),
                         ("⤢  ملاءمة الشاشة", self.fit_view),
                         ("＋  تكبير", lambda: self.zoom_by(1.4)),
                         ("－  تصغير", lambda: self.zoom_by(1 / 1.4))):
            tk.Button(tb, text=txt, command=cmd, bg="#454b55", fg="white", bd=0,
                      activebackground="#5a616d", activeforeground="white", cursor="hand2",
                      font=("Segoe UI", 9)).pack(fill="x", padx=6, pady=2)

        # ─ لوحة الإحداثيات (يسار) ─
        info_side = "left" if TOOLBAR_SIDE == "right" else "right"
        info = ttk.Frame(main, width=590)
        info.pack(side=info_side, fill="y")
        info.pack_propagate(False)

        lf = ttk.LabelFrame(info, text=" الإحداثيات ")
        lf.pack(fill="x", padx=6, pady=(6, 4))
        top = ttk.Frame(lf)
        top.pack(fill="x", padx=6, pady=(2, 0))
        ttk.Checkbutton(top, text="متابعة المؤشر مباشرة", variable=self.track_var,
                        command=self.on_track_toggle).pack(side="right")
        self.lock_lbl = tk.Label(top, text="", anchor="w", font=("Segoe UI", 9, "bold"))
        self.lock_lbl.pack(side="left", fill="x", expand=True)
        grid = ttk.Frame(lf)
        grid.pack(fill="x", padx=6, pady=2)
        self.build_fields(grid)
        self.field_msg = tk.Label(lf, text="اكتب في أي حقل ثم اضغط «اذهب» أو Enter لإظهار الموقع على الخريطة • انقر اسم الصيغة لنسخ القيمتين معاً",
                                  anchor="e", justify="right", wraplength=540, font=("Segoe UI", 8), fg="#6b7280")
        self.field_msg.pack(fill="x", padx=6)
        btns = ttk.Frame(lf)
        btns.pack(fill="x", padx=6, pady=(2, 6))
        ttk.Button(btns, text="◎  الذهاب إلى الموقع", command=self.go_last).pack(side="right", padx=2)
        ttk.Button(btns, text="＋ علامة على هذه النقطة", command=self.add_marker_here).pack(side="right", padx=2)
        ttk.Button(btns, text="نسخ الكل", command=self.copy_all).pack(side="right", padx=2)

        sz = ttk.Frame(lf)
        sz.pack(fill="x", padx=6, pady=(0, 6))
        ttk.Label(sz, text="حجم علامة الموقع", font=("Segoe UI", 9, "bold")).pack(side="right", padx=(4, 6))
        ttk.Button(sz, text="＋", width=3, command=lambda: self.change_mark_size(1.25)).pack(side="right")
        ttk.Scale(sz, from_=0.4, to=5.0, orient="horizontal", variable=self.mark_scale).pack(
            side="right", fill="x", expand=True, padx=4)
        ttk.Button(sz, text="－", width=3, command=lambda: self.change_mark_size(1 / 1.25)).pack(side="right")
        self.mark_pct = ttk.Label(sz, text="100%", width=5, anchor="e", cursor="hand2")
        self.mark_pct.pack(side="left")
        self.mark_pct.bind("<Double-Button-1>", lambda e: self.mark_scale.set(1.0))
        self.mark_scale.trace_add("write", lambda *a: self.on_mark_scale())

        gf = ttk.LabelFrame(info, text=" لصق إحداثيات كاملة (أي صيغة) ")
        gf.pack(fill="x", padx=6, pady=4)
        self.goto_var = tk.StringVar()
        ge = ttk.Entry(gf, textvariable=self.goto_var, font=("Consolas", 10))
        ge.pack(side="right", fill="x", expand=True, padx=6, pady=6)
        ge.bind("<Return>", lambda e: self.goto_coords())
        ge.bind("<FocusIn>", lambda e: self.on_field_focus())
        self.enable_edit_menu(ge, paste_go=self.goto_coords)
        ttk.Button(gf, text="انتقال", command=self.goto_coords).pack(side="left", padx=6)
        ttk.Button(gf, text="مسار من قائمة…", command=self.open_route_dialog).pack(side="left", padx=2)

        cf = ttk.LabelFrame(info, text=" المعايرة ")
        cf.pack(fill="x", padx=6, pady=4)
        self.calib_lbl = tk.Label(cf, anchor="e", justify="right", wraplength=540)
        self.calib_lbl.pack(fill="x", padx=6, pady=4)

        tf = ttk.LabelFrame(info, text=" العناصر على الخريطة ")
        tf.pack(fill="both", expand=True, padx=6, pady=(4, 6))
        cols = ("type", "name", "info")
        self.tree = ttk.Treeview(tf, columns=cols, show="headings", height=6, selectmode="browse")
        for c, t, w in (("type", "النوع", 70), ("name", "الاسم", 110), ("info", "التفاصيل", 270)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="w")
        sc = ttk.Scrollbar(tf, orient="vertical", command=self.tree.yview)
        self.tree.configure(yscrollcommand=sc.set)
        bb = ttk.Frame(tf)
        bb.pack(side="bottom", fill="x", pady=2)
        ttk.Button(bb, text="حذف", command=self.delete_selected).pack(side="right", padx=2)
        ttk.Button(bb, text="إعادة تسمية", command=self.rename_selected).pack(side="right", padx=2)
        ttk.Button(bb, text="تكبير إليه", command=self.zoom_to_selected).pack(side="right", padx=2)
        sc.pack(side="left", fill="y")
        self.tree.pack(side="right", fill="both", expand=True)
        self.tree.bind("<<TreeviewSelect>>", self.on_tree_select)
        self.tree.bind("<Double-1>", lambda e: self.rename_selected())

        # ─ لوحة الخريطة ─
        self.canvas = tk.Canvas(main, bg="#20242b", highlightthickness=0)
        self.canvas.pack(side="left", fill="both", expand=True)
        c = self.canvas
        c.bind("<Configure>", self.on_configure)
        c.bind("<Motion>", self.on_motion)
        c.bind("<Leave>", lambda e: c.delete("glprev"))
        c.bind("<ButtonPress-1>", self.on_press)
        c.bind("<B1-Motion>", self.on_drag)
        c.bind("<ButtonRelease-1>", self.on_release)
        c.bind("<Double-Button-1>", self.on_double)
        c.bind("<ButtonPress-3>", self.on_rpress)
        c.bind("<B3-Motion>", self.on_pan_move)
        c.bind("<ButtonRelease-3>", self.on_pan_end)
        c.bind("<ButtonPress-2>", self.on_pan_start)
        c.bind("<B2-Motion>", self.on_pan_move)
        c.bind("<ButtonRelease-2>", self.on_pan_end)
        c.bind("<MouseWheel>", self.on_wheel)
        c.bind("<Button-4>", lambda e: self.wheel_zoom(e, 1))
        c.bind("<Button-5>", lambda e: self.wheel_zoom(e, -1))

    def build_fields(self, parent):
        for row, title, cells in FIELD_ROWS:
            fr = ttk.Frame(parent)
            fr.pack(fill="x", pady=1)
            n = len(cells)
            t = tk.Label(fr, text=title, anchor="e", font=("Segoe UI", 9, "bold"), fg="#1e3a5f",
                         cursor="hand2", width=12)
            t.grid(row=0, column=n + 1, sticky="e", padx=(4, 0))
            t.bind("<Button-1>", lambda e, r=row: self.copy_row(r))
            fr.columnconfigure(n + 1, weight=0)
            fr.columnconfigure(0, weight=0)
            ttk.Button(fr, text="اذهب", width=5, command=lambda r=row: self.go_row(r)
                       ).grid(row=0, column=0, sticky="s", padx=(2, 0))
            for i, (key, cap, w) in enumerate(cells):
                col = n - i
                fr.columnconfigure(col, weight=w, uniform=f"c{row}")
                cell = ttk.Frame(fr)
                cell.grid(row=0, column=col, sticky="ew", padx=2)
                ttk.Label(cell, text=cap, font=("Segoe UI", 8), foreground="#6b7280", anchor="e").pack(fill="x")
                line = ttk.Frame(cell)
                line.pack(fill="x")
                fk = f"{row}.{key}"
                ent = ttk.Entry(line, textvariable=self.field_vars[fk], font=("Consolas", 10), width=4)
                ent.pack(side="right", fill="x", expand=True)
                ent.bind("<Return>", lambda e, r=row, k=key: self.apply_typed(r, k))
                ent.bind("<FocusIn>", lambda e: self.on_field_focus(e.widget))
                for ev in ("<Key>", "<<Paste>>", "<<Cut>>"):
                    ent.bind(ev, lambda e, r=row, k=key: self.mark_edit(e, r, k), add="+")
                self.enable_edit_menu(ent, on_edit=lambda r=row, k=key: self.note_edit(r, k))
                ttk.Button(line, text="⧉", width=2, command=lambda k=fk: self.copy_field(k)).pack(side="left")

    def on_configure(self, e):
        if self.img is not None and self.auto_fit:
            self.fit_view()
        else:
            self.request_redraw()

    def bind_keys(self):
        r = self.root
        r.bind("<Control-o>", lambda e: self.open_image_dialog())
        r.bind("<Control-s>", lambda e: self.save_project())
        r.bind("<Control-p>", lambda e: self.save_pdf())
        r.bind("<Control-e>", lambda e: self.open_coord_file_dialog())
        r.bind("<Control-z>", lambda e: self.undo())
        r.bind("<Delete>", lambda e: self.delete_selected())
        r.bind("<Escape>", lambda e: self.cancel_cur())
        r.bind("<Return>", lambda e: self.finish_cur() if self.root.focus_get() is self.canvas else None)
        r.bind("f", lambda e: self.fit_view() if self.root.focus_get() is self.canvas else None)
        r.bind("+", lambda e: self.zoom_by(1.4) if self.root.focus_get() is self.canvas else None)
        r.bind("-", lambda e: self.zoom_by(1 / 1.4) if self.root.focus_get() is self.canvas else None)

    # ── تحويلات ───────────────────────────────────────────────────────────
    def i2s(self, x, y):
        return x * self.zoom + self.off[0], y * self.zoom + self.off[1]

    def s2i(self, sx, sy):
        return (sx - self.off[0]) / self.zoom, (sy - self.off[1]) / self.zoom

    # ── فتح الصور والمشاريع ───────────────────────────────────────────────
    def open_default_map(self):
        p = resource_path(DEFAULT_MAP)
        if os.path.isfile(p):
            self.open_image(p)
        else:
            messagebox.showinfo("تنبيه", f"ملف الخريطة المدمجة غير موجود:\n{p}")

    def is_bundled(self, path):
        return bool(path) and os.path.abspath(path) == os.path.abspath(resource_path(DEFAULT_MAP))

    def project_path(self, path=None):
        path = path or self.img_path
        if self.is_bundled(path):
            return os.path.join(user_data_dir(), os.path.basename(path) + ".mapproj")
        return path + ".mapproj"

    def on_close(self):
        if self.dirty and (self.shapes or self.geo.pts):
            r = messagebox.askyesnocancel("حفظ", "هل تريد حفظ العلامات والرسومات قبل الخروج؟")
            if r is None:
                return
            if r:
                self.save_project()
        self.root.destroy()

    def open_image_dialog(self):
        p = filedialog.askopenfilename(
            title="اختر صورة الخريطة",
            filetypes=[("خرائط (صور / PDF)", "*.png *.jpg *.jpeg *.bmp *.tif *.tiff *.webp *.gif *.pdf"), ("كل الملفات", "*.*")])
        if p:
            self.open_image(p)

    def open_image(self, path):
        self.root.config(cursor="watch")
        self.canvas.delete("all")
        self.canvas.create_text(self.canvas.winfo_width() / 2, self.canvas.winfo_height() / 2,
                                text="جارٍ تحميل الخريطة…", fill="#9aa4b2", font=("Segoe UI", 16))
        self.root.update()
        try:
            self.img = load_image_any(path)
        except Exception as ex:
            self.root.config(cursor="")
            messagebox.showerror("خطأ", f"تعذّر فتح الملف:\n{ex}")
            return
        self.root.config(cursor="")
        self.pyr = [self.img]
        self.img_path = path
        self.shapes = []
        self.next_id = 1
        self.undo_stack = []
        self.sel = None
        self.cur = None
        self.geo = GeoRef()
        self.geo.mode = self.proj.get()
        self.locked = False
        self.target = None
        self.track_var.set(True)
        side = self.project_path(path)
        if os.path.isfile(side) and (self.is_bundled(path) or messagebox.askyesno(
                "مشروع محفوظ", "وُجد مشروع محفوظ لهذه الخريطة (معايرة ورسومات). هل تريد تحميله؟")):
            try:
                self.load_project(side, reopen=False)
            except Exception as ex:
                messagebox.showerror("خطأ", f"تعذّر تحميل المشروع:\n{ex}")
        self.root.title(f"{APP_TITLE} — {os.path.basename(path)}")
        if not self.geo.ok:
            self.try_preset()
        self.dirty = False
        self.refresh_tree()
        self.update_calib_label()
        self.root.update_idletasks()
        self.fit_view()
        self.show_coords(None)

    def try_preset(self):
        for pr in PRESETS:
            if tuple(pr["size"]) == self.img.size:
                self.geo = GeoRef()
                self.geo.mode = pr["proj"]
                self.proj.set(pr["proj"])
                self.geo.pts = [tuple(p) for p in pr["calib"]]
                self.geo.fit()
                self.tip("تم التعرف على الخريطة وعُويرت تلقائياً: " + pr["name"])
                return True
        return False

    def project_dict(self):
        return {"version": 1, "image": self.img_path, "proj": self.geo.mode,
                "calib": [list(p) for p in self.geo.pts], "shapes": self.shapes, "next_id": self.next_id,
                "marker_scale": self.mark_scale.get()}

    def save_project(self):
        if self.img is None:
            return
        path = self.project_path()
        try:
            with open(path, "w", encoding="utf-8") as f:
                json.dump(self.project_dict(), f, ensure_ascii=False, indent=1)
            self.dirty = False
            self.tip(f"تم حفظ العلامات والرسومات: {path}")
        except Exception as ex:
            messagebox.showerror("خطأ", str(ex))

    def load_project_dialog(self):
        p = filedialog.askopenfilename(title="فتح مشروع", filetypes=[("مشروع MapCoords", "*.mapproj"), ("كل الملفات", "*.*")])
        if p:
            try:
                self.load_project(p, reopen=True)
            except Exception as ex:
                messagebox.showerror("خطأ", f"تعذّر تحميل المشروع:\n{ex}")

    def load_project(self, path, reopen=True):
        with open(path, "r", encoding="utf-8") as f:
            d = json.load(f)
        if reopen:
            img = d.get("image")
            if (not img or not os.path.isfile(img)) and os.path.basename(img or "") == DEFAULT_MAP \
                    and os.path.isfile(resource_path(DEFAULT_MAP)):
                img = resource_path(DEFAULT_MAP)
            if not img or not os.path.isfile(img):
                alt = path[:-len(".mapproj")] if path.endswith(".mapproj") else None
                img = alt if alt and os.path.isfile(alt) else None
            if not img:
                img = filedialog.askopenfilename(title="لم يُعثر على صورة الخريطة — اخترها")
                if not img:
                    return
            self.img = load_image_any(img)
            self.pyr = [self.img]
            self.img_path = img
            self.root.title(f"{APP_TITLE} — {os.path.basename(img)}")
        self.geo = GeoRef()
        self.geo.mode = d.get("proj") or ("web" if d.get("mercator", True) else "linear")
        self.proj.set(self.geo.mode)
        self.mark_scale.set(float(d.get("marker_scale", self.mark_scale.get())))
        self.geo.pts = [tuple(p) for p in d.get("calib", [])]
        try:
            self.geo.fit()
        except ValueError:
            pass
        self.shapes = d.get("shapes", [])
        if self.geo.ok and self.img is not None:
            W_, H_ = self.img.size
            for sh in self.shapes:
                if sh.get("type") == "gline":
                    pts_ = gline_pts(sh["kind"], sh["value"], self.geo, W_, H_)
                    if pts_:
                        sh["pts"] = pts_
        self.next_id = d.get("next_id", len(self.shapes) + 1)
        self.undo_stack = []
        self.sel = None
        self.refresh_tree()
        self.update_calib_label()
        if reopen:
            self.root.update_idletasks()
            self.fit_view()
        self.request_redraw()

    # ── العرض والتكبير ────────────────────────────────────────────────────
    def fit_view(self):
        if self.img is None:
            return
        cw, ch = max(self.canvas.winfo_width(), 50), max(self.canvas.winfo_height(), 50)
        W, H = self.img.size
        self.zoom = min(cw / W, ch / H) * 0.97
        self.off = [(cw - W * self.zoom) / 2, (ch - H * self.zoom) / 2]
        self.auto_fit = True
        self.request_redraw()

    def zoom_at(self, factor, sx, sy):
        if self.img is None:
            return
        self.auto_fit = False
        nz = min(64.0, max(0.02, self.zoom * factor))
        f = nz / self.zoom
        self.off[0] = sx - (sx - self.off[0]) * f
        self.off[1] = sy - (sy - self.off[1]) * f
        self.zoom = nz
        self.request_redraw()

    def zoom_by(self, factor):
        self.zoom_at(factor, self.canvas.winfo_width() / 2, self.canvas.winfo_height() / 2)

    def zoom_to(self, z):
        self.zoom_by(z / self.zoom)

    def on_wheel(self, e):
        self.wheel_zoom(e, 1 if e.delta > 0 else -1)

    def wheel_zoom(self, e, d):
        self.zoom_at(1.18 if d > 0 else 1 / 1.18, e.x, e.y)

    def center_on(self, x, y):
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        self.auto_fit = False
        self.off = [cw / 2 - x * self.zoom, ch / 2 - y * self.zoom]
        self.request_redraw()

    # ── الرسم على اللوحة ──────────────────────────────────────────────────
    def request_redraw(self):
        if not self._redraw_pending:
            self._redraw_pending = True
            self.root.after_idle(self.redraw)

    def get_level(self, k):
        """هرم صور: نسخ مصغّرة (÷2 ÷4 ÷8…) لتسريع العرض على الخرائط الضخمة"""
        while len(self.pyr) <= k:
            self.pyr.append(self.pyr[-1].reduce(2))
        return self.pyr[k]

    def redraw(self):
        self._redraw_pending = False
        c = self.canvas
        c.delete("all")
        cw, ch = c.winfo_width(), c.winfo_height()
        if self.img is None:
            c.create_text(cw / 2, ch / 2 - 20, text="MapCoords", fill="#5c6675", font=("Segoe UI", 34, "bold"))
            c.create_text(cw / 2, ch / 2 + 34, text="انقر هنا أو اضغط Ctrl+O لفتح صورة الخريطة",
                          fill="#9aa4b2", font=("Segoe UI", 14))
            return
        z = self.zoom
        ox, oy = self.off
        W, H = self.img.size
        x0 = max(0, int(math.floor(-ox / z)))
        y0 = max(0, int(math.floor(-oy / z)))
        x1 = min(W, int(math.ceil((cw - ox) / z)))
        y1 = min(H, int(math.ceil((ch - oy) / z)))
        if x1 > x0 and y1 > y0:
            dw = max(1, int(round((x1 - x0) * z)))
            dh = max(1, int(round((y1 - y0) * z)))
            k = 0
            while k < 10 and z * (2 ** (k + 1)) <= 1.0:
                k += 1
            lvl = self.get_level(k)
            sx, sy = lvl.width / W, lvl.height / H
            res = RS.NEAREST if z >= 1.5 else RS.BILINEAR
            tile = lvl.resize((dw, dh), res, box=(x0 * sx, y0 * sy, x1 * sx, y1 * sy))
            self.tkimg = ImageTk.PhotoImage(tile)
            c.create_image(ox + x0 * z, oy + y0 * z, image=self.tkimg, anchor="nw")

        for s in self.shapes:
            self.draw_shape(s, selected=(s["id"] == self.sel))
        if self.cur:
            tmp = dict(self.cur)
            if tmp["type"] in ("line", "polygon", "measure") and self.cursor_s:
                tmp["pts"] = tmp["pts"] + [list(self.s2i(*self.cursor_s))]
            self.draw_shape(tmp, temp=True)
        self.draw_target()
        self.draw_calib_points()

    def draw_target(self):
        if self.target is None or self.track_var.get():
            return
        k = self.mark_scale.get()
        x, y = self.i2s(*self.target)
        c = self.canvas
        r, arm, gap = 18 * k, 40 * k, 8 * k
        lw = max(2, round(3 * k ** 0.7))
        c.create_oval(x - r, y - r, x + r, y + r, outline="white", width=lw + 3)
        c.create_oval(x - r, y - r, x + r, y + r, outline="#d500f9", width=lw)
        for x1, y1, x2, y2 in ((x - arm, y, x - gap, y), (x + gap, y, x + arm, y),
                               (x, y - arm, x, y - gap), (x, y + gap, x, y + arm)):
            c.create_line(x1, y1, x2, y2, fill="white", width=lw + 3)
            c.create_line(x1, y1, x2, y2, fill="#d500f9", width=lw)
        c.create_oval(x - 3 * k, y - 3 * k, x + 3 * k, y + 3 * k, fill="#d500f9", outline="white")
        dd = f"{self.field_vars['dd.lat'].get()}, {self.field_vars['dd.lon'].get()}"
        text = (self.target_label or "الموقع المحدد") + "\n" + dd
        size = max(8, min(30, round(10 * k)))
        est_w = max(len(t) for t in text.split("\n")) * size * 0.85
        est_h = 2 * size * 1.9
        cw, ch = c.winfo_width(), c.winfo_height()
        off = r + 8
        right_ok = x + off + est_w <= cw - 6
        below = y - off - est_h < 6
        anchor = ("n" if below else "s") + ("w" if right_ok else "e")
        lx = x + off if right_ok else x - off
        ly = y + off if below else y - off
        self.draw_label(lx, ly, text, "#6a00b8", anchor=anchor, size=size)

    def draw_label(self, x, y, text, color="#111", anchor="sw", size=9, tags=()):
        f = ("Segoe UI", size, "bold")
        for dx, dy in ((-1, -1), (1, -1), (-1, 1), (1, 1)):
            self.canvas.create_text(x + dx, y + dy, text=text, fill="white", font=f, anchor=anchor, tags=tags)
        self.canvas.create_text(x, y, text=text, fill=color, font=f, anchor=anchor, tags=tags)

    def draw_gline(self, s, selected=False, tag=None):
        c = self.canvas
        tg = (tag,) if tag else ()
        P = [self.i2s(*p) for p in s["pts"]]
        col = s["color"]
        w = max(1, int(s["width"]))
        flat = [v for p in P for v in p]
        if selected:
            c.create_line(*flat, fill="#1e88e5", width=w + 7, tags=tg)
        c.create_line(*flat, fill="white", width=w + 2, tags=tg)
        c.create_line(*flat, fill=col, width=w, dash=(12, 6), tags=tg)
        cw, ch = c.winfo_width(), c.winfo_height()
        seg = clip_segment(P[0], P[1], 6, 6, cw - 6, ch - 6)
        if not seg:
            return
        txt = gline_label(s["kind"], s["value"])
        est = len(txt) * 8
        if s["kind"] == "lon":
            x, y = min(seg, key=lambda q: q[1])
            if x + 8 + est > cw - 4:
                self.draw_label(x - 6, y + 4, txt, col, "ne", 10, tg)
            else:
                self.draw_label(x + 6, y + 4, txt, col, "nw", 10, tg)
        else:
            x, y = min(seg, key=lambda q: q[0])
            if y < 24:
                self.draw_label(x + 6, y + 4, txt, col, "nw", 10, tg)
            else:
                self.draw_label(x + 6, y - 4, txt, col, "sw", 10, tg)

    def gline_from_point(self, kind, px, py, snap=False):
        """قيمة خط الطول/العرض المار بالنقطة (بكسلات الصورة)"""
        lat, lon = self.geo.px_to_ll(px, py)
        v = lon if kind == "lon" else lat
        return round(v * 60) / 60 if snap else v

    def update_gl_preview(self, x, y, shift=False):
        c = self.canvas
        c.delete("glprev")
        t = self.tool.get()
        if t not in ("meridian", "parallel") or self.img is None or not self.geo.ok:
            return
        kind = "lon" if t == "meridian" else "lat"
        px, py = self.s2i(x, y)
        v = self.gline_from_point(kind, px, py, shift)
        W, H = self.img.size
        pts = gline_pts(kind, v, self.geo, W, H)
        if pts:
            self.draw_gline({"kind": kind, "value": v, "pts": pts, "color": self.color, "width": 1}, tag="glprev")

    def add_gline(self, kind, value, push=True):
        W, H = self.img.size
        pts = gline_pts(kind, value, self.geo, W, H)
        if pts is None:
            return None
        if push:
            self.push_undo()
        lab = gline_label(kind, value)
        sh = {"type": "gline", "kind": kind, "value": value, "pts": pts, "color": self.color,
              "width": max(1, int(self.width.get()) - 1), "name": ("خط طول " if kind == "lon" else "خط عرض ") + lab,
              "auto_name": True}
        self.add_shape(sh)
        return sh

    def gline_move(self, s, px, py):
        v = self.gline_from_point(s["kind"], px, py, False)
        W, H = self.img.size
        pts = gline_pts(s["kind"], v, self.geo, W, H)
        if pts:
            s["value"], s["pts"] = v, pts
            if s.get("auto_name"):
                s["name"] = ("خط طول " if s["kind"] == "lon" else "خط عرض ") + gline_label(s["kind"], v)

    def draw_handles(self, P):
        for x, y in P:
            self.canvas.create_rectangle(x - 4, y - 4, x + 4, y + 4, fill="white", outline="#1e88e5", width=2)

    def draw_shape(self, s, selected=False, temp=False):
        c = self.canvas
        t = s["type"]
        col = s["color"]
        w = int(s["width"])
        P = [self.i2s(*p) for p in s["pts"]]
        if not P:
            return
        flat = [v for p in P for v in p]
        if t == "point":
            x, y = P[0]
            k = self.mark_scale.get()
            if selected:
                c.create_oval(x - 15 * k, y - 15 * k, x + 15 * k, y + 15 * k, outline="#1e88e5", width=2, dash=(3, 2))
            c.create_oval(x - 8 * k, y - 8 * k, x + 8 * k, y + 8 * k, fill="white", outline=col,
                          width=max(2, round(3 * k ** 0.7)))
            c.create_oval(x - 3 * k, y - 3 * k, x + 3 * k, y + 3 * k, fill=col, outline=col)
            lw = max(2, round(2 * k ** 0.7))
            c.create_line(x - 15 * k, y, x - 9 * k, y, fill=col, width=lw)
            c.create_line(x + 9 * k, y, x + 15 * k, y, fill=col, width=lw)
            c.create_line(x, y - 15 * k, x, y - 9 * k, fill=col, width=lw)
            c.create_line(x, y + 9 * k, x, y + 15 * k, fill=col, width=lw)
            self.draw_label(x + 12 * k, y - 10 * k, s.get("name", ""), col, size=max(7, round(9 * k)))
            return
        if t == "text":
            x, y = P[0]
            f = ("Segoe UI", 10 + 2 * w, "bold")
            for dx, dy in ((-1, -1), (1, -1), (-1, 1), (1, 1)):
                c.create_text(x + dx, y + dy, text=s.get("text", ""), fill="white", font=f, anchor="w")
            c.create_text(x, y, text=s.get("text", ""), fill=col, font=f, anchor="w")
            if selected:
                self.draw_handles([P[0]])
            return

        if t == "gline":
            self.draw_gline(s, selected)
            return
        if t in ("line", "measure", "free"):
            if len(P) >= 2:
                c.create_line(*flat, fill=col, width=w, capstyle="round", joinstyle="round",
                              dash=(7, 4) if t == "measure" else "")
            if t != "free":
                for x, y in P:
                    c.create_oval(x - 3, y - 3, x + 3, y + 3, fill="white", outline=col, width=2)
            lx, ly = P[-1]
        elif t == "polygon":
            if len(P) >= 3:
                c.create_polygon(*flat, fill=col, stipple="gray25", outline=col, width=w)
            elif len(P) == 2:
                c.create_line(*flat, fill=col, width=w)
            for x, y in P:
                c.create_oval(x - 3, y - 3, x + 3, y + 3, fill="white", outline=col, width=2)
            lx = sum(p[0] for p in P) / len(P)
            ly = sum(p[1] for p in P) / len(P)
        elif t == "rect":
            if len(P) >= 2:
                c.create_rectangle(P[0][0], P[0][1], P[1][0], P[1][1], fill=col, stipple="gray12", outline=col, width=w)
                lx, ly = (P[0][0] + P[1][0]) / 2, (P[0][1] + P[1][1]) / 2
            else:
                return
        elif t == "circle":
            if len(P) >= 2:
                r = math.hypot(P[1][0] - P[0][0], P[1][1] - P[0][1])
                c.create_oval(P[0][0] - r, P[0][1] - r, P[0][0] + r, P[0][1] + r,
                              fill=col, stipple="gray12", outline=col, width=w)
                c.create_line(P[0][0], P[0][1], P[1][0], P[1][1], fill=col, dash=(3, 3))
                lx, ly = P[0]
            else:
                return
        else:
            return
        numbered_route = s.get("vnames") is not None and t in ("line", "polygon") and not temp
        if numbered_route:
            self.draw_route_marks(s, P, selected)
        if selected and not (numbered_route and s.get("vlabels")):
            self.draw_handles(P if t not in ("free",) else [P[0], P[-1]])
        if t == "measure" or selected or temp:
            txt = self.shape_metrics(s)
            if txt:
                self.draw_label(lx + 10, ly - 8, txt, "#0d47a1")

    def leg_texts(self, s):
        key = (s["id"], s["type"], tuple((round(p[0], 1), round(p[1], 1)) for p in s["pts"]))
        v = self._leg_cache.get(key)
        if v is None:
            v = route_leg_texts(s, self.geo)
            if len(self._leg_cache) > 400:
                self._leg_cache.clear()
            self._leg_cache[key] = v
        return v

    def draw_route_marks(self, s, P, selected=False):
        c = self.canvas
        k = self.mark_scale.get()
        col = s["color"]
        if s.get("legs") and self.geo.ok:
            pairs = list(zip(P, P[1:]))
            if s["type"] == "polygon" and len(P) > 2:
                pairs.append((P[-1], P[0]))
            fs = max(7, round(8 * k))
            for (a, b), txt in zip(pairs, self.leg_texts(s)):
                dx, dy = b[0] - a[0], b[1] - a[1]
                if math.hypot(dx, dy) >= 95 * max(0.7, k):
                    mx, my = (a[0] + b[0]) / 2, (a[1] + b[1]) / 2
                    if abs(dx) >= abs(dy):                      # مقطع أفقي تقريباً: النص فوق الخط
                        self.draw_label(mx, my - 6 - 3 * k, txt, "#0d47a1", anchor="s", size=fs)
                    else:                                       # مقطع رأسي تقريباً: النص بجانب الخط
                        self.draw_label(mx + 8 + 3 * k, my, txt, "#0d47a1", anchor="w", size=fs)
        names = s["vnames"]
        for i, (x, y) in enumerate(P):
            if s.get("vlabels"):
                r = 10 * k
                if selected:
                    c.create_oval(x - r - 5, y - r - 5, x + r + 5, y + r + 5, outline="#1e88e5", width=2, dash=(3, 2))
                c.create_oval(x - r, y - r, x + r, y + r, fill="white", outline=col, width=2)
                c.create_text(x, y, text=str(i + 1), fill=col, font=("Segoe UI", max(7, round(9 * k)), "bold"))
            if i < len(names) and names[i]:
                self.draw_label(x + 12 * k, y - 8 * k, names[i], col, size=max(7, round(9 * k)))

    def draw_calib_points(self):
        for i, (px, py, _, _) in enumerate(self.geo.pts, 1):
            x, y = self.i2s(px, py)
            self.canvas.create_line(x - 12, y, x + 12, y, fill="#ff9800", width=2)
            self.canvas.create_line(x, y - 12, x, y + 12, fill="#ff9800", width=2)
            self.canvas.create_oval(x - 6, y - 6, x + 6, y + 6, outline="#ff9800", width=2)
            self.draw_label(x + 10, y - 8, f"C{i}", "#e65100")

    # ── قياسات ───────────────────────────────────────────────────────────
    def shape_metrics(self, s):
        return shape_metrics_geo(s, self.geo)

    # ── الفأرة ────────────────────────────────────────────────────────────
    def hit_test(self, sx, sy):
        tol = 8
        for s in reversed(self.shapes):
            P = [self.i2s(*p) for p in s["pts"]]
            t = s["type"]
            if not P:
                continue
            if t == "point":
                if math.hypot(sx - P[0][0], sy - P[0][1]) <= 14 * max(1.0, self.mark_scale.get()):
                    return s["id"]
            elif t == "text":
                w = max(20, len(s.get("text", "")) * (10 + 2 * s["width"]) * 0.6)
                if P[0][0] - 4 <= sx <= P[0][0] + w and abs(sy - P[0][1]) <= 12 + s["width"]:
                    return s["id"]
            elif t in ("line", "measure", "free", "gline"):
                if any(seg_dist(sx, sy, a[0], a[1], b[0], b[1]) <= tol for a, b in zip(P, P[1:])):
                    return s["id"]
            elif t == "polygon":
                if len(P) >= 3 and (point_in_poly(sx, sy, P) or any(
                        seg_dist(sx, sy, P[i][0], P[i][1], P[(i + 1) % len(P)][0], P[(i + 1) % len(P)][1]) <= tol
                        for i in range(len(P)))):
                    return s["id"]
            elif t == "rect" and len(P) >= 2:
                xa, xb = sorted((P[0][0], P[1][0]))
                ya, yb = sorted((P[0][1], P[1][1]))
                if xa - tol <= sx <= xb + tol and ya - tol <= sy <= yb + tol:
                    return s["id"]
            elif t == "circle" and len(P) >= 2:
                r = math.hypot(P[1][0] - P[0][0], P[1][1] - P[0][1])
                if math.hypot(sx - P[0][0], sy - P[0][1]) <= r + tol:
                    return s["id"]
        return None

    def shape_by_id(self, sid):
        for s in self.shapes:
            if s["id"] == sid:
                return s
        return None

    def on_motion(self, e):
        self.motion_to(e.x, e.y, bool(getattr(e, "state", 0) & 0x0001))

    def motion_to(self, x, y, shift=False):
        if self.img is None:
            return
        self.cursor_s = (x, y)
        if self.tool.get() in ("meridian", "parallel"):
            self.update_gl_preview(x, y, shift)
        px, py = self.s2i(x, y)
        if not self.locked:
            self.show_coords((px, py))
        W, H = self.img.size
        self.st_zoom.config(text=f"تكبير {self.zoom * 100:.0f}%   بكسل ({px:.0f}, {py:.0f}) من {W}×{H}")
        if self.cur and self.cur["type"] in ("line", "polygon", "measure"):
            self.request_redraw()

    # ── تحريك الخريطة تلقائياً عند حافة الشاشة ────────────────────────────
    EDGE_ZONE = 48                # عرض منطقة الحافة بالبكسل
    EDGE_DWELL = 0.35             # مهلة (ثانية) قبل التحريك عندما لا يكون هناك رسم جارٍ
    DRAW_TOOLS = ("point", "measure", "line", "polygon", "rect", "circle", "free", "text")

    def edge_tick(self):
        try:
            self.edge_step()
        except Exception:
            pass
        self.root.after(20, self.edge_tick)

    def edge_step(self):
        if self.img is None or not self.autopan_var.get():
            self._edge_since = None
            return
        if self.root.grab_current() is not None or self._pan or self._rpan:
            self._edge_since = None
            return
        holding = bool(self._drag) or (self.cur is not None and self._dragging_draw)   # سحب بزر مضغوط
        polyline = self.cur is not None and self.cur["type"] in ("line", "polygon", "measure")
        t = self.tool.get()
        if not (holding or polyline or t in self.DRAW_TOOLS):
            self._edge_since = None
            return
        rx, ry = self.root.winfo_pointerxy()
        x, y = rx - self.canvas.winfo_rootx(), ry - self.canvas.winfo_rooty()
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        over = self.root.winfo_containing(rx, ry) is self.canvas
        if not holding and not over:
            self._edge_since = None
            return
        z = self.EDGE_ZONE

        def vel(v, size):
            if v < z:
                return min(2.5, (z - v) / z)
            if v > size - z:
                return -min(2.5, (v - (size - z)) / z)
            return 0.0

        vx, vy = vel(x, cw), vel(y, ch)
        if vx == 0 and vy == 0:
            self._edge_since = None
            return
        if not (holding or polyline):                 # أداة رسم بلا عملية جارية: انتظر قليلاً
            now = time.monotonic()
            if self._edge_since is None:
                self._edge_since = now
            if now - self._edge_since < self.EDGE_DWELL:
                return
        W, H = self.img.size
        m = 60
        nx, ny = self.off
        if W * self.zoom + 2 * m > cw:
            nx = min(m, max(cw - W * self.zoom - m, nx + vx * (2 + 14 * abs(vx))))
        if H * self.zoom + 2 * m > ch:
            ny = min(m, max(ch - H * self.zoom - m, ny + vy * (2 + 14 * abs(vy))))
        if abs(nx - self.off[0]) < 0.01 and abs(ny - self.off[1]) < 0.01:
            return
        self.off = [nx, ny]
        self.auto_fit = False
        if holding:
            self.drag_to(x, y)                        # الشكل الجاري يتبع المؤشر أثناء الحركة
        else:
            self.motion_to(x, y)
        self.request_redraw()

    def on_press(self, e):
        self.canvas.focus_set()
        if self.img is None:
            self.open_image_dialog()
            return
        t = self.tool.get()
        px, py = self.s2i(e.x, e.y)
        col, w = self.color, int(self.width.get())
        if t == "select":
            sid = self.hit_test(e.x, e.y)
            if sid is not None:
                self.select(sid)
                s = self.shape_by_id(sid)
                self.push_undo()
                self._drag = {"id": sid, "x": px, "y": py, "moved": False}
                if s["type"] in ("point", "text"):
                    self.lock_at(s["pts"][0][0], s["pts"][0][1])
                else:
                    self.lock_at(px, py)
            else:
                self.select(None)
                self._pan = {"x": e.x, "y": e.y, "off": list(self.off), "moved": False, "click": (px, py)}
        elif t == "point":
            self.push_undo()
            self.add_shape({"type": "point", "pts": [[px, py]], "color": col, "width": w})
            self.lock_at(px, py)
        elif t in ("meridian", "parallel"):
            if not self.geo.ok:
                messagebox.showinfo("تنبيه", "الخريطة غير معايَرة.")
                return
            kind = "lon" if t == "meridian" else "lat"
            v = self.gline_from_point(kind, px, py, bool(getattr(e, "state", 0) & 0x0001))
            if self.add_gline(kind, v) is not None:
                self.tip(("خط طول " if kind == "lon" else "خط عرض ") + gline_label(kind, v))
                self.lock_at(px, py)
        elif t in ("line", "polygon", "measure"):
            if self.cur is None:
                self.cur = {"type": t, "pts": [[px, py]], "color": col, "width": w}
            elif self.cur["pts"][-1] != [px, py]:
                self.cur["pts"].append([px, py])
            self.request_redraw()
        elif t in ("rect", "circle"):
            self.cur = {"type": t, "pts": [[px, py], [px, py]], "color": col, "width": w}
            self._dragging_draw = True
        elif t == "free":
            self.cur = {"type": "free", "pts": [[px, py]], "color": col, "width": w}
            self._dragging_draw = True
        elif t == "text":
            txt = simpledialog.askstring("نص", "اكتب النص:", parent=self.root)
            if txt:
                self.push_undo()
                self.add_shape({"type": "text", "pts": [[px, py]], "color": col, "width": w, "text": txt})
        elif t == "calib":
            self.calib_click(px, py)

    def on_drag(self, e):
        self.drag_to(e.x, e.y)

    def drag_to(self, x, y):
        if self.img is None:
            return
        px, py = self.s2i(x, y)
        self.cursor_s = (x, y)
        if self._pan:
            dx, dy = x - self._pan["x"], y - self._pan["y"]
            if abs(dx) + abs(dy) > 3:
                self._pan["moved"] = True
                self.auto_fit = False
            self.off = [self._pan["off"][0] + dx, self._pan["off"][1] + dy]
            self.request_redraw()
        elif self._drag and (self.shape_by_id(self._drag["id"]) or {}).get("type") == "gline":
            self.gline_move(self.shape_by_id(self._drag["id"]), px, py)
            self._drag["moved"] = True
            self.request_redraw()
        elif self._drag:
            s = self.shape_by_id(self._drag["id"])
            dx, dy = px - self._drag["x"], py - self._drag["y"]
            if dx or dy:
                self._drag["moved"] = True
                for p in s["pts"]:
                    p[0] += dx
                    p[1] += dy
                self._drag["x"], self._drag["y"] = px, py
                self.request_redraw()
        elif self.cur and self._dragging_draw:
            if self.cur["type"] == "free":
                last = self.cur["pts"][-1]
                if math.hypot(px - last[0], py - last[1]) * self.zoom > 2.5:
                    self.cur["pts"].append([px, py])
            else:
                self.cur["pts"][1] = [px, py]
            self.request_redraw()
        if not self.locked:
            self.show_coords((px, py))

    def on_release(self, e):
        if self.img is None:
            return
        if self._pan:
            if not self._pan["moved"]:
                self.lock_at(*self._pan["click"])
            self._pan = None
        elif self._drag:
            if not self._drag["moved"]:
                if self.undo_stack:
                    self.undo_stack.pop()
            else:
                s = self.shape_by_id(self._drag["id"])
                if s and s["type"] in ("point", "text"):
                    self.lock_at(s["pts"][0][0], s["pts"][0][1])
                self.refresh_tree()
            self._drag = None
        elif self.cur and self._dragging_draw:
            self._dragging_draw = False
            t = self.cur["type"]
            p = self.cur["pts"]
            ok = (len(p) >= 3) if t == "free" else (
                math.hypot(p[1][0] - p[0][0], p[1][1] - p[0][1]) * self.zoom >= 4)
            if ok:
                self.finish_cur()
            else:
                self.cur = None
                self.request_redraw()

    def on_double(self, e):
        if self.cur and self.cur["type"] in ("line", "polygon", "measure"):
            px, py = self.s2i(e.x, e.y)
            last = self.cur["pts"][-1]
            if math.hypot(px - last[0], py - last[1]) * self.zoom > 4:
                self.cur["pts"].append([px, py])
            self.finish_cur()

    def on_rpress(self, e):
        if self.cur and self.cur["type"] in ("line", "polygon", "measure"):
            self.finish_cur()
        else:
            self.on_pan_start(e)

    def on_pan_start(self, e):
        self._rpan = (e.x, e.y, list(self.off))

    def on_pan_move(self, e):
        if getattr(self, "_rpan", None):
            self.auto_fit = False
            self.off = [self._rpan[2][0] + e.x - self._rpan[0], self._rpan[2][1] + e.y - self._rpan[1]]
            self.request_redraw()

    def on_pan_end(self, e):
        self._rpan = None

    # ── إدارة العناصر ─────────────────────────────────────────────────────
    def push_undo(self):
        self.dirty = True
        self.undo_stack.append((copy.deepcopy(self.shapes), self.next_id))
        if len(self.undo_stack) > 100:
            self.undo_stack.pop(0)

    def undo(self):
        if self.cur:
            self.cancel_cur()
            return
        if not self.undo_stack:
            return
        self.shapes, self.next_id = self.undo_stack.pop()
        if self.sel is not None and not self.shape_by_id(self.sel):
            self.sel = None
        self.refresh_tree()
        self.request_redraw()

    def add_shape(self, s):
        s["id"] = self.next_id
        self.next_id += 1
        names = {"point": "موقع", "line": "خط", "measure": "قياس", "polygon": "مضلع",
                 "rect": "مستطيل", "circle": "دائرة", "free": "رسم", "text": "نص"}
        cnt = sum(1 for x in self.shapes if x["type"] == s["type"]) + 1
        s.setdefault("name", f"{names.get(s['type'], 'عنصر')} {cnt}")
        self.shapes.append(s)
        self.sel = s["id"]
        self.refresh_tree()
        self.request_redraw()

    def finish_cur(self):
        if not self.cur:
            return
        s = self.cur
        need = {"line": 2, "measure": 2, "polygon": 3, "rect": 2, "circle": 2, "free": 2}[s["type"]]
        self._dragging_draw = False
        if len(s["pts"]) >= need:
            self.cur = None
            self.push_undo()
            self.add_shape(s)
            txt = self.shape_metrics(s)
            if txt:
                self.tip(txt)
        else:
            self.cur = None
            self.request_redraw()

    def cancel_cur(self):
        self.cur = None
        self._dragging_draw = False
        self.request_redraw()

    def select(self, sid, from_tree=False):
        self.sel = sid
        if not from_tree:
            self._sync = True
            try:
                if sid is not None and self.tree.exists(str(sid)):
                    self.tree.selection_set(str(sid))
                    self.tree.see(str(sid))
                else:
                    self.tree.selection_remove(self.tree.selection())
            finally:
                self._sync = False
        self.request_redraw()

    def on_tree_select(self, e):
        if self._sync:
            return
        sel = self.tree.selection()
        if not sel:
            return
        sid = int(sel[0])
        self.select(sid, from_tree=True)
        s = self.shape_by_id(sid)
        if s and s["type"] in ("point", "text"):
            self.lock_at(*s["pts"][0])

    def delete_selected(self):
        if self.root.focus_get() is not None and isinstance(self.root.focus_get(), (tk.Entry, ttk.Entry)):
            return
        if self.sel is None:
            return
        self.push_undo()
        self.shapes = [s for s in self.shapes if s["id"] != self.sel]
        self.sel = None
        self.refresh_tree()
        self.request_redraw()

    def clear_all(self):
        if self.shapes and messagebox.askyesno("تأكيد", "مسح كل الرسومات والعلامات؟"):
            self.push_undo()
            self.shapes = []
            self.sel = None
            self.refresh_tree()
            self.request_redraw()

    def rename_selected(self):
        s = self.shape_by_id(self.sel) if self.sel is not None else None
        if not s:
            return
        if s["type"] == "text":
            new = simpledialog.askstring("تعديل النص", "النص:", initialvalue=s.get("text", ""), parent=self.root)
            if new:
                self.push_undo()
                s["text"] = new
        else:
            new = simpledialog.askstring("إعادة تسمية", "الاسم:", initialvalue=s.get("name", ""), parent=self.root)
            if new:
                self.push_undo()
                s["name"] = new
        self.refresh_tree()
        self.request_redraw()

    def zoom_to_selected(self):
        s = self.shape_by_id(self.sel) if self.sel is not None else None
        if not s:
            return
        P = s["pts"] if s["type"] != "circle" else circle_ring(s["pts"])
        xs, ys = [p[0] for p in P], [p[1] for p in P]
        cx, cy = (min(xs) + max(xs)) / 2, (min(ys) + max(ys)) / 2
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        w, h = max(max(xs) - min(xs), 1), max(max(ys) - min(ys), 1)
        self.zoom = min(64.0, max(0.02, min(cw / w, ch / h) * 0.5 if (w > 20 or h > 20) else 4.0))
        self.center_on(cx, cy)

    def refresh_tree(self):
        self._sync = True
        try:
            self.tree.delete(*self.tree.get_children())
            for s in self.shapes:
                self.tree.insert("", "end", iid=str(s["id"]),
                                 values=(type_label(s), s.get("name", "") if s["type"] != "text" else s.get("text", ""),
                                         self.shape_summary(s)))
            if self.sel is not None and self.tree.exists(str(self.sel)):
                self.tree.selection_set(str(self.sel))
        finally:
            self._sync = False

    def shape_summary(self, s):
        if s["type"] == "gline":
            return gline_label(s["kind"], s["value"])
        if s["type"] in ("point", "text"):
            if self.geo.ok:
                la, lo = self.geo.px_to_ll(*s["pts"][0])
                return f"{la:.6f}, {lo:.6f}"
            return f"px {s['pts'][0][0]:.0f}, {s['pts'][0][1]:.0f}"
        m = self.shape_metrics(s)
        return m or f"{len(s['pts'])} نقطة"

    # ── عرض الإحداثيات ────────────────────────────────────────────────────
    def field_values(self, pt):
        vals = {k: "—" for k in ALL_KEYS}
        if pt is None:
            return vals
        px, py = pt
        self.last_px = pt
        vals["pix.x"], vals["pix.y"] = f"{px:.1f}", f"{py:.1f}"
        if self.geo.ok:
            lat, lon = self.geo.px_to_ll(px, py)
            vals.update(format_parts(lat, lon))
        return vals

    def show_coords(self, pt):
        for k, v in self.field_values(pt).items():
            self.field_vars[k].set(v)
        self.update_lock_label()

    def update_lock_label(self):
        if self.track_var.get():
            self.lock_lbl.config(text="● متابعة المؤشر مفعّلة", fg="#2e7d32")
        else:
            self.lock_lbl.config(text="● المتابعة متوقفة — اكتب في أي حقل", fg="#c62828")

    def set_msg(self, text, kind="info"):
        col = {"ok": "#2e7d32", "bad": "#c62828", "warn": "#ef6c00", "info": "#6b7280"}[kind]
        self.field_msg.config(text=text, fg=col)

    def on_track_toggle(self):
        if self.track_var.get():
            self.locked = False
            self.target = None
            if self.cursor_s and self.img is not None:
                self.show_coords(self.s2i(*self.cursor_s))
            else:
                self.show_coords(None)
        else:
            self.locked = True
            if self.last_px:
                self.target = self.last_px
        self.update_lock_label()
        self.request_redraw()

    def on_field_focus(self, widget=None):
        if self.track_var.get():
            self.track_var.set(False)
            self.on_track_toggle()
        if widget is not None:
            widget.after(1, lambda: widget.select_range(0, "end"))

    def lock_at(self, px, py, label=""):
        self.track_var.set(False)
        self.locked = True
        self.target = (px, py)
        self.target_label = label or ""
        self.show_coords((px, py))
        self.request_redraw()

    def unlock(self):
        self.track_var.set(True)
        self.on_track_toggle()

    def view_center_ll(self):
        if self.img is None or not self.geo.ok:
            return None
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        return self.geo.px_to_ll(*self.s2i(cw / 2, ch / 2))

    def change_mark_size(self, factor):
        v = min(5.0, max(0.4, self.mark_scale.get() * factor))
        self.mark_scale.set(round(v, 3))

    def on_mark_scale(self):
        try:
            self.mark_pct.config(text=f"{int(round(self.mark_scale.get() * 100))}%")
        except Exception:
            pass
        self.dirty = True
        self.request_redraw()

    # ── مسار من قائمة إحداثيات ────────────────────────────────────────────
    def enable_text_menu(self, txt):
        def rng():
            r = txt.tag_ranges("sel")
            return (r[0], r[1]) if r else None

        def do_paste():
            try:
                t = self.root.clipboard_get().replace("\r\n", "\n").replace("\r", "\n")
            except tk.TclError:
                return "break"
            r = rng()
            if r:
                txt.delete(r[0], r[1])
                txt.mark_set("insert", r[0])
            txt.insert("insert", t)
            return "break"

        def do_copy():
            r = rng()
            t = txt.get(r[0], r[1]) if r else txt.get("1.0", "end-1c")
            if t:
                self.root.clipboard_clear()
                self.root.clipboard_append(t)
            return "break"

        def do_cut():
            r = rng()
            if r:
                self.root.clipboard_clear()
                self.root.clipboard_append(txt.get(r[0], r[1]))
                txt.delete(r[0], r[1])
            return "break"

        def do_all():
            txt.focus_set()
            txt.tag_add("sel", "1.0", "end-1c")
            return "break"

        def do_clear():
            txt.delete("1.0", "end")
            return "break"

        menu = tk.Menu(txt, tearoff=0)
        for lab, fn in (("لصق", do_paste), ("قص", do_cut), ("نسخ", do_copy), ("تحديد الكل", do_all), ("مسح", do_clear)):
            menu.add_command(label=lab, command=fn)
        txt._ctx_menu = menu

        def popup(e):
            txt.focus_set()
            try:
                menu.tk_popup(e.x_root, e.y_root)
            finally:
                menu.grab_release()
            return "break"

        def ctrl(e):
            ks = getattr(e, "keysym", "")
            if ks in ("a", "A"):
                return do_all()
            if ks in ("v", "V", "c", "C", "x", "X"):
                return None
            if self.win_keys:
                act = {86: do_paste, 67: do_copy, 88: do_cut, 65: do_all}.get(getattr(e, "keycode", 0))
                if act:
                    return act()
            return None

        txt.bind("<Button-3>", popup)
        txt.bind("<<Paste>>", lambda e: do_paste())
        txt.bind("<Control-KeyPress>", ctrl)

    def zoom_to_points(self, pts):
        if not pts:
            return
        xs, ys = [p[0] for p in pts], [p[1] for p in pts]
        cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
        w, h = max(max(xs) - min(xs), 30), max(max(ys) - min(ys), 30)
        self.zoom = min(8.0, max(0.02, min(cw / w, ch / h) * 0.8))
        self.center_on((min(xs) + max(xs)) / 2, (min(ys) + max(ys)) / 2)

    def create_route(self, pts, closed=False, numbered=True, legs=True, name=""):
        """يرسم خطاً (أو مضلعاً مغلقاً) يصل النقاط بالترتيب. pts = [(اسم, lat, lon)]"""
        px = [list(self.geo.ll_to_px(la, lo)) for _, la, lo in pts]
        self.push_undo()
        shape = {"type": "polygon" if closed else "line", "pts": px, "color": self.color,
                 "width": int(self.width.get()), "vnames": [n for n, _, _ in pts],
                 "vlabels": bool(numbered), "legs": bool(legs)}
        cnt = sum(1 for x in self.shapes if x.get("vnames") is not None) + 1
        shape["name"] = name or (f"مضلع {cnt}" if closed else f"مسار {cnt}")
        self.add_shape(shape)
        W, H = self.img.size
        inside = [p for p in px if 0 <= p[0] <= W and 0 <= p[1] <= H]
        self.zoom_to_points(inside or px)
        return shape, len(px) - len(inside)

    def open_route_dialog(self):
        if self.img is None or not self.geo.ok:
            messagebox.showinfo("تنبيه", "افتح خريطة معايَرة أولاً.")
            return
        if self._route_win is not None and self._route_win.winfo_exists():
            self._route_win.deiconify()
            self._route_win.lift()
            return
        win = tk.Toplevel(self.root)
        self._route_win = win
        win.title("مسار من قائمة إحداثيات")
        win.geometry("860x720")
        win.minsize(700, 560)
        win.transient(self.root)

        tk.Label(win, justify="right", anchor="e", wraplength=820, fg="#1e3a5f", font=("Segoe UI", 10),
                 text="اكتب كل إحداثية في سطر مستقل بالترتيب الذي تريد التوصيل به (بأي صيغة: DD أو DMS أو DDM أو UTM أو MGRS).\n"
                      "لإعطاء نقطة اسماً اكتبه قبلها هكذا:   ميناء الشويخ | 29°21'36\"N 47°55'48\"E      "
                      "(السطر الذي يبدأ بـ # يُتجاهل)").pack(fill="x", padx=10, pady=(8, 4))
        box = ttk.Frame(win)
        box.pack(fill="both", expand=True, padx=10)
        txt = tk.Text(box, height=9, wrap="none", font=("Consolas", 11), undo=True)
        sb = ttk.Scrollbar(box, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=sb.set)
        sb.pack(side="left", fill="y")
        txt.pack(side="right", fill="both", expand=True)
        self.enable_text_menu(txt)

        opts = ttk.Frame(win)
        opts.pack(fill="x", padx=10, pady=6)
        kind = tk.StringVar(value="line")
        num = tk.BooleanVar(value=True)
        legs = tk.BooleanVar(value=True)
        nm = tk.StringVar(value="")
        ttk.Radiobutton(opts, text="مسار مفتوح", variable=kind, value="line").pack(side="right", padx=6)
        ttk.Radiobutton(opts, text="مضلع مغلق (+ مساحة)", variable=kind, value="polygon").pack(side="right", padx=6)
        ttk.Checkbutton(opts, text="ترقيم النقاط", variable=num).pack(side="right", padx=6)
        ttk.Checkbutton(opts, text="المسافة والاتجاه على المقاطع", variable=legs).pack(side="right", padx=6)
        nrow = ttk.Frame(win)
        nrow.pack(fill="x", padx=10)
        ttk.Label(nrow, text="اسم المسار (اختياري):").pack(side="right", padx=4)
        ttk.Entry(nrow, textvariable=nm, width=28).pack(side="right")

        status = tk.Label(win, text="", anchor="e", justify="right", wraplength=820, font=("Segoe UI", 9, "bold"))
        status.pack(fill="x", padx=10)

        cols = ("n", "name", "lat", "lon", "nm", "km", "brg", "cum")
        heads = {"n": "#", "name": "الاسم", "lat": "العرض", "lon": "الطول", "nm": "المقطع م.ب",
                 "km": "المقطع كم", "brg": "الاتجاه", "cum": "التراكمي م.ب"}
        widths = {"n": 42, "name": 120, "lat": 120, "lon": 125, "nm": 100, "km": 100, "brg": 72, "cum": 110}
        tf = ttk.Frame(win)
        tf.pack(fill="both", expand=True, padx=10, pady=4)
        tree = ttk.Treeview(tf, columns=cols, show="headings", height=8)
        for cname in cols:
            tree.heading(cname, text=heads[cname])
            tree.column(cname, width=widths[cname], anchor="center")
        tsb = ttk.Scrollbar(tf, orient="vertical", command=tree.yview)
        tree.configure(yscrollcommand=tsb.set)
        tsb.pack(side="left", fill="y")
        tree.pack(side="right", fill="both", expand=True)
        total = tk.Label(win, text="", anchor="e", justify="right", wraplength=820, font=("Segoe UI", 10, "bold"), fg="#0d47a1")
        total.pack(fill="x", padx=10)

        state = {"rows": []}

        def validate(_e=None):
            pts, errs = parse_route_text(txt.get("1.0", "end"))
            if errs:
                status.config(text=f"⚠ {len(pts)} نقطة صحيحة — سطر {errs[0][0]} غير مفهوم: {errs[0][1][:40]}"
                                   + (f"  (+{len(errs) - 1} أخرى)" if len(errs) > 1 else ""), fg="#c62828")
            elif pts:
                status.config(text=f"✔ {len(pts)} نقطة صحيحة", fg="#2e7d32")
            else:
                status.config(text="", fg="#6b7280")
            return pts, errs

        def fill_table(rows, closed):
            tree.delete(*tree.get_children())
            ddm = lambda la, lo: fmt_ddm(la, lo).split(", ")
            for r in rows:
                la, lo = ddm(r["lat"], r["lon"])
                tree.insert("", "end", values=(
                    r["n"], r["name"], la, lo,
                    "—" if r["leg"] is None else f"{r['leg'] / NM:.2f}",
                    "—" if r["leg"] is None else f"{r['leg'] / 1000:.3f}",
                    "—" if r["brg"] is None else f"{r['brg']:.1f}°",
                    f"{r['cum'] / NM:.2f}"))
            tot = rows[-1]["cum"] if rows else 0
            t = f"الإجمالي: {tot / 1000:.3f} كم  =  {tot / NM:.2f} ميل بحري   ({max(len(rows) - 1, 0)} مقطع)"
            if closed and len(rows) > 3:
                ll = [(r["lat"], r["lon"]) for r in rows[:-1]]
                t += f"   •   المساحة: {fmt_area(geo_area(ll))}"
            total.config(text=t)
            state["rows"] = rows

        def do_draw(close=False):
            pts, errs = validate()
            if errs:
                lines = "\n".join(f"سطر {n}:  {t[:60]}   ←   {why}" for n, t, why in errs[:8])
                messagebox.showwarning("توجد أسطر غير مفهومة",
                                       "لم يُرسم شيء حتى لا يختل ترتيب المسار.\nصحّح هذه الأسطر:\n\n" + lines, parent=win)
                return
            closed = kind.get() == "polygon"
            need = 3 if closed else 2
            if len(pts) < need:
                messagebox.showinfo("تنبيه", ("يلزم نقطتان على الأقل." if need == 2 else f"يلزم {need} نقاط على الأقل."), parent=win)
                return
            shape, outside = self.create_route(pts, closed, num.get(), legs.get(), nm.get().strip())
            fill_table(route_rows(pts, closed), closed)
            self.tip(f"رُسم «{shape['name']}» بـ {len(pts)} نقطة")
            if outside:
                status.config(text=f"⚠ رُسم المسار لكن {outside} نقطة تقع خارج حدود الخريطة", fg="#ef6c00")
            if close:
                win.destroy()

        def table_text(sep="\t"):
            hdr = ["#", "الاسم", "Lat", "Lon", "المقطع (م.ب)", "المقطع (كم)", "الاتجاه", "التراكمي (م.ب)"]
            out = [sep.join(hdr)]
            for r in state["rows"]:
                out.append(sep.join([r["n"], r["name"], f"{r['lat']:.6f}", f"{r['lon']:.6f}",
                                     "" if r["leg"] is None else f"{r['leg'] / NM:.3f}",
                                     "" if r["leg"] is None else f"{r['leg'] / 1000:.3f}",
                                     "" if r["brg"] is None else f"{r['brg']:.1f}", f"{r['cum'] / NM:.3f}"]))
            return "\n".join(out)

        def copy_table():
            if state["rows"]:
                self.copy_text(table_text())

        def export_table():
            if not state["rows"]:
                return
            f = filedialog.asksaveasfilename(parent=win, defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="حفظ جدول المسار")
            if f:
                with open(f, "w", newline="", encoding="utf-8-sig") as fh:
                    csv.writer(fh).writerows([ln.split("\t") for ln in table_text().split("\n")])
                self.tip(f"تم التصدير: {f}")

        def load_file():
            f = filedialog.askopenfilename(parent=win, filetypes=[("نصوص", "*.txt *.csv *.lst"), ("كل الملفات", "*.*")])
            if f:
                for enc in ("utf-8-sig", "cp1256", "latin-1"):
                    try:
                        with open(f, "r", encoding=enc) as fh:
                            data = fh.read()
                        break
                    except Exception:
                        data = None
                if data is not None:
                    txt.delete("1.0", "end")
                    txt.insert("1.0", data)
                    validate()

        def example():
            txt.delete("1.0", "end")
            txt.insert("1.0", "ميناء الشويخ | 29°21'36\"N 47°55'48\"E\n"
                              "29.3900, 48.1200\n"
                              "جزيرة فيلكا | 29°25'12\"N 48°19'12\"E\n"
                              "N 29 18.0  E 48 30.0\n")
            validate()

        b1 = ttk.Frame(win)
        b1.pack(fill="x", padx=10, pady=(4, 8))
        ttk.Button(b1, text="رسم على الخريطة", command=do_draw).pack(side="right", padx=3)
        ttk.Button(b1, text="رسم وإغلاق", command=lambda: do_draw(True)).pack(side="right", padx=3)
        ttk.Button(b1, text="مثال", command=example).pack(side="right", padx=3)
        ttk.Button(b1, text="فتح ملف نصي…", command=load_file).pack(side="right", padx=3)
        ttk.Button(b1, text="إغلاق", command=win.destroy).pack(side="left", padx=3)
        ttk.Button(b1, text="تصدير CSV", command=export_table).pack(side="left", padx=3)
        ttk.Button(b1, text="نسخ الجدول", command=copy_table).pack(side="left", padx=3)

        txt.bind("<KeyRelease>", validate)
        win.bind("<<Paste>>", lambda e: win.after(50, validate))
        txt.focus_set()
        win._api = {"txt": txt, "draw": do_draw, "validate": validate, "table": lambda: state["rows"],
                    "kind": kind, "num": num, "legs": legs, "name": nm, "tree": tree, "total": total, "status": status}

    # ── فتح ملف إحداثيات (Excel / CSV) ────────────────────────────────────
    def open_coord_file_dialog(self):
        if self.img is None or not self.geo.ok:
            messagebox.showinfo("تنبيه", "افتح خريطة معايَرة أولاً.")
            return
        path = filedialog.askopenfilename(
            parent=self.root,
            title="فتح ملف إحداثيات",
            filetypes=[("Excel و CSV", "*.xlsx *.xlsm *.xls *.xlsb *.csv"),
                       ("Excel الحديث", "*.xlsx *.xlsm"),
                       ("Excel القديم", "*.xls *.xlsb"),
                       ("CSV", "*.csv"),
                       ("كل الملفات", "*.*")])
        if not path:
            return
        ext = os.path.splitext(path)[1].lower()
        if ext in (".xls", ".xlsb"):
            self.set_msg("جارٍ تحويل ملف Excel القديم عبر Excel — قد يستغرق ثوانٍ…", "info")
            self.root.update_idletasks()
        try:
            sheets_dict = read_coord_file(path)
        except Exception as ex:
            self.set_msg("", "info")
            messagebox.showerror("خطأ في القراءة", f"تعذّر قراءة الملف:\n\n{ex}")
            return
        self.set_msg("", "info")
        if not sheets_dict:
            messagebox.showinfo("ملف فارغ", "الملف لا يحتوي على أوراق قابلة للقراءة.")
            return

        # اختَر أفضل ورقة تحوي إحداثيات
        best_sheet = max(sheets_dict.keys(),
                         key=lambda k: score_sheet_for_coords(*sheets_dict[k]))
        if score_sheet_for_coords(*sheets_dict[best_sheet]) == 0:
            best_sheet = next(iter(sheets_dict.keys()))

        win = tk.Toplevel(self.root)
        self._coord_file_win = win
        win.title(f"ملف إحداثيات — {os.path.basename(path)}")
        win.geometry("1050x680")
        win.minsize(780, 480)
        try:
            win.transient(self.root)
        except Exception:
            pass

        tk.Label(win, text=f"الملف: {path}", anchor="e", justify="right",
                 fg="#1e3a5f", font=("Segoe UI", 9)).pack(fill="x", padx=10, pady=(8, 2))

        # اختيار الورقة
        top = ttk.Frame(win)
        top.pack(fill="x", padx=10, pady=(2, 4))
        info_lbl = tk.Label(top, text="", anchor="e", justify="right", fg="#546e7a", font=("Segoe UI", 9))
        info_lbl.pack(side="right", fill="x", expand=True, padx=(8, 0))
        sheet_var = tk.StringVar(value=best_sheet)
        if len(sheets_dict) > 1:
            ttk.Label(top, text="الورقة:", font=("Segoe UI", 10, "bold")).pack(side="right", padx=(2, 0))
            sheet_cb = ttk.Combobox(top, textvariable=sheet_var,
                                    values=list(sheets_dict.keys()), state="readonly", width=28)
            sheet_cb.pack(side="right", padx=(0, 8))

        # قوائم اختيار الأعمدة
        map_frame = ttk.LabelFrame(win, text="أعمدة الإحداثيات (سيتم اكتشافها تلقائياً)")
        map_frame.pack(fill="x", padx=10, pady=4)
        row1 = ttk.Frame(map_frame)
        row1.pack(fill="x", padx=6, pady=4)

        name_var = tk.StringVar()
        lat_var = tk.StringVar()
        lon_var = tk.StringVar()
        full_var = tk.StringVar()

        def add_combo(parent, label, var, width=22):
            ttk.Label(parent, text=label).pack(side="right", padx=(2, 0))
            cb = ttk.Combobox(parent, textvariable=var, state="readonly", width=width)
            cb.pack(side="right", padx=(0, 8))
            return cb

        name_cb = add_combo(row1, "الاسم:", name_var)
        lat_cb = add_combo(row1, "العرض (Lat):", lat_var)
        lon_cb = add_combo(row1, "الطول (Lon):", lon_var)
        full_cb = add_combo(row1, "إحداثي كامل:", full_var)

        hint = tk.Label(win,
                        text="اختر صفاً من الجدول لتعليم موقعه على الخريطة بعلامة بنفسجية مميزة",
                        anchor="e", justify="right", font=("Segoe UI", 9, "bold"), fg="#0d47a1")
        hint.pack(fill="x", padx=10)
        status = tk.Label(win, text="", anchor="e", justify="right", font=("Segoe UI", 9, "bold"))
        status.pack(fill="x", padx=10)

        # جدول الصفوف
        tf = ttk.Frame(win)
        tf.pack(fill="both", expand=True, padx=10, pady=4)
        tree = ttk.Treeview(tf, show="headings", height=18, selectmode="browse")
        vsb = ttk.Scrollbar(tf, orient="vertical", command=tree.yview)
        hsb = ttk.Scrollbar(win, orient="horizontal", command=tree.xview)
        tree.configure(yscrollcommand=vsb.set, xscrollcommand=hsb.set)
        vsb.pack(side="left", fill="y")
        tree.pack(side="right", fill="both", expand=True)
        hsb.pack(fill="x", padx=10)
        tree.tag_configure("ok", background="#e8f5e9")
        tree.tag_configure("bad", background="#ffebee")
        tree.tag_configure("out", background="#fff3e0")

        state = {"headers": [], "rows": [], "opt_names": [], "parsed": [], "compound": None, "_sync": False}

        def sel_idx(var):
            try:
                return state["opt_names"].index(var.get()) - 1
            except ValueError:
                return -1

        def parse_pair(la_txt, lo_txt):
            la_txt = (la_txt or "").strip()
            lo_txt = (lo_txt or "").strip()
            if not (la_txt and lo_txt):
                raise ValueError("فارغ")
            try:
                la = float(la_txt.replace(",", ".").translate(_TRANS))
                lo = float(lo_txt.replace(",", ".").translate(_TRANS))
                if abs(la) <= 90 and abs(lo) <= 180:
                    return la, lo
                if abs(lo) <= 90 and abs(la) <= 180:
                    return lo, la
                raise ValueError("خارج المدى")
            except ValueError:
                return parse_coords(f"{la_txt} {lo_txt}")

        def refresh():
            headers = state["headers"]
            data_rows = state["rows"]
            ni = sel_idx(name_var)
            li = sel_idx(lat_var)
            oi = sel_idx(lon_var)
            fi = sel_idx(full_var)
            # فقط عند تحديد lat/lon نعيد اكتشاف الصيغة المركّبة
            state["compound"] = detect_compound_dms(headers, data_rows[:40], li, oi) if li >= 0 and oi >= 0 else None
            comp = state["compound"]
            parsed = state["parsed"]
            parsed.clear()
            for iid in tree.get_children():
                tree.delete(iid)
            W, H = self.img.size
            good = bad = out = 0
            for r_i, r in enumerate(data_rows):
                def cell(k):
                    if 0 <= k < len(r) and r[k] is not None:
                        return str(r[k])
                    return ""

                nm = cell(ni).strip() if ni >= 0 else ""
                lat = lon = None
                err = ""
                try:
                    if fi >= 0 and cell(fi).strip():
                        lat, lon = parse_coords(cell(fi))
                    elif comp and li >= 0 and oi >= 0:
                        lat = parse_compound_row(r, li, comp, True)
                        lon = parse_compound_row(r, oi, comp, False)
                    elif li >= 0 and oi >= 0:
                        lat, lon = parse_pair(cell(li), cell(oi))
                    else:
                        err = "لم تُحدَّد أعمدة الإحداثيات"
                except Exception as ex:
                    err = (str(ex) or "صيغة غير مفهومة")[:60]

                px = py = None
                inside = False
                if lat is not None and lon is not None:
                    px, py = self.geo.ll_to_px(lat, lon)
                    inside = 0 <= px <= W and 0 <= py <= H

                values = [str(r_i + 1)]
                for i in range(len(headers)):
                    v = r[i] if i < len(r) and r[i] is not None else ""
                    v = str(v)
                    if len(v) > 80:
                        v = v[:78] + "…"
                    values.append(v)
                if lat is None:
                    st_txt, tag = ("⚠ " + err), "bad"
                    bad += 1
                elif not inside:
                    st_txt, tag = "⚠ خارج الخريطة", "out"
                    out += 1
                    good += 1
                else:
                    st_txt, tag = "✔", "ok"
                    good += 1
                values.append(st_txt)
                tree.insert("", "end", iid=str(r_i), values=values, tags=(tag,))
                parsed.append({"name": nm, "lat": lat, "lon": lon,
                               "px": px, "py": py, "err": err, "inside": inside})
            parts = [f"{good} صف بإحداثيات صحيحة"]
            if comp:
                parts.append(f"صيغة مركّبة: {'درجات+دقائق+ث+اتجاه' if comp == 'dms' else 'درجات+دقائق+اتجاه'}")
            if out:
                parts.append(f"{out} خارج الخريطة")
            if bad:
                parts.append(f"{bad} بدون إحداثيات")
            fg = "#2e7d32" if (bad == 0 and out == 0) else ("#ef6c00" if bad == 0 else "#c62828")
            status.config(text="  •  ".join(parts), fg=fg)

        def load_sheet(name):
            headers, rows = sheets_dict[name]
            if not headers and rows:
                headers = [f"عمود {i + 1}" for i in range(max(len(r) for r in rows))]
            state["headers"] = headers
            state["rows"] = rows
            state["opt_names"] = ["— لا شيء —"] + [
                f"{i + 1}. {(h or '').strip() or 'عمود ' + str(i + 1)}"
                for i, h in enumerate(headers)]
            info_lbl.config(text=f"الصفوف: {len(rows)}   •   الأعمدة: {len(headers)}")

            # أعِد بناء أعمدة الجدول
            col_ids = ["_n"] + [f"c{i}" for i in range(len(headers))] + ["_st"]
            disp_names = ["#"] + [((h or "").strip() or f"عمود {i + 1}")
                                   for i, h in enumerate(headers)] + ["الحالة"]
            tree.configure(columns=col_ids)
            for cid, nm in zip(col_ids, disp_names):
                tree.heading(cid, text=nm)
                if cid == "_n":
                    tree.column(cid, width=48, anchor="center", stretch=False)
                elif cid == "_st":
                    tree.column(cid, width=140, anchor="center", stretch=False)
                else:
                    tree.column(cid, width=110, anchor="center")

            # حدّث القوائم المنسدلة
            for cb in (name_cb, lat_cb, lon_cb, full_cb):
                cb.configure(values=state["opt_names"])
            state["_sync"] = True
            try:
                auto = detect_coord_cols(headers)
                if auto["lat"] == -1 and auto["lon"] == -1 and auto["full"] == -1 and rows:
                    first = rows[0]
                    for i, v in enumerate(first):
                        try:
                            parse_coords(str(v))
                            auto["full"] = i
                            break
                        except Exception:
                            pass

                def val_of(i):
                    return state["opt_names"][i + 1] if 0 <= i < len(headers) else state["opt_names"][0]

                name_var.set(val_of(auto["name"]))
                lat_var.set(val_of(auto["lat"]))
                lon_var.set(val_of(auto["lon"]))
                full_var.set(val_of(auto["full"]))
            finally:
                state["_sync"] = False
            refresh()

        def on_select(_e=None):
            sel = tree.selection()
            if not sel:
                return
            try:
                r_i = int(sel[0])
            except ValueError:
                return
            p = state["parsed"][r_i]
            if p["lat"] is None:
                self.set_msg(f"⚠ الصف {r_i + 1}: {p['err']}", "bad")
                return
            if not p["inside"]:
                self.set_msg(f"⚠ الصف {r_i + 1}: خارج حدود الخريطة", "warn")
                return
            label = p["name"] or f"صف {r_i + 1}"
            self.goto_px(p["px"], p["py"], label=label)

        def add_all_markers():
            valid = [p for p in state["parsed"] if p["lat"] is not None and p["inside"]]
            if not valid:
                messagebox.showinfo("تنبيه", "لا توجد صفوف صالحة داخل حدود الخريطة.", parent=win)
                return
            if len(valid) > 200:
                if not messagebox.askyesno("تأكيد",
                                           f"سيُضاف {len(valid)} علامة. المتابعة؟", parent=win):
                    return
            self.push_undo()
            added = 0
            for p in valid:
                s = {"type": "point", "pts": [[p["px"], p["py"]]],
                     "color": self.color, "width": int(self.width.get())}
                if p["name"]:
                    s["name"] = p["name"]
                self.add_shape(s)
                added += 1
            outside = sum(1 for p in state["parsed"] if p["lat"] is not None and not p["inside"])
            msg = f"✔ أُضيفت {added} علامة"
            if outside:
                msg += f"   •  تم تجاهل {outside} خارج الخريطة"
            self.set_msg(msg, "ok")
            self.tip(msg)

        def draw_track(closed=False):
            valid = [(p["name"] or "", p["lat"], p["lon"])
                     for p in state["parsed"] if p["lat"] is not None]
            need = 3 if closed else 2
            if len(valid) < need:
                messagebox.showinfo("تنبيه", f"يلزم {need} صف صحيح على الأقل.", parent=win)
                return
            self.create_route(valid, closed=closed, numbered=True, legs=True,
                              name=os.path.splitext(os.path.basename(path))[0])
            self.tip(f"رُسم {'مضلع' if closed else 'مسار'} بـ {len(valid)} نقطة")

        def swap_lat_lon():
            a = lat_var.get()
            state["_sync"] = True
            try:
                lat_var.set(lon_var.get())
                lon_var.set(a)
            finally:
                state["_sync"] = False
            refresh()

        def clear_target():
            self.target = None
            self.target_label = ""
            self.unlock()
            self.request_redraw()

        def on_var_change(*_a):
            if not state["_sync"]:
                refresh()

        tree.bind("<<TreeviewSelect>>", on_select)
        for v in (lat_var, lon_var, name_var, full_var):
            v.trace_add("write", on_var_change)
        sheet_var.trace_add("write", lambda *a: load_sheet(sheet_var.get()))

        btns = ttk.Frame(win)
        btns.pack(fill="x", padx=10, pady=(6, 10))
        ttk.Button(btns, text="علامات ثابتة للجميع", command=add_all_markers).pack(side="right", padx=3)
        ttk.Button(btns, text="مسار من الجميع", command=lambda: draw_track(False)).pack(side="right", padx=3)
        ttk.Button(btns, text="مضلع مغلق من الجميع", command=lambda: draw_track(True)).pack(side="right", padx=3)
        ttk.Button(btns, text="تبديل العرض/الطول", command=swap_lat_lon).pack(side="right", padx=3)
        ttk.Button(btns, text="مسح العلامة", command=clear_target).pack(side="left", padx=3)
        ttk.Button(btns, text="إغلاق", command=win.destroy).pack(side="left", padx=3)

        load_sheet(best_sheet)

    def open_gline_dialog(self):
        if self.img is None or not self.geo.ok:
            messagebox.showinfo("تنبيه", "افتح خريطة معايَرة أولاً.")
            return
        win = tk.Toplevel(self.root)
        win.title("خطوط طول وعرض بقيم محددة")
        win.geometry("560x430")
        win.transient(self.root)
        tk.Label(win, justify="right", anchor="e", wraplength=520, fg="#1e3a5f", font=("Segoe UI", 10),
                 text="اكتب كل قيمة في سطر. حرف الاتجاه يحدد النوع: E أو W = خط طول، N أو S = خط عرض.\n"
                      "أمثلة:   48°30'E    29.5N    N 29°15.5'    47.75 W\n"
                      "وإن كتبتَ رقماً بلا حرف فسيُعامل حسب الاختيار أدناه.").pack(fill="x", padx=10, pady=(8, 4))
        txt = tk.Text(win, height=9, font=("Consolas", 11), undo=True)
        txt.pack(fill="both", expand=True, padx=10)
        self.enable_text_menu(txt)
        opts = ttk.Frame(win)
        opts.pack(fill="x", padx=10, pady=6)
        kind = tk.StringVar(value="lon")
        ttk.Label(opts, text="القيمة بلا حرف تعني:").pack(side="right", padx=4)
        ttk.Radiobutton(opts, text="خط طول", variable=kind, value="lon").pack(side="right", padx=4)
        ttk.Radiobutton(opts, text="خط عرض", variable=kind, value="lat").pack(side="right", padx=4)
        status = tk.Label(win, text="", anchor="e", justify="right", wraplength=520, font=("Segoe UI", 9, "bold"))
        status.pack(fill="x", padx=10)

        def validate(_e=None):
            vals, errs = parse_gline_text(txt.get("1.0", "end"), kind.get())
            if errs:
                status.config(text=f"⚠ {len(vals)} صحيح — سطر {errs[0][0]}: {errs[0][2]}", fg="#c62828")
            elif vals:
                status.config(text=f"✔ {len(vals)} خط", fg="#2e7d32")
            else:
                status.config(text="", fg="#6b7280")
            return vals, errs

        def do_draw(close=False):
            vals, errs = validate()
            if errs:
                lines = "\n".join(f"سطر {n}:  {t[:50]}   ←   {why}" for n, t, why in errs[:8])
                messagebox.showwarning("توجد أسطر غير مفهومة", "لم يُرسم شيء. صحّح هذه الأسطر:\n\n" + lines, parent=win)
                return
            if not vals:
                messagebox.showinfo("تنبيه", "اكتب قيمة واحدة على الأقل.", parent=win)
                return
            self.push_undo()
            made, skipped = 0, []
            for k_, v_, raw_ in vals:
                if self.add_gline(k_, v_, push=False) is not None:
                    made += 1
                else:
                    skipped.append(raw_)
            self.tip(f"رُسم {made} خط")
            if skipped:
                status.config(text="⚠ خارج حدود الخريطة ولم تُرسم: " + " ، ".join(skipped[:5]), fg="#ef6c00")
                if not made and self.undo_stack:
                    self.undo_stack.pop()
            elif close:
                win.destroy()
            else:
                status.config(text=f"✔ رُسم {made} خط", fg="#2e7d32")

        def example():
            txt.delete("1.0", "end")
            txt.insert("1.0", "48°00'E\n48°30'E\n49°00'E\n29°30'N\n29°00'N\n")
            validate()

        b = ttk.Frame(win)
        b.pack(fill="x", padx=10, pady=(4, 10))
        ttk.Button(b, text="رسم على الخريطة", command=do_draw).pack(side="right", padx=3)
        ttk.Button(b, text="رسم وإغلاق", command=lambda: do_draw(True)).pack(side="right", padx=3)
        ttk.Button(b, text="مثال", command=example).pack(side="right", padx=3)
        ttk.Button(b, text="إغلاق", command=win.destroy).pack(side="left", padx=3)
        txt.bind("<KeyRelease>", validate)
        txt.focus_set()
        win._api = {"txt": txt, "draw": do_draw, "kind": kind, "status": status, "validate": validate}

    def note_edit(self, row, field):
        self.edit_row = (row, field)
        self.edit_field[row] = field

    def mark_edit(self, e, row, field):
        ks = getattr(e, "keysym", "")
        ch = getattr(e, "char", "")
        if ks in ("BackSpace", "Delete") or (ch and ch.isprintable()) or ks in ("Paste", "Cut", "??"):
            self.note_edit(row, field)

    # ── قائمة الزر الأيمن + لصق/نسخ/قص تعمل مع أي لغة لوحة مفاتيح ──────────
    def enable_edit_menu(self, ent, on_edit=None, paste_go=None):
        def sel_range():
            try:
                if ent.selection_present():
                    return ent.index("sel.first"), ent.index("sel.last")
            except tk.TclError:
                pass
            return None

        def sel_text():
            r = sel_range()
            return ent.get()[r[0]:r[1]] if r else ""

        def clip_text():
            try:
                return " ".join(self.root.clipboard_get().split())     # يحوّل الأسطر المتعددة إلى سطر واحد
            except tk.TclError:
                return ""

        def do_paste(go=False):
            txt = clip_text()
            if not txt:
                return "break"
            r = sel_range()
            if r:
                ent.delete(r[0], r[1])
                ent.icursor(r[0])
            else:
                ent.delete(0, "end")                # بلا تحديد: يستبدل محتوى الحقل كله
            ent.insert("insert", txt)
            if on_edit:
                on_edit()
            if go and paste_go:
                paste_go()
            return "break"

        def do_copy():
            t = sel_text() or ent.get()
            if t:
                self.root.clipboard_clear()
                self.root.clipboard_append(t)
                self.tip("تم النسخ: " + t)
            return "break"

        def do_cut():
            r = sel_range()
            if r:
                self.root.clipboard_clear()
                self.root.clipboard_append(ent.get()[r[0]:r[1]])
                ent.delete(r[0], r[1])
                if on_edit:
                    on_edit()
            return "break"

        def do_all():
            ent.focus_set()
            ent.select_range(0, "end")
            ent.icursor("end")
            return "break"

        def do_clear():
            ent.delete(0, "end")
            if on_edit:
                on_edit()
            return "break"

        menu = tk.Menu(ent, tearoff=0)
        menu.add_command(label="لصق", command=do_paste)
        if paste_go:
            menu.add_command(label="لصق وانتقال", command=lambda: do_paste(True))
        menu.add_separator()
        menu.add_command(label="قص", command=do_cut)
        menu.add_command(label="نسخ", command=do_copy)
        menu.add_command(label="تحديد الكل", command=do_all)
        menu.add_separator()
        menu.add_command(label="مسح", command=do_clear)
        ent._ctx_menu = menu

        def popup(e):
            ent.focus_set()
            has_sel = bool(sel_text())
            can_paste = bool(clip_text())
            for i in range(menu.index("end") + 1):
                lab = menu.entrycget(i, "label") if menu.type(i) == "command" else None
                if lab in ("لصق", "لصق وانتقال"):
                    menu.entryconfig(i, state="normal" if can_paste else "disabled")
                elif lab in ("قص",):
                    menu.entryconfig(i, state="normal" if has_sel else "disabled")
            try:
                menu.tk_popup(e.x_root, e.y_root)
            finally:
                menu.grab_release()
            return "break"

        def ctrl(e):
            ks = getattr(e, "keysym", "")
            if ks in ("a", "A"):
                return do_all()
            if ks in ("v", "V", "c", "C", "x", "X"):
                return None                                    # لوحة لاتينية: يتولاها Tk
            if self.win_keys:                                  # لوحة عربية وغيرها: نستخدم رمز المفتاح
                act = {86: do_paste, 67: do_copy, 88: do_cut, 65: do_all}.get(getattr(e, "keycode", 0))
                if act:
                    return act()
            return None

        ent.bind("<Button-3>", popup)
        ent.bind("<<Paste>>", lambda e: do_paste())
        ent.bind("<Control-KeyPress>", ctrl)
        ent._edit_api = {"paste": do_paste, "copy": do_copy, "cut": do_cut, "all": do_all, "clear": do_clear}

    def go_row(self, row):
        self.apply_typed(row, self.edit_field.get(row))

    def go_last(self):
        row, field = self.edit_row if self.edit_row else ("dd", None)
        self.apply_typed(row, field)

    def chart_bounds_text(self):
        if not self.geo.ok or self.img is None:
            return ""
        W, H = self.img.size
        la1, lo1 = self.geo.px_to_ll(0, 0)
        la2, lo2 = self.geo.px_to_ll(W, H)
        return (f"تغطي هذه الخريطة تقريباً: العرض من {min(la1, la2):.2f}° إلى {max(la1, la2):.2f}° "
                f"والطول من {min(lo1, lo2):.2f}° إلى {max(lo1, lo2):.2f}°")

    def apply_typed(self, row, field=None):
        """يقرأ الحقول المكتوبة يدوياً ويذهب إلى الموقع ويعلّم عليه"""
        if self.img is None:
            return
        pref = row + "."
        vals = {k[len(pref):]: self.field_vars[k].get() for k in ALL_KEYS if k.startswith(pref)}
        try:
            res = parse_row(row, vals, field, self.view_center_ll())
        except Exception as ex:
            self.set_msg("⚠ " + (str(ex) or "صيغة غير صحيحة"), "bad")
            return
        W, H = self.img.size
        inside = lambda x, y: 0 <= x <= W and 0 <= y <= H
        if res[0] == "px":
            px, py = res[1], res[2]
        else:
            if not self.geo.ok:
                self.set_msg("⚠ عايِر الخريطة أولاً لتحويل الإحداثيات إلى موضع", "bad")
                return
            px, py = self.geo.ll_to_px(res[1], res[2])
            if not inside(px, py) and row in ("dd", "dms", "ddm") and abs(res[2]) <= 90:
                sx, sy = self.geo.ll_to_px(res[2], res[1])      # هل العرض والطول مقلوبان؟
                if inside(sx, sy) and messagebox.askyesno(
                        "هل العرض والطول مقلوبان؟",
                        "الإحداثيات المكتوبة تقع خارج الخريطة.\n\n"
                        f"لكن إذا كان العرض = {res[2]:.6f} والطول = {res[1]:.6f} فالموقع داخل الخريطة.\n\n"
                        "هل تريد تبديل العرض والطول والذهاب إلى الموقع؟"):
                    px, py = sx, sy
        self.goto_px(px, py)

    def goto_px(self, px, py, label=""):
        W, H = self.img.size
        inside = 0 <= px <= W and 0 <= py <= H
        self.lock_at(px, py, label)
        if inside:
            if self.zoom < 0.8:
                self.zoom = 0.8
            self.center_on(px, py)
            self.set_msg("✔ ظهر الموقع على الخريطة (الدائرة البنفسجية) — انقر «علامة على هذه النقطة» لحفظه", "ok")
        else:
            msg = "الموقع المكتوب يقع خارج حدود الخريطة الحالية."
            b = self.chart_bounds_text()
            if b:
                msg += "\n\n" + b + "\n\nتأكد من أن العرض في حقل العرض والطول في حقل الطول."
            self.set_msg("⚠ الموقع خارج حدود الخريطة — راجع العرض والطول", "warn")
            messagebox.showwarning("خارج الخريطة", msg)

    def add_marker_here(self):
        pt = self.target or self.last_px
        if self.img is None or pt is None:
            self.set_msg("⚠ لا توجد نقطة محددة — اكتب إحداثية أو انقر على الخريطة", "bad")
            return
        W, H = self.img.size
        if not (0 <= pt[0] <= W and 0 <= pt[1] <= H):
            self.set_msg("⚠ النقطة خارج حدود الخريطة — لم تُضَف علامة", "bad")
            messagebox.showwarning("خارج الخريطة", "هذه النقطة تقع خارج حدود الخريطة، لذلك لم تُضَف علامة.\n\n" + self.chart_bounds_text())
            return
        self.push_undo()
        self.add_shape({"type": "point", "pts": [[pt[0], pt[1]]], "color": self.color,
                        "width": int(self.width.get())})
        self.set_msg("✔ أُضيفت علامة موقع", "ok")

    def copy_text(self, txt):
        self.root.clipboard_clear()
        self.root.clipboard_append(txt)
        self.tip("تم النسخ: " + txt.replace("\n", " | "))

    def copy_field(self, k):
        v = self.field_vars[k].get()
        if v and not v.startswith("—"):
            self.copy_text(v)

    def row_text(self, row):
        cells = [c for r, _, cs in FIELD_ROWS if r == row for c in cs]
        vals = [self.field_vars[f"{row}.{k}"].get() for k, _, _ in cells]
        vals = [v for v in vals if v and not v.startswith("—")]
        sep = " " if row in ("utm", "mgrs") else (" | " if row == "code" else ", ")
        return sep.join(vals)

    def copy_row(self, row):
        t = self.row_text(row)
        if t:
            self.copy_text(t)

    def copy_all(self):
        lines = [f"{ROW_TITLES[r]}: {self.row_text(r)}" for r, _, _ in FIELD_ROWS if self.row_text(r)]
        if lines:
            self.copy_text("\n".join(lines))

    def tip(self, msg):
        self.st_tip.config(text=msg)

    def pick_color(self):
        c = colorchooser.askcolor(color=self.color, parent=self.root)
        if c and c[1]:
            self.color = c[1]
            self.color_btn.config(bg=self.color)
            s = self.shape_by_id(self.sel) if self.sel is not None else None
            if s and self.tool.get() == "select":
                self.push_undo()
                s["color"] = self.color
                self.request_redraw()

    def on_tool_change(self):
        t = self.tool.get()
        self.cur = None
        self._dragging_draw = False
        self.canvas.config(cursor="arrow" if t == "select" else "crosshair")
        self.tip(TOOL_TIPS.get(t, ""))
        self.canvas.delete("glprev")
        self.request_redraw()

    # ── الانتقال إلى إحداثيات ─────────────────────────────────────────────
    def goto_coords(self):
        if self.img is None:
            messagebox.showinfo("تنبيه", "افتح خريطة أولاً.")
            return
        if not self.geo.ok:
            messagebox.showinfo("تنبيه", "عايِر الخريطة أولاً (نقطتان معروفتان على الأقل).")
            return
        try:
            lat, lon = parse_coords(self.goto_var.get())
        except Exception as ex:
            self.set_msg("⚠ " + (str(ex) or "تعذّر فهم الصيغة"), "bad")
            return
        px, py = self.geo.ll_to_px(lat, lon)
        self.goto_px(px, py)

    # ── المعايرة ──────────────────────────────────────────────────────────
    def calib_click(self, px, py):
        n = len(self.geo.pts) + 1
        while True:
            txt = simpledialog.askstring(
                f"نقطة المعايرة C{n}",
                "اكتب إحداثيات هذه النقطة بأي صيغة\n\nأمثلة:\n29.3759, 47.9774\n"
                "29°22'33.2\"N 47°58'38.6\"E\n38R 789011 3253319",
                parent=self.root)
            if not txt:
                return
            try:
                lat, lon = parse_coords(txt)
                break
            except Exception as ex:
                messagebox.showerror("إحداثيات غير صحيحة", str(ex) or "تعذّر فهم الصيغة")
        self.geo.pts.append((px, py, lat, lon))
        self.geo.mode = self.proj.get()
        try:
            self.geo.fit()
        except ValueError as ex:
            messagebox.showwarning("المعايرة", str(ex))
            self.geo.pts.pop()
            self.geo.fit() if len(self.geo.pts) >= 2 else None
        self.update_calib_label()
        self.refresh_tree()
        self.request_redraw()

    def calib_undo(self):
        if self.geo.pts:
            self.geo.pts.pop()
            try:
                self.geo.fit()
            except ValueError:
                self.geo.coef = None
            self.update_calib_label()
            self.refresh_tree()
            self.request_redraw()

    def calib_clear(self):
        if self.geo.pts and messagebox.askyesno("تأكيد", "مسح كل نقاط المعايرة؟"):
            self.geo.pts = []
            self.geo.coef = None
            self.geo.rms = None
            self.update_calib_label()
            self.refresh_tree()
            self.request_redraw()
            self.show_coords(None if self.img is None else self.last_px)

    def on_proj_change(self):
        self.geo.mode = self.proj.get()
        try:
            self.geo.fit()
        except ValueError:
            self.geo.coef = None
        self.update_calib_label()
        self.refresh_tree()
        self.request_redraw()

    def update_calib_label(self):
        n = len(self.geo.pts)
        proj = {"web": "ميركاتور كروي", "wgs84": "ميركاتور WGS84", "linear": "خطي"}[self.geo.mode]
        if n == 0:
            txt = "⚠ الخريطة غير معايَرة — اختر أداة «معايرة الخريطة» ◎ وانقر على نقطة معروفة الإحداثيات."
            col = "#c62828"
        elif n == 1:
            txt = "نقطة معايرة واحدة — أضف نقطة ثانية بعيدة عن الأولى على الأقل."
            col = "#ef6c00"
        elif not self.geo.ok:
            txt = "تعذّر حساب المعايرة — راجع النقاط."
            col = "#c62828"
        elif n == 2:
            txt = f"✔ معايَرة بنقطتين (خريطة متجهة للشمال) • إسقاط {proj}. أضف نقطة ثالثة لرفع الدقة ودعم الدوران."
            col = "#2e7d32"
        else:
            txt = f"✔ معايَرة بـ {n} نقاط • إسقاط {proj} • متوسط الخطأ ≈ {fmt_len(self.geo.rms or 0)}"
            col = "#2e7d32"
        self.calib_lbl.config(text=txt, fg=col)

    # ── التصدير ───────────────────────────────────────────────────────────
    def need_geo(self):
        if self.img is None or not self.geo.ok:
            messagebox.showinfo("تنبيه", "عايِر الخريطة أولاً.")
            return False
        return True

    def geo_geometry(self, s):
        """يرجع (نوع الهندسة, الإحداثيات [lon,lat])"""
        G = lambda p: [round(self.geo.px_to_ll(p[0], p[1])[1], 8), round(self.geo.px_to_ll(p[0], p[1])[0], 8)]
        t = s["type"]
        if t in ("point", "text"):
            return "Point", G(s["pts"][0])
        if t in ("line", "measure", "free", "gline"):
            return "LineString", [G(p) for p in s["pts"]]
        if t == "polygon":
            ring = [G(p) for p in s["pts"]]
        elif t == "rect":
            ring = [G(p) for p in rect_corners(s["pts"])]
        else:
            ring = [G(p) for p in circle_ring(s["pts"])]
        ring.append(ring[0])
        return "Polygon", ring

    def export_csv(self):
        if not self.need_geo():
            return
        pts = [s for s in self.shapes if s["type"] == "point"]
        if not pts:
            messagebox.showinfo("تنبيه", "لا توجد علامات مواقع لتصديرها.")
            return
        p = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")], title="حفظ CSV")
        if not p:
            return
        with open(p, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["الاسم", "Lat", "Lon", "DMS", "DDM", "UTM", "MGRS", "Web Mercator", "Plus Code", "Geohash", "Maidenhead"])
            for s in pts:
                la, lo = self.geo.px_to_ll(*s["pts"][0])
                a = format_all(la, lo)
                w.writerow([s["name"], f"{la:.8f}", f"{lo:.8f}", a["dms"], a["ddm"], a["utm"],
                            a["mgrs"], a["merc"], a["plus"], a["geohash"], a["mh"]])
        self.tip(f"تم التصدير: {p}")

    @staticmethod
    def kml_color(hexcol, alpha="ff"):
        h = hexcol.lstrip("#")
        return alpha + h[4:6] + h[2:4] + h[0:2]

    def export_kml(self):
        if not self.need_geo() or not self.shapes:
            if self.shapes == []:
                messagebox.showinfo("تنبيه", "لا توجد عناصر لتصديرها.")
            return
        p = filedialog.asksaveasfilename(defaultextension=".kml", filetypes=[("KML", "*.kml")], title="حفظ KML")
        if not p:
            return
        out = ['<?xml version="1.0" encoding="UTF-8"?>',
               '<kml xmlns="http://www.opengis.net/kml/2.2"><Document>',
               f"<name>{xml_escape(os.path.basename(self.img_path or 'MapCoords'))}</name>"]
        for s in self.shapes:
            typ, co = self.geo_geometry(s)
            name = xml_escape(s.get("text") if s["type"] == "text" else s.get("name", ""))
            kc = self.kml_color(s["color"])
            style = (f"<Style><IconStyle><color>{kc}</color></IconStyle>"
                     f"<LineStyle><color>{kc}</color><width>{s['width']}</width></LineStyle>"
                     f"<PolyStyle><color>{self.kml_color(s['color'], '55')}</color></PolyStyle></Style>")
            if typ == "Point":
                geom = f"<Point><coordinates>{co[0]},{co[1]},0</coordinates></Point>"
            elif typ == "LineString":
                geom = "<LineString><tessellate>1</tessellate><coordinates>" + " ".join(f"{a},{b},0" for a, b in co) + "</coordinates></LineString>"
            else:
                geom = ("<Polygon><outerBoundaryIs><LinearRing><coordinates>" +
                        " ".join(f"{a},{b},0" for a, b in co) + "</coordinates></LinearRing></outerBoundaryIs></Polygon>")
            out.append(f"<Placemark><name>{name}</name>{style}{geom}</Placemark>")
            if s.get("vnames") is not None:
                for i, pp in enumerate(s["pts"]):
                    lat_, lon_ = self.geo.px_to_ll(pp[0], pp[1])
                    wn = xml_escape(f"{i + 1} {s['vnames'][i]}".strip() if i < len(s["vnames"]) else str(i + 1))
                    out.append(f"<Placemark><name>{wn}</name>{style}<Point><coordinates>{lon_:.8f},{lat_:.8f},0</coordinates></Point></Placemark>")
        out.append("</Document></kml>")
        with open(p, "w", encoding="utf-8") as f:
            f.write("\n".join(out))
        self.tip(f"تم التصدير: {p}")

    def export_geojson(self):
        if not self.need_geo():
            return
        if not self.shapes:
            messagebox.showinfo("تنبيه", "لا توجد عناصر لتصديرها.")
            return
        p = filedialog.asksaveasfilename(defaultextension=".geojson", filetypes=[("GeoJSON", "*.geojson")], title="حفظ GeoJSON")
        if not p:
            return
        feats = []
        for s in self.shapes:
            typ, co = self.geo_geometry(s)
            feats.append({"type": "Feature",
                          "properties": {"name": s.get("text") if s["type"] == "text" else s.get("name", ""),
                                         "kind": s["type"], "color": s["color"]},
                          "geometry": {"type": typ, "coordinates": co if typ != "Polygon" else [co]}})
            if s.get("vnames") is not None:
                for i, pp in enumerate(s["pts"]):
                    lat_, lon_ = self.geo.px_to_ll(pp[0], pp[1])
                    feats.append({"type": "Feature",
                                  "properties": {"name": s["vnames"][i] if i < len(s["vnames"]) else "",
                                                 "kind": "waypoint", "order": i + 1, "route": s.get("name", "")},
                                  "geometry": {"type": "Point", "coordinates": [round(lon_, 8), round(lat_, 8)]}})
        with open(p, "w", encoding="utf-8") as f:
            json.dump({"type": "FeatureCollection", "features": feats}, f, ensure_ascii=False, indent=1)
        self.tip(f"تم التصدير: {p}")

    # ── حفظ الخريطة مع العلامات كـ PDF / PNG ──────────────────────────────
    def export_png(self):
        self.save_map_dialog("png")

    def save_pdf(self):
        self.save_map_dialog("pdf")

    def save_map_dialog(self, fmt="pdf"):
        if self.img is None:
            return
        if getattr(self, "_export_busy", False):
            messagebox.showinfo("تنبيه", "هناك عملية حفظ جارية، انتظر حتى تنتهي.")
            return
        win = tk.Toplevel(self.root)
        win.title("حفظ الخريطة كـ PDF" if fmt == "pdf" else "حفظ الخريطة كصورة PNG")
        win.transient(self.root)
        win.resizable(False, False)
        area = tk.StringVar(value="whole")
        qual = tk.StringVar(value="1.0")
        tbl = tk.BooleanVar(value=bool(self.shapes))
        tgt = tk.BooleanVar(value=self.target is not None and not self.track_var.get())
        pad = {"anchor": "e", "padx": 14}
        tk.Label(win, text="ما الذي تريد حفظه؟", font=("Segoe UI", 10, "bold")).pack(pady=(12, 2), **pad)
        ttk.Radiobutton(win, text="كامل الخريطة مع كل العلامات والرسومات", variable=area, value="whole").pack(**pad)
        ttk.Radiobutton(win, text="المنطقة الظاهرة على الشاشة الآن فقط", variable=area, value="view").pack(**pad)
        tk.Label(win, text="الدقة (تؤثر على حجم الملف)", font=("Segoe UI", 10, "bold")).pack(pady=(10, 2), **pad)
        ttk.Radiobutton(win, text="دقة كاملة — أفضل جودة (ملف أكبر)", variable=qual, value="1.0").pack(**pad)
        ttk.Radiobutton(win, text="متوسطة — نصف الدقة", variable=qual, value="0.5").pack(**pad)
        ttk.Radiobutton(win, text="خفيفة — ربع الدقة (ملف صغير)", variable=qual, value="0.25").pack(**pad)
        tk.Label(win, text="إضافات", font=("Segoe UI", 10, "bold")).pack(pady=(10, 2), **pad)
        if fmt == "pdf":
            ttk.Checkbutton(win, text="صفحة إضافية بجدول العلامات والمسارات وإحداثياتها", variable=tbl).pack(**pad)
        ttk.Checkbutton(win, text="إظهار الموقع المحدد (الدائرة البنفسجية) إن وُجد", variable=tgt).pack(**pad)
        btns = ttk.Frame(win)
        btns.pack(fill="x", padx=14, pady=14)

        def go():
            opts = {"whole": area.get() == "whole", "q": float(qual.get()),
                    "table": bool(tbl.get()) and fmt == "pdf", "target": bool(tgt.get())}
            win.destroy()
            self.ask_path_and_export(fmt, opts)

        ttk.Button(btns, text="حفظ…", command=go).pack(side="right", padx=3)
        ttk.Button(btns, text="إلغاء", command=win.destroy).pack(side="right", padx=3)
        win.grab_set()

    def ask_path_and_export(self, fmt, opts):
        base = os.path.splitext(os.path.basename(self.img_path or "map"))[0]
        docs = os.path.join(os.path.expanduser("~"), "Documents")
        p = filedialog.asksaveasfilename(
            title="حفظ الخريطة", defaultextension=".pdf" if fmt == "pdf" else ".png",
            initialdir=docs if os.path.isdir(docs) else os.path.expanduser("~"),
            initialfile=f"{base}_{time.strftime('%Y-%m-%d')}",
            filetypes=[("PDF", "*.pdf")] if fmt == "pdf" else [("PNG", "*.png")])
        if p:
            self.run_export(p, fmt, opts)

    def run_export(self, path, fmt, opts):
        W, H = self.img.size
        z = self.zoom
        q = opts["q"]
        if opts["whole"]:
            box = (0, 0, W, H)
            T = q
            R = max(1.0, W * T / 1450.0)
        else:
            cw, ch = self.canvas.winfo_width(), self.canvas.winfo_height()
            x0, y0 = self.s2i(0, 0)
            x1, y1 = self.s2i(cw, ch)
            box = (max(0.0, x0), max(0.0, y0), min(float(W), x1), min(float(H), y1))
            if box[2] - box[0] < 2 or box[3] - box[1] < 2:
                messagebox.showinfo("تنبيه", "لا توجد منطقة ظاهرة من الخريطة لحفظها.")
                return
            R = max(2.0, 1.0 / z) * q
            T = R * z
        # سقف لحجم الصورة الناتجة
        while (box[2] - box[0]) * T * (box[3] - box[1]) * T > 120e6 or (box[2] - box[0]) * T > 16000:
            T *= 0.9
            R *= 0.9
        lk = 0
        while lk < 10 and T * (2 ** (lk + 1)) <= 1.0 + 1e-9:
            lk += 1
        self.get_level(lk)                                  # يُبنى هنا (الخيط الرئيسي) قبل بدء العمل
        target = self.target if (opts["target"] and self.target is not None) else None
        tdd = f"{self.field_vars['dd.lat'].get()}, {self.field_vars['dd.lon'].get()}" if target else ""
        shapes = copy.deepcopy(self.shapes)
        title = f"{os.path.splitext(os.path.basename(self.img_path or 'map'))[0]} — MapCoords"
        args = dict(path=path, fmt=fmt, base_levels=self.get_level, W=W, H=H, shapes=shapes, geo=self.geo,
                    k=self.mark_scale.get(), box=box, T=T, R=R, target=target, target_dd=tdd,
                    with_table=opts["table"], title=title)
        st = {"msg": "جارٍ التجهيز…", "done": False, "err": None}
        args["status"] = lambda m: st.__setitem__("msg", m)

        def job():
            try:
                export_map_file(**args)
            except Exception as ex:                          # noqa
                import traceback
                st["err"] = (ex, traceback.format_exc())
            st["done"] = True

        self._export_busy = True
        dlg = tk.Toplevel(self.root)
        dlg.title("جارٍ الحفظ")
        dlg.transient(self.root)
        dlg.resizable(False, False)
        dlg.protocol("WM_DELETE_WINDOW", lambda: None)
        lbl = tk.Label(dlg, text=st["msg"], font=("Segoe UI", 11), width=44)
        lbl.pack(padx=20, pady=(16, 6))
        pb = ttk.Progressbar(dlg, mode="indeterminate", length=320)
        pb.pack(padx=20, pady=(0, 6))
        pb.start(12)
        tk.Label(dlg, text="قد يستغرق الأمر بضع عشرات من الثواني للخرائط الكبيرة", fg="#6b7280").pack(pady=(0, 14))
        dlg.update_idletasks()
        threading.Thread(target=job, daemon=True).start()

        def poll():
            lbl.config(text=st["msg"])
            if not st["done"]:
                self.root.after(120, poll)
                return
            pb.stop()
            dlg.destroy()
            self._export_busy = False
            if st["err"]:
                messagebox.showerror("تعذّر الحفظ", f"{st['err'][0]}")
                return
            self.tip(f"تم الحفظ: {path}")
            if AR_MISSING["hit"] and not (_USE_RAQM or _AR_OK):
                AR_MISSING["hit"] = False
                messagebox.showinfo("النص العربي", "حُفظ الملف، لكن الأسماء العربية قد تظهر غير متصلة.\n"
                                    "لعلاج ذلك ثبّت:  pip install arabic-reshaper python-bidi  ثم أعد بناء البرنامج.")
            if messagebox.askyesno("تم الحفظ", f"تم حفظ الملف:\n{path}\n\nهل تريد فتحه الآن؟"):
                try:
                    if sys.platform.startswith("win"):
                        os.startfile(path)                   # noqa
                    else:
                        import subprocess
                        subprocess.Popen(["xdg-open", path])
                except Exception:
                    pass

        self.root.after(150, poll)

    def show_help(self):
        win = tk.Toplevel(self.root)
        win.title("طريقة الاستخدام")
        win.geometry("640x620")
        t = tk.Text(win, wrap="word", font=("Segoe UI", 11), padx=12, pady=10)
        t.pack(fill="both", expand=True)
        t.insert("1.0", HELP_TEXT)
        t.tag_configure("r", justify="right")
        t.tag_add("r", "1.0", "end")
        t.config(state="disabled")

    # ── التحقق من التحديثات ───────────────────────────────────────────────
    def _start_update_check_bg(self):
        """فحص صامت في الخلفية عند الإقلاع — لا يزعج المستخدم إن فشل الاتصال."""
        def worker():
            try:
                info = check_for_update(timeout=8)
            except Exception:
                return
            if info:
                self.root.after(0, lambda: self._on_update_found(info, silent=True))
        threading.Thread(target=worker, daemon=True).start()

    def check_update_manual(self):
        """فحص يدوي من قائمة مساعدة — يُظهر النتيجة دائماً."""
        self.set_msg("جارٍ البحث عن تحديث…", "info")

        def worker():
            info = None
            err = None
            try:
                info = check_for_update(timeout=12)
            except Exception as ex:
                err = str(ex)
            self.root.after(0, lambda: self._done_manual_check(info, err))

        threading.Thread(target=worker, daemon=True).start()

    def _done_manual_check(self, info, err):
        self.set_msg("", "info")
        if err:
            messagebox.showerror("تعذّر التحقق من التحديثات",
                                 f"لم يستطع التطبيق الاتصال بخادم التحديثات:\n\n{err}")
            return
        if info:
            self._on_update_found(info, silent=False)
            self.show_update_dialog()
        else:
            messagebox.showinfo("لا يوجد تحديث",
                                f"أنت تستخدم آخر إصدار متاح ({APP_VERSION}).")

    def _on_update_found(self, info, silent=True):
        """يخزّن معلومات التحديث ويظهر زر أخضر في شريط الحالة."""
        self._update_info = info
        if self._update_btn is not None and self._update_btn.winfo_exists():
            return
        try:
            self.st_version.pack_forget()
        except Exception:
            pass
        btn = tk.Button(
            self.status_bar,
            text=f"🆕  تحديث متاح إلى v{info['version']} — انقر للتنزيل",
            bg="#43a047", fg="white", activebackground="#2e7d32", activeforeground="white",
            font=("Segoe UI", 9, "bold"), relief="raised", bd=1, cursor="hand2",
            padx=10, pady=1, command=self.show_update_dialog)
        btn.pack(side="left", padx=6, pady=1)
        self._update_btn = btn
        if silent:
            self.set_msg(f"🆕 تحديث متاح — v{info['version']}", "info")

    def show_update_dialog(self):
        info = self._update_info
        if not info:
            return
        if self._update_dialog is not None and self._update_dialog.winfo_exists():
            self._update_dialog.deiconify()
            self._update_dialog.lift()
            return
        win = tk.Toplevel(self.root)
        self._update_dialog = win
        win.title("تحديث متاح")
        win.geometry("580x480")
        win.minsize(480, 380)
        try:
            win.transient(self.root)
        except Exception:
            pass

        tk.Label(win, text="🆕  تحديث جديد متاح", font=("Segoe UI", 15, "bold"),
                 fg="#0d47a1").pack(pady=(14, 4))
        tk.Label(win, text=f"الإصدار الحالي:  {APP_VERSION}    ←    الجديد:  {info['version']}",
                 font=("Segoe UI", 11)).pack(pady=2)
        size_mb = info["size"] / 1024 / 1024 if info["size"] else 0
        tk.Label(win, text=(f"حجم التنزيل: {size_mb:.1f} MB" if size_mb else ""),
                 fg="#546e7a").pack()

        tk.Label(win, text="ملاحظات الإصدار:", anchor="e", justify="right",
                 font=("Segoe UI", 10, "bold")).pack(fill="x", padx=14, pady=(12, 2))
        box = tk.Frame(win)
        box.pack(fill="both", expand=True, padx=14, pady=(0, 6))
        notes = tk.Text(box, wrap="word", font=("Segoe UI", 10), height=10, bd=1, relief="solid")
        nsb = ttk.Scrollbar(box, orient="vertical", command=notes.yview)
        notes.configure(yscrollcommand=nsb.set)
        notes.insert("1.0", info.get("notes") or "(لا توجد ملاحظات)")
        notes.tag_configure("r", justify="right")
        notes.tag_add("r", "1.0", "end")
        notes.configure(state="disabled")
        nsb.pack(side="left", fill="y")
        notes.pack(side="right", fill="both", expand=True)

        prog_var = tk.DoubleVar(value=0)
        prog = ttk.Progressbar(win, variable=prog_var, maximum=100)
        prog.pack(fill="x", padx=14, pady=(6, 2))
        status = tk.Label(win, text="", fg="#546e7a", font=("Segoe UI", 9))
        status.pack()

        btns = tk.Frame(win)
        btns.pack(fill="x", padx=14, pady=(8, 12))

        btn_now = ttk.Button(btns, text="تحديث الآن")
        btn_later = ttk.Button(btns, text="لاحقاً", command=win.destroy)
        btn_now.pack(side="right", padx=4)
        btn_later.pack(side="left", padx=4)

        def do_update():
            btn_now.configure(state="disabled")
            btn_later.configure(state="disabled")
            self._download_and_install(info, prog_var, status, win)

        btn_now.configure(command=do_update)

    def _download_and_install(self, info, prog_var, status, win):
        """ينزّل EXE الجديد إلى temp، ثم يشغّل PowerShell يستبدل الملف ويعيد التشغيل."""
        import urllib.request
        import tempfile
        import subprocess

        def worker():
            dl = None
            try:
                fd, dl = tempfile.mkstemp(suffix=".exe", prefix="MapCoords_new_")
                os.close(fd)
                status.after(0, lambda: status.config(text="جارٍ التنزيل…", fg="#0d47a1"))
                req = urllib.request.Request(info["url"],
                                             headers={"User-Agent": f"MapCoords/{APP_VERSION}"})
                with urllib.request.urlopen(req, timeout=30, context=_https_context()) as resp:
                    total = int(resp.headers.get("Content-Length") or 0)
                    got = 0
                    with open(dl, "wb") as fh:
                        while True:
                            chunk = resp.read(128 * 1024)
                            if not chunk:
                                break
                            fh.write(chunk)
                            got += len(chunk)
                            if total > 0:
                                pct = got * 100.0 / total
                                mb_got = got / 1024 / 1024
                                mb_tot = total / 1024 / 1024
                                status.after(0, lambda p=pct, g=mb_got, t=mb_tot:
                                             (prog_var.set(p),
                                              status.config(text=f"{g:.1f} / {t:.1f} MB   ({p:.0f}%)")))
                actual = os.path.getsize(dl)
                if info["size"] and actual < info["size"] * 0.9:
                    raise RuntimeError(f"الملف غير كامل ({actual} من {info['size']} بايت).")

                if not getattr(sys, "frozen", False):
                    win.after(0, lambda: (
                        prog_var.set(100),
                        status.config(text="", fg="#546e7a"),
                        messagebox.showinfo("وضع تطوير",
                                            f"تم تنزيل الإصدار الجديد إلى:\n{dl}\n\n"
                                            "الاستبدال التلقائي يعمل فقط عند تشغيل التطبيق كملف EXE.",
                                            parent=win),
                        win.destroy()))
                    return

                current = os.path.abspath(sys.executable)
                # سكربت PowerShell خفيف: انتظر ثم استبدل ثم شغّل
                ps_lines = [
                    "$ErrorActionPreference = 'SilentlyContinue'",
                    "Start-Sleep -Seconds 2",
                    f"$src = '{dl.replace(chr(39), chr(39)*2)}'",
                    f"$dst = '{current.replace(chr(39), chr(39)*2)}'",
                    "for ($i = 0; $i -lt 40; $i++) {",
                    "  try { Move-Item -Force -LiteralPath $src -Destination $dst -ErrorAction Stop; break }",
                    "  catch { Start-Sleep -Milliseconds 500 }",
                    "}",
                    "Start-Process -FilePath $dst",
                ]
                ps_cmd = "; ".join(ps_lines)
                flags = 0
                if hasattr(subprocess, "CREATE_NO_WINDOW"):
                    flags |= subprocess.CREATE_NO_WINDOW
                if hasattr(subprocess, "DETACHED_PROCESS"):
                    flags |= subprocess.DETACHED_PROCESS
                subprocess.Popen(
                    ["powershell", "-NoProfile", "-WindowStyle", "Hidden", "-Command", ps_cmd],
                    creationflags=flags, close_fds=True)

                win.after(0, lambda: (
                    prog_var.set(100),
                    status.config(text="✔ تم التنزيل — سيُعاد تشغيل التطبيق بالإصدار الجديد…",
                                  fg="#2e7d32")))
                self.root.after(1800, self.root.destroy)
            except Exception as ex:
                if dl and os.path.exists(dl):
                    try:
                        os.remove(dl)
                    except OSError:
                        pass
                msg = str(ex)
                win.after(0, lambda: (
                    status.config(text="✗ فشل التنزيل", fg="#c62828"),
                    messagebox.showerror("خطأ", f"فشل تنزيل التحديث:\n\n{msg}", parent=win)))

        threading.Thread(target=worker, daemon=True).start()


def main():
    try:
        import ctypes
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:
        pass
    root = tk.Tk()
    try:
        ttk.Style().theme_use("vista")
    except Exception:
        pass
    app = App(root)
    if len(sys.argv) > 1 and os.path.isfile(sys.argv[1]):
        root.after(200, lambda: app.open_image(sys.argv[1]))
    elif os.path.isfile(resource_path(DEFAULT_MAP)):
        root.after(200, app.open_default_map)
    root.mainloop()


if __name__ == "__main__":
    main()
