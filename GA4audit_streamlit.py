import os
import re
import json
import time
import glob
import base64
import shutil
import subprocess
import uuid
from datetime import datetime, timezone, timedelta
from typing import List, Dict, Any, Tuple, Optional, Set
from urllib.parse import urlparse, parse_qs, urlunparse, unquote_plus
from zoneinfo import ZoneInfo

import pandas as pd
import requests
import streamlit as st
from bs4 import BeautifulSoup
try:
    import extra_streamlit_components as stx
except Exception:
    stx = None
try:
    import gspread
    from google.oauth2.service_account import Credentials
except Exception:
    gspread = None
    Credentials = None
from seleniumwire import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.common.exceptions import JavascriptException
from selenium.webdriver.common.by import By
from selenium.webdriver.remote.webelement import WebElement

# Shared GA4 mapping helpers

def safe_json(obj):
    try:
        return json.dumps(obj, ensure_ascii=False, indent=2)
    except Exception:
        try:
            return json.dumps(str(obj), ensure_ascii=False)
        except Exception:
            return ""


def _safe_json_load(value, fallback):
    if isinstance(value, str):
        try:
            value = json.loads(value)
        except Exception:
            return fallback
    return value if isinstance(value, type(fallback)) else fallback


def normalize_single_url(raw_value: str):
    text = str(raw_value or "").strip()
    if not text:
        return "", "", "Please enter a URL."

    tokens = [token.strip() for token in text.replace(",", " ").split() if token.strip()]
    if len(tokens) != 1:
        return "", "", "Please enter only one URL."

    original = tokens[0]
    candidate = original
    had_scheme = "://" in candidate
    if not had_scheme:
        candidate = f"https://{candidate}"

    parsed = urlparse(candidate)
    if not parsed.netloc and parsed.path:
        parsed = urlparse(f"https://{parsed.path}")

    host = (parsed.netloc or "").strip()
    if not host or "." not in host:
        return "", "", "Please enter a valid URL."

    if not had_scheme and not host.startswith("www.") and host.count(".") == 1:
        host = f"www.{host}"

    normalized = urlunparse(
        (
            parsed.scheme or "https",
            host,
            parsed.path or "/",
            parsed.params,
            parsed.query,
            parsed.fragment,
        )
    )
    return original, normalized, ""


def _flatten_qs(values):
    flat = {}
    for key, raw in values.items():
        if isinstance(raw, list):
            flat[key] = raw[0] if raw else ""
        else:
            flat[key] = raw
    return flat


def _stringify_value(value):
    if value is None:
        return ""
    if isinstance(value, (dict, list)):
        return json.dumps(value, ensure_ascii=False, sort_keys=True)
    return str(value)


def _normalize_key(name: str) -> str:
    if not isinstance(name, str):
        return ""

    name = name.strip()
    for prefix in ("ep.", "epn.", "epf.", "up.", "upn.", "cdp.", "tvc_"):
        if name.startswith(prefix):
            name = name[len(prefix):]
            break

    return name.replace("_", "").lower()


def decode_ga4_collect_url(url: str) -> dict:
    parsed = urlparse(url)
    flat = _flatten_qs(parse_qs(parsed.query))

    event_name = flat.get("en", "")
    event_params = {}
    user_properties = {}

    for key, value in flat.items():
        if key.startswith(("ep.", "epn.", "epf.")):
            clean_key = key.split(".", 1)[1]
            event_params[clean_key] = value
        elif key.startswith(("up.", "upn.")):
            clean_key = key.split(".", 1)[1]
            user_properties[clean_key] = value

    fallback_fields = {
        "dl": "page_location",
        "dt": "page_title",
        "dr": "page_referrer",
        "ul": "browser_language",
    }
    for raw_key, clean_key in fallback_fields.items():
        if raw_key in flat and clean_key not in event_params:
            event_params[clean_key] = flat[raw_key]

    return {
        "event_name": event_name,
        "params": event_params,
        "event_params": event_params,
        "user_properties": user_properties,
        "raw_fields": flat,
    }


def merge_ga4_events(event_list):
    merged = []

    for event in event_list or []:
        if not isinstance(event, dict):
            continue

        params = {}
        raw_params = event.get("params")
        if isinstance(raw_params, dict):
            params.update(raw_params)

        event_params = event.get("event_params")
        if isinstance(event_params, dict):
            params.update(event_params)

        user_properties = event.get("user_properties")
        if isinstance(user_properties, dict):
            params.update(user_properties)
        else:
            user_properties = {}

        merged.append(
            {
                "event_name": event.get("event_name") or event.get("en") or "",
                "params": params,
                "user_properties": user_properties,
                "raw_fields": event.get("raw_fields", {}),
            }
        )

    return merged


def _collect_param_values(event_list):
    params = {}
    for event in merge_ga4_events(event_list):
        raw = event.get("params")
        if not isinstance(raw, dict):
            continue
        for key, value in raw.items():
            norm = _normalize_key(key)
            if not norm:
                continue
            entry = params.setdefault(norm, {"key": key, "values": []})
            value_text = _stringify_value(value)
            if value_text and value_text not in entry["values"]:
                entry["values"].append(value_text)
    return params


def _normalize_event_key(name: str) -> str:
    return str(name or "").strip().lower().replace("_", "")


def _matching_score(event: dict, dl_event: dict):
    params = event.get("params") or {}
    if not isinstance(params, dict):
        params = {}

    event_keys = {_normalize_key(key) for key in params.keys() if _normalize_key(key)}
    dl_keys = {
        _normalize_key(key)
        for key in (dl_event or {}).keys()
        if key != "event" and not str(key).startswith("gtm") and _normalize_key(key)
    }
    overlap_count = len(event_keys & dl_keys)
    return overlap_count, len(event_keys)


def _best_matching_event(event_list, target_event_name: str, dl_event: dict):
    target = _normalize_event_key(target_event_name)
    if not target:
        return None

    best_event = None
    best_score = (-1, -1, -1)

    for index, event in enumerate(merge_ga4_events(event_list)):
        if _normalize_event_key(event.get("event_name")) != target:
            continue
        overlap_count, param_count = _matching_score(event, dl_event)
        score = (overlap_count, param_count, index)
        if score >= best_score:
            best_event = event
            best_score = score

    if best_event:
        return best_event

    for event in merge_ga4_events(event_list):
        if _normalize_event_key(event.get("event_name")) == target:
            return event
    return None


def _compact_values(values):
    if not values:
        return None
    if len(values) == 1:
        return values[0]
    return values


def map_dl_to_ga4(
    pageview_event_json,
    ga4_exec_events_json,
    ga4_network_events_json,
):
    dl_event = _safe_json_load(pageview_event_json, {})
    exec_events = _safe_json_load(ga4_exec_events_json, [])
    network_events = _safe_json_load(ga4_network_events_json, [])

    target_event_name = dl_event.get("event") or "page_view"
    exec_event = _best_matching_event(exec_events, target_event_name, dl_event)
    network_event = _best_matching_event(network_events, target_event_name, dl_event)

    exec_params = _collect_param_values([exec_event] if exec_event else [])
    network_params = _collect_param_values([network_event] if network_event else [])

    rows = []
    matched_exec = set()
    matched_network = set()

    for dl_key, dl_value in dl_event.items():
        if dl_key == "event" or str(dl_key).startswith("gtm"):
            continue

        dl_norm = _normalize_key(dl_key)

        exec_entry = exec_params.get(dl_norm)
        exec_key = exec_entry["key"] if exec_entry else None
        exec_value = _compact_values(exec_entry["values"]) if exec_entry else None
        if exec_entry:
            matched_exec.add(dl_norm)

        ga4_entry = network_params.get(dl_norm)
        ga4_key = ga4_entry["key"] if ga4_entry else None
        ga4_value = _compact_values(ga4_entry["values"]) if ga4_entry else None
        if ga4_entry:
            matched_network.add(dl_norm)

        rows.append(
            {
                "dl_key": dl_key,
                "dl_value": dl_value,
                "exec_key": exec_key,
                "exec_value": exec_value,
                "ga4_key": ga4_key,
                "ga4_value": ga4_value,
            }
        )

    for norm_key, ga4_entry in network_params.items():
        if norm_key in matched_network:
            continue
        rows.append(
            {
                "dl_key": None,
                "dl_value": None,
                "exec_key": None,
                "exec_value": None,
                "ga4_key": ga4_entry["key"],
                "ga4_value": _compact_values(ga4_entry["values"]),
            }
        )

    for norm_key, exec_entry in exec_params.items():
        if norm_key in matched_exec:
            continue
        rows.append(
            {
                "dl_key": None,
                "dl_value": None,
                "exec_key": exec_entry["key"],
                "exec_value": _compact_values(exec_entry["values"]),
                "ga4_key": None,
                "ga4_value": None,
            }
        )

    return rows


def map_dl_to_execution_and_ga4(
    pageview_event_json,
    ga4_exec_events_json,
    ga4_network_events_json,
):
    return map_dl_to_ga4(
        pageview_event_json,
        ga4_exec_events_json,
        ga4_network_events_json,
    )

# Network hit patterns and consent selectors

# -------------------------
# Regex patterns for network hits
# -------------------------

GTM_SCRIPT_PATTERN = re.compile(
    r"https://www\.googletagmanager\.com/gtm\.js\?id=GTM-[A-Z0-9]+",
    re.IGNORECASE,
)

GTAG_SCRIPT_PATTERN = re.compile(
    r"https://www\.googletagmanager\.com/gtag/js\?id=G-[A-Z0-9A-Z]+",
    re.IGNORECASE,
)

GA4_COLLECT_PATTERN = re.compile(
    r"https://[a-z0-9\.-]*google-analytics\.com/.*/collect",
    re.IGNORECASE,
)

CCM_PAGEVIEW_PATTERN = re.compile(
    r"https://www\.google\.com/ccm/collect\?en=page_view",
    re.IGNORECASE,
)

CONSENT_BUTTON_TEXT_PATTERN = re.compile(
    r"\b(accept|allow all|allow cookies|agree|i agree|ok|got it|continue|consent|accept all)\b",
    re.IGNORECASE,
)

COMMON_CONSENT_SELECTORS = [
    "#onetrust-accept-btn-handler",
    ".onetrust-accept-btn-handler",
    "#CybotCookiebotDialogBodyLevelButtonLevelOptinAllowAll",
    "#didomi-notice-agree-button",
    "[id*='didomi-notice-agree-button']",
    "[data-testid*='accept']",
    "[aria-label*='Accept']",
    "[class*='accept']",
    "[id*='accept']",
    "button",
    "[role='button']",
    "a",
]

# Embedded GA4 audit engine

def create_driver(headless: bool = True):
    chrome_options = Options()
    if headless:
        chrome_options.add_argument("--headless=new")

    chrome_options.add_argument("--no-sandbox")
    chrome_options.add_argument("--disable-dev-shm-usage")
    chrome_options.add_argument("--disable-gpu")
    chrome_options.add_argument("--disable-quic")
    chrome_options.add_argument("--window-size=1920,1080")

    # Anti-bot / more human-like
    chrome_options.add_argument("--disable-blink-features")
    chrome_options.add_argument("--disable-blink-features=AutomationControlled")
    chrome_options.add_argument("--disable-infobars")
    chrome_options.add_argument("--disable-web-security")
    chrome_options.add_argument("--allow-running-insecure-content")
    chrome_options.add_argument(
        "--disable-features=IsolateOrigins,site-per-process,BlockInsecurePrivateNetworkRequests"
    )
    chrome_options.add_argument(
        "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"
    )
    chrome_options.set_capability("goog:loggingPrefs", {"performance": "ALL"})

    chrome_binary = os.environ.get("CHROME_BINARY")
    binary_candidates = [
        chrome_binary,
        "/usr/bin/chromium",
        "/usr/bin/chromium-browser",
        "/usr/bin/google-chrome",
        "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    ]
    browser_cmd = ""
    for candidate in binary_candidates:
        if candidate and os.path.exists(candidate):
            chrome_options.binary_location = candidate
            browser_cmd = candidate
            break
    if not browser_cmd:
        browser_cmd = chrome_binary or ""

    def _major_version(text: str) -> str:
        match = re.search(r"(\d+)\.", text or "")
        return match.group(1) if match else ""

    def _read_version(command_path: str) -> str:
        if not command_path or not os.path.exists(command_path):
            return ""
        try:
            proc = subprocess.run(
                [command_path, "--version"],
                capture_output=True,
                text=True,
                check=False,
                timeout=5,
            )
            return (proc.stdout or proc.stderr).strip()
        except Exception:
            return ""

    browser_version = _read_version(browser_cmd)
    browser_major = _major_version(browser_version)

    def _locate_cached_chromedriver(target_major: str) -> str:
        cache_root = os.path.expanduser("~/.cache/selenium/chromedriver")
        candidates = []
        for path in glob.glob(os.path.join(cache_root, "**", "chromedriver"), recursive=True):
            version_text = _read_version(path)
            major = _major_version(version_text)
            score = 0
            if target_major and major == target_major:
                score = 2
            elif not target_major:
                score = 1
            else:
                continue
            try:
                mtime = os.path.getmtime(path)
            except OSError:
                mtime = 0
            candidates.append((score, mtime, path))
        if not candidates:
            return ""
        candidates.sort(reverse=True)
        return candidates[0][2]

    chromedriver_path = os.environ.get("CHROMEDRIVER_PATH") or _locate_cached_chromedriver(browser_major)
    if not chromedriver_path:
        for candidate in ("/usr/bin/chromedriver", shutil.which("chromedriver")):
            if candidate and os.path.exists(candidate):
                chromedriver_path = candidate
                break
    service = Service(executable_path=chromedriver_path) if chromedriver_path else None

    try:
        if service:
            driver = webdriver.Chrome(options=chrome_options, service=service)
        else:
            driver = webdriver.Chrome(options=chrome_options)
        try:
            driver.execute_cdp_cmd("Network.enable", {})
            driver.execute_cdp_cmd("Network.setCacheDisabled", {"cacheDisabled": True})
        except Exception:
            pass
        return driver
    except Exception as exc:
        driver_version = _read_version(chromedriver_path or shutil.which("chromedriver") or "")
        resolved_driver = chromedriver_path or shutil.which("chromedriver")

        details = []
        if browser_version:
            details.append(f"Chrome: {browser_version}")
        if driver_version:
            details.append(f"ChromeDriver: {driver_version}")
        if resolved_driver:
            details.append(f"Driver path: {resolved_driver}")

        message = str(exc)
        if details:
            message = f"{message}\n" + "\n".join(details)
        if "only supports Chrome version" in message:
            message += (
                "\nSet CHROMEDRIVER_PATH to a matching driver or update the "
                "installed chromedriver to the same major version as Chrome."
            )
        raise RuntimeError(message) from exc


def extract_datalayer(driver) -> Tuple[list, Optional[str]]:
    try:
        dl = driver.execute_script("return window.dataLayer || []")
        if not isinstance(dl, list):
            dl = [dl]
        return dl, None
    except JavascriptException as e:
        return [], f"JavascriptException: {e}"
    except Exception as e:
        return [], f"Error: {e}"


def _norm_event_name(ev: Any) -> str:
    s = str(ev or "").strip().lower()
    return s.replace("_", "")


def find_pageview_event(data_layer_list: list) -> Optional[dict]:
    pageview_event = None
    for item in data_layer_list:
        if isinstance(item, dict):
            ev_norm = _norm_event_name(item.get("event"))
            if ev_norm == "pageview":
                pageview_event = item
    return pageview_event


def find_events_by_name(data_layer_list: list, names: List[str]) -> List[dict]:
    target = {_norm_event_name(n) for n in names}
    matches: List[dict] = []
    for item in data_layer_list:
        if isinstance(item, dict):
            ev_norm = _norm_event_name(item.get("event"))
            if ev_norm in target:
                matches.append(item)
    return matches


def _case_insensitive_get(d: Dict[str, Any], key: str) -> Any:
    key_lower = key.lower()
    for k, v in d.items():
        if k.lower() == key_lower:
            return v
    return None


GA4_CONTEXT_FIELD_MAP = {
    "dl": "page_location",
    "dt": "page_title",
    "dr": "page_referrer",
    "ul": "browser_language",
    "tid": "measurement_id",
    "cid": "client_id",
    "sid": "session_id",
}

COMSCORE_PARAM_KEYS = ("c1", "c2", "c7", "c8")
COMSCORE_HOST_PATTERN = re.compile(r"(?:^|[.])scorecardresearch\.com$", re.I)
COMSCORE_JS_PATTERN = re.compile(r"scorecardresearch\.com/(?:c2/\d+/)?beacon\.js", re.I)
COMSCORE_JS_C1_RE = re.compile(
    r"""(?:
        [\s'"=]c1[\s'"]*[:=][\s'"]*([0-9]{1,6})
        |
        ["']?c1["']?\s*[:=]\s*["']?([0-9]{1,6})["']?
    )""",
    re.I | re.X,
)
COMSCORE_JS_C2_RE = re.compile(
    r"""(?:
        [\s'"=]c2[\s'"]*[:=][\s'"]*([0-9]{4,12})
        |
        ["']?c2["']?\s*[:=]\s*["']?([0-9]{4,12})["']?
    )""",
    re.I | re.X,
)
COMSCORE_GENERIC_PARAM_RE = re.compile(r"(?:[?&]|\b)(c1|c2|c7|c8)=([^&'\"\\s]+)", re.I)

GA4_PRELOAD_SCRIPT = r"""
(function () {
    try {
        var state = window.__ga4AuditState = window.__ga4AuditState || {
            dataLayerPushes: [],
            gtagCalls: [],
            transportHits: []
        };

        function trim(list) {
            if (list.length > 500) {
                list.splice(0, list.length - 500);
            }
        }

        function safeClone(value, depth) {
            depth = depth || 0;
            if (depth > 5) {
                return "[MaxDepth]";
            }
            if (value === null || value === undefined) {
                return value;
            }
            var type = typeof value;
            if (type === "string" || type === "number" || type === "boolean") {
                return value;
            }
            if (type === "function") {
                return "[Function]";
            }
            if (typeof Element !== "undefined" && value instanceof Element) {
                return "<" + value.tagName.toLowerCase() + ">";
            }
            if (Array.isArray(value)) {
                return value.slice(0, 50).map(function (entry) {
                    return safeClone(entry, depth + 1);
                });
            }
            if (typeof URLSearchParams !== "undefined" && value instanceof URLSearchParams) {
                return value.toString();
            }
            if (typeof FormData !== "undefined" && value instanceof FormData) {
                var pairs = [];
                value.forEach(function (entryValue, entryKey) {
                    pairs.push(encodeURIComponent(entryKey) + "=" + encodeURIComponent(String(entryValue)));
                });
                return pairs.join("&");
            }
            if (typeof Blob !== "undefined" && value instanceof Blob) {
                return "[Blob size=" + value.size + "]";
            }
            if (typeof ArrayBuffer !== "undefined" && value instanceof ArrayBuffer) {
                return "[ArrayBuffer byteLength=" + value.byteLength + "]";
            }
            if (typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView && ArrayBuffer.isView(value)) {
                return "[TypedArray byteLength=" + value.byteLength + "]";
            }
            if (type === "object") {
                var output = {};
                Object.keys(value).slice(0, 100).forEach(function (key) {
                    try {
                        output[key] = safeClone(value[key], depth + 1);
                    } catch (error) {}
                });
                return output;
            }
            return String(value);
        }

        function push(target, payload) {
            try {
                state[target].push(Object.assign({ timestamp: Date.now() }, payload));
                trim(state[target]);
            } catch (error) {}
        }

        function isGaUrl(url) {
            return typeof url === "string" && /(google-analytics\.com\/(g|j|r)\/collect|analytics\.google\.com\/g\/collect|google\.com\/ccm\/collect)/i.test(url);
        }

        function asText(data) {
            try {
                if (data === null || data === undefined) {
                    return "";
                }
                if (typeof data === "string") {
                    return data;
                }
                if (typeof URLSearchParams !== "undefined" && data instanceof URLSearchParams) {
                    return data.toString();
                }
                if (typeof FormData !== "undefined" && data instanceof FormData) {
                    var pairs = [];
                    data.forEach(function (entryValue, entryKey) {
                        pairs.push(encodeURIComponent(entryKey) + "=" + encodeURIComponent(String(entryValue)));
                    });
                    return pairs.join("&");
                }
                if (typeof Blob !== "undefined" && data instanceof Blob) {
                    return "[Blob size=" + data.size + "]";
                }
                if (typeof ArrayBuffer !== "undefined" && data instanceof ArrayBuffer) {
                    return "[ArrayBuffer byteLength=" + data.byteLength + "]";
                }
                if (typeof ArrayBuffer !== "undefined" && ArrayBuffer.isView && ArrayBuffer.isView(data)) {
                    return "[TypedArray byteLength=" + data.byteLength + "]";
                }
                return String(data);
            } catch (error) {
                return "[unserializable]";
            }
        }

        function recordTransport(api, url, method, body) {
            try {
                if (!isGaUrl(url)) {
                    return;
                }
                push("transportHits", {
                    api: api,
                    url: String(url || ""),
                    method: String(method || "GET").toUpperCase(),
                    bodyText: asText(body)
                });
            } catch (error) {}
        }

        function wrapDataLayer(list) {
            if (!list) {
                list = [];
            }
            if (list.__ga4AuditWrappedPush) {
                return list;
            }
            var originalPush = typeof list.push === "function" ? list.push : Array.prototype.push;
            Object.defineProperty(list, "__ga4AuditWrappedPush", {
                value: true,
                configurable: true
            });
            list.push = function () {
                var args = Array.prototype.slice.call(arguments);
                push("dataLayerPushes", { args: safeClone(args) });
                return originalPush.apply(this, arguments);
            };
            return list;
        }

        var currentDataLayer = wrapDataLayer(window.dataLayer || []);
        Object.defineProperty(window, "dataLayer", {
            configurable: true,
            enumerable: true,
            get: function () {
                return currentDataLayer;
            },
            set: function (value) {
                currentDataLayer = wrapDataLayer(value || []);
            }
        });
        window.dataLayer = currentDataLayer;

        function wrapGtag(original) {
            if (original && original.__ga4AuditWrapped) {
                return original;
            }
            var wrapped = function () {
                var args = Array.prototype.slice.call(arguments);
                push("gtagCalls", {
                    args: safeClone(args),
                    command: args[0],
                    event_name: args[0] === "event" ? args[1] : "",
                    params: args[0] === "event" && args[2] && typeof args[2] === "object"
                        ? safeClone(args[2])
                        : null
                });
                if (typeof original === "function") {
                    return original.apply(this, arguments);
                }
            };
            Object.defineProperty(wrapped, "__ga4AuditWrapped", {
                value: true,
                configurable: true
            });
            return wrapped;
        }

        var currentGtag = typeof window.gtag === "function" ? wrapGtag(window.gtag) : undefined;
        Object.defineProperty(window, "gtag", {
            configurable: true,
            enumerable: true,
            get: function () {
                return currentGtag;
            },
            set: function (value) {
                currentGtag = typeof value === "function" ? wrapGtag(value) : value;
            }
        });
        if (currentGtag) {
            window.gtag = currentGtag;
        }

        if (navigator && typeof navigator.sendBeacon === "function" && !navigator.sendBeacon.__ga4AuditWrapped) {
            var originalSendBeacon = navigator.sendBeacon.bind(navigator);
            var wrappedSendBeacon = function (url, data) {
                recordTransport("sendBeacon", url, "POST", data);
                return originalSendBeacon(url, data);
            };
            wrappedSendBeacon.__ga4AuditWrapped = true;
            navigator.sendBeacon = wrappedSendBeacon;
        }

        if (typeof window.fetch === "function" && !window.fetch.__ga4AuditWrapped) {
            var originalFetch = window.fetch.bind(window);
            var wrappedFetch = function (input, init) {
                var url = typeof input === "string" ? input : (input && input.url) || "";
                var method = (init && init.method) || (input && input.method) || "GET";
                var body = (init && init.body) || null;
                recordTransport("fetch", url, method, body);
                return originalFetch(input, init);
            };
            wrappedFetch.__ga4AuditWrapped = true;
            window.fetch = wrappedFetch;
        }

        if (window.XMLHttpRequest && window.XMLHttpRequest.prototype && !window.XMLHttpRequest.prototype.__ga4AuditWrapped) {
            var proto = window.XMLHttpRequest.prototype;
            var originalOpen = proto.open;
            var originalSend = proto.send;
            proto.open = function (method, url) {
                this.__ga4AuditMeta = { method: method, url: url };
                return originalOpen.apply(this, arguments);
            };
            proto.send = function (body) {
                var meta = this.__ga4AuditMeta || {};
                recordTransport("xhr", meta.url || "", meta.method || "GET", body);
                return originalSend.apply(this, arguments);
            };
            proto.__ga4AuditWrapped = true;
        }

        try {
            var proto = window.HTMLImageElement && window.HTMLImageElement.prototype;
            if (proto) {
                var descriptor = Object.getOwnPropertyDescriptor(proto, "src");
                if (descriptor && descriptor.configurable && descriptor.set && !descriptor.set.__ga4AuditWrapped) {
                    Object.defineProperty(proto, "src", {
                        configurable: true,
                        enumerable: descriptor.enumerable,
                        get: descriptor.get,
                        set: function (value) {
                            recordTransport("image", value, "GET", "");
                            return descriptor.set.call(this, value);
                        }
                    });
                }
            }
        } catch (error) {}
    } catch (error) {}
})();
"""


def _decode_body_bytes(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bytes):
        return value.decode("utf-8", errors="ignore")
    return str(value)


def _truncate_text(value: str, limit: int = 4000) -> str:
    value = value or ""
    if len(value) <= limit:
        return value
    return f"{value[:limit]}... [truncated {len(value) - limit} chars]"


def _safe_headers(headers: Any) -> Dict[str, Any]:
    try:
        return {str(key): str(value) for key, value in dict(headers or {}).items()}
    except Exception:
        return {}


def _flatten_qs(values: Dict[str, List[str]]) -> Dict[str, str]:
    flat: Dict[str, str] = {}
    for key, raw in values.items():
        flat[key] = raw[0] if raw else ""
    return flat


def _parse_ga_payloads(url: str, body_text: str = "") -> List[Dict[str, Any]]:
    parsed = urlparse(url)
    query_payload = _flatten_qs(parse_qs(parsed.query, keep_blank_values=True))
    body_text = (body_text or "").strip()

    if not body_text or "[" in body_text and "byteLength" in body_text:
        return [query_payload]

    payloads: List[Dict[str, Any]] = []
    lines = [line.strip() for line in body_text.splitlines() if line.strip()]

    if len(lines) > 1 and all("=" in line for line in lines):
        for line in lines:
            payloads.append(
                {
                    **query_payload,
                    **_flatten_qs(parse_qs(line, keep_blank_values=True)),
                }
            )
        return payloads

    if "=" in body_text:
        return [
            {
                **query_payload,
                **_flatten_qs(parse_qs(body_text, keep_blank_values=True)),
            }
        ]

    return [{**query_payload, "_body_text": body_text}]


def _decode_ga_payload(payload: Dict[str, Any]) -> Dict[str, Any]:
    event_name = str(payload.get("en") or payload.get("event_name") or "")
    params: Dict[str, Any] = {}
    user_properties: Dict[str, Any] = {}

    for key, value in payload.items():
        if key.startswith(("ep.", "epn.", "epf.")):
            params[key.split(".", 1)[1]] = value
        elif key.startswith(("up.", "upn.")):
            user_properties[key.split(".", 1)[1]] = value

    for raw_key, clean_key in GA4_CONTEXT_FIELD_MAP.items():
        if raw_key in payload and clean_key not in params:
            params[clean_key] = payload[raw_key]

    return {
        "event_name": event_name,
        "params": params,
        "user_properties": user_properties,
        "raw_fields": payload,
    }


def decode_ga4_collect_url(url: str) -> Dict[str, Any]:
    payloads = _parse_ga_payloads(url)
    if not payloads:
        return {"event_name": "", "params": {}, "user_properties": {}, "raw_fields": {}}
    return _decode_ga_payload(payloads[0])


def decode_ga4_collect_request(url: str, body_text: str = "") -> List[Dict[str, Any]]:
    return [_decode_ga_payload(payload) for payload in _parse_ga_payloads(url, body_text)]


def install_preload_instrumentation(driver) -> Tuple[bool, str]:
    try:
        driver.execute_cdp_cmd(
            "Page.addScriptToEvaluateOnNewDocument",
            {"source": GA4_PRELOAD_SCRIPT},
        )
        return True, ""
    except Exception as exc:
        return False, str(exc)


def extract_preload_state(driver) -> Dict[str, Any]:
    try:
        state = driver.execute_script(
            "return window.__ga4AuditState ? "
            "JSON.parse(JSON.stringify(window.__ga4AuditState)) : {};"
        )
        return state if isinstance(state, dict) else {}
    except Exception:
        return {}


def normalize_gtag_calls(gtag_calls: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    events: List[Dict[str, Any]] = []
    for call in gtag_calls or []:
        if not isinstance(call, dict):
            continue
        if call.get("command") != "event":
            continue
        params = call.get("params")
        if not isinstance(params, dict):
            params = {}
        events.append(
            {
                "event_name": call.get("event_name") or "",
                "params": params,
                "timestamp": call.get("timestamp"),
            }
        )
    return events


def normalize_transport_hits(preload_state: Dict[str, Any]) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    hits: List[Dict[str, Any]] = []
    events: List[Dict[str, Any]] = []

    for hit in preload_state.get("transportHits", []) or []:
        if not isinstance(hit, dict):
            continue
        url = str(hit.get("url") or "")
        body_text = _truncate_text(str(hit.get("bodyText") or ""))
        decoded_events = decode_ga4_collect_request(url, body_text)
        normalized_hit = {
            "transport": hit.get("api"),
            "request_url": url,
            "method": hit.get("method") or "GET",
            "request_body": body_text,
            "timestamp": hit.get("timestamp"),
            "decoded_events": decoded_events,
        }
        hits.append(normalized_hit)
        events.extend(decoded_events)

    return hits, events


def _is_comscore_hit(url: str) -> bool:
    parsed = urlparse(str(url or ""))
    host = parsed.netloc.lower().split(":", 1)[0]
    return bool(COMSCORE_HOST_PATTERN.search(host))


def _merge_multivalue_dicts(base: Dict[str, List[str]], extra: Dict[str, List[str]]) -> Dict[str, List[str]]:
    merged = {key: list(values) for key, values in (base or {}).items()}
    for key, values in (extra or {}).items():
        bucket = merged.setdefault(key, [])
        for value in values or []:
            value_text = str(value)
            if value_text not in bucket:
                bucket.append(value_text)
    return merged


def _base64_decode_attempt(value: str) -> Optional[str]:
    text = str(value or "").strip()
    if len(text) < 8:
        return None
    try:
        raw = base64.b64decode(text, validate=False)
        decoded = raw.decode("utf-8", errors="ignore")
        return decoded or None
    except Exception:
        return None


def _filter_comscore_params(values: Dict[str, List[str]]) -> Dict[str, List[str]]:
    filtered: Dict[str, List[str]] = {}
    for key, raw_values in (values or {}).items():
        key_text = str(key or "").strip().lower()
        if key_text not in COMSCORE_PARAM_KEYS:
            continue
        kept = [str(item) for item in raw_values if str(item) != ""]
        if kept:
            filtered[key_text] = kept
    return filtered


def _extract_comscore_params_from_text(value: str) -> Dict[str, List[str]]:
    text = str(value or "")
    if not text:
        return {}

    try:
        parsed = parse_qs(unquote_plus(text), keep_blank_values=True)
        filtered = _filter_comscore_params(parsed)
        if filtered:
            return filtered
    except Exception:
        pass

    matches: Dict[str, List[str]] = {}
    for match in COMSCORE_GENERIC_PARAM_RE.finditer(text):
        key = match.group(1).lower()
        val = unquote_plus(match.group(2))
        matches.setdefault(key, [])
        if val not in matches[key]:
            matches[key].append(val)
    if matches:
        return matches

    decoded = _base64_decode_attempt(text)
    if decoded and decoded != text:
        return _extract_comscore_params_from_text(decoded)

    return {}


def _extract_comscore_params_from_js(value: str) -> Dict[str, List[str]]:
    text = str(value or "")
    if not text:
        return {}

    params = _extract_comscore_params_from_text(text)

    c1_match = COMSCORE_JS_C1_RE.search(text)
    if c1_match:
        c1_value = next((group for group in c1_match.groups() if group), "")
        if c1_value:
            params = _merge_multivalue_dicts(params, {"c1": [c1_value]})

    c2_match = COMSCORE_JS_C2_RE.search(text)
    if c2_match:
        c2_value = next((group for group in c2_match.groups() if group), "")
        if c2_value:
            params = _merge_multivalue_dicts(params, {"c2": [c2_value]})

    return params


def _build_comscore_capture_row(hit: Dict[str, Any]) -> Dict[str, Any]:
    url = str(hit.get("url") or hit.get("request_url") or "")
    combined: Dict[str, List[str]] = {}

    try:
        query_params = _filter_comscore_params(parse_qs(urlparse(url).query, keep_blank_values=True))
        combined = _merge_multivalue_dicts(combined, query_params)
    except Exception:
        pass

    combined = _merge_multivalue_dicts(
        combined,
        _extract_comscore_params_from_text(hit.get("request_body") or ""),
    )

    for headers_field in ("request_headers", "response_headers", "headers"):
        headers = hit.get(headers_field) or {}
        if not isinstance(headers, dict):
            continue
        for header_value in headers.values():
            combined = _merge_multivalue_dicts(
                combined,
                _extract_comscore_params_from_text(header_value),
            )

    response_headers = hit.get("response_headers") or hit.get("headers") or {}
    if isinstance(response_headers, dict):
        location_value = _case_insensitive_get(response_headers, "Location")
        combined = _merge_multivalue_dicts(
            combined,
            _extract_comscore_params_from_text(location_value or ""),
        )

    if COMSCORE_JS_PATTERN.search(url):
        combined = _merge_multivalue_dicts(
            combined,
            _extract_comscore_params_from_js(hit.get("response_body") or ""),
        )

    hit_type = "Beacon JS" if COMSCORE_JS_PATTERN.search(url) else "Beacon Request"

    return {
        "hit_type": hit_type,
        "source": hit.get("source") or "",
        "status": hit.get("status") or hit.get("response_status") or "",
        "request_url": url,
        "c1": format_exact_value(combined.get("c1") or []),
        "c2": format_exact_value(combined.get("c2") or []),
        "c7": format_exact_value(combined.get("c7") or []),
        "c8": format_exact_value(combined.get("c8") or []),
    }


def _has_comscore_values(row: Dict[str, Any]) -> bool:
    return any(str(row.get(key) or "").strip() for key in COMSCORE_PARAM_KEYS)


def build_comscore_capture_rows(hits: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    grouped_rows: Dict[Tuple[str, str, str, str, str], Dict[str, Any]] = {}

    for hit in hits or []:
        if not isinstance(hit, dict):
            continue
        row = _build_comscore_capture_row(hit)
        if not _has_comscore_values(row):
            continue

        key = (
            row["hit_type"],
            row["c1"],
            row["c2"],
            row["c7"],
            row["c8"],
        )
        grouped = grouped_rows.setdefault(
            key,
            {
                "hit_type": row["hit_type"],
                "times_fired": 0,
                "status_chain": [],
                "c1": row["c1"],
                "c2": row["c2"],
                "c7": row["c7"],
                "c8": row["c8"],
                "request_url": row["request_url"],
            },
        )
        grouped["times_fired"] += 1
        status_text = str(row.get("status") or "").strip()
        if status_text and status_text not in grouped["status_chain"]:
            grouped["status_chain"].append(status_text)
        if not grouped.get("request_url") and row.get("request_url"):
            grouped["request_url"] = row["request_url"]

    rows: List[Dict[str, Any]] = []
    for grouped in grouped_rows.values():
        rows.append(
            {
                "hit_type": grouped["hit_type"],
                "times_fired": grouped["times_fired"],
                "status_chain": " -> ".join(grouped["status_chain"]) if grouped["status_chain"] else "",
                "c1": grouped["c1"],
                "c2": grouped["c2"],
                "c7": grouped["c7"],
                "c8": grouped["c8"],
                "request_url": grouped["request_url"],
            }
        )

    rows.sort(key=lambda row: (-int(row.get("times_fired") or 0), row.get("request_url") or ""))
    return rows


def _is_ga4_collect_hit(url: str) -> bool:
    parsed = urlparse(str(url or ""))
    host = parsed.netloc.lower()
    path = parsed.path.lower()
    query = parse_qs(parsed.query, keep_blank_values=True)

    if not path.endswith("/collect"):
        return False

    if "google-analytics.com" in host:
        return True

    if host.endswith("google.com"):
        return bool({"v", "tid", "en"} & set(query.keys()))

    return False


def _is_ccm_pageview_hit(url: str, page_domain: str) -> bool:
    if not CCM_PAGEVIEW_PATTERN.search(url or ""):
        return False
    qs = parse_qs(urlparse(url).query, keep_blank_values=True)
    dl = qs.get("dl", [""])[0]
    return page_domain in dl if page_domain else True


def _build_network_hit(request) -> Dict[str, Any]:
    response = getattr(request, "response", None)
    request_headers = _safe_headers(getattr(request, "headers", {}))
    response_headers = _safe_headers(getattr(response, "headers", {})) if response else {}
    request_body = _truncate_text(_decode_body_bytes(getattr(request, "body", b"")))
    response_body = (
        _truncate_text(_decode_body_bytes(getattr(response, "body", b"")))
        if response
        else ""
    )
    decoded_events = decode_ga4_collect_request(getattr(request, "url", ""), request_body)

    return {
        "source": "seleniumwire",
        "url": getattr(request, "url", ""),
        "method": getattr(request, "method", "GET"),
        "status": getattr(response, "status_code", None),
        "response_status": getattr(response, "status_code", None),
        "content_type": _case_insensitive_get(response_headers, "Content-Type"),
        "headers": response_headers,
        "request_headers": request_headers,
        "response_headers": response_headers,
        "request_body": request_body,
        "response_body": response_body,
        "decoded_events": decoded_events,
    }


def _try_get_response_body_from_cdp(driver, request_id: str) -> str:
    if not request_id:
        return ""
    try:
        body_info = driver.execute_cdp_cmd("Network.getResponseBody", {"requestId": request_id})
    except Exception:
        return ""
    if not isinstance(body_info, dict):
        return ""
    return _truncate_text(str(body_info.get("body") or ""))


def extract_collect_hits_from_performance_logs(
    driver,
    page_domain: str,
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]]]:
    try:
        raw_entries = driver.get_log("performance")
    except Exception:
        return [], []

    requests_by_id: Dict[str, Dict[str, Any]] = {}

    for entry in raw_entries:
        try:
            message = json.loads(entry.get("message", "{}")).get("message", {})
        except Exception:
            continue

        method = message.get("method")
        params = message.get("params", {})
        request_id = str(params.get("requestId") or "")
        if not request_id:
            continue

        item = requests_by_id.setdefault(request_id, {"request_id": request_id, "source": "performance_log"})

        if method == "Network.requestWillBeSent":
            request = params.get("request", {})
            url = str(request.get("url") or item.get("url") or "")
            if not (
                _is_ga4_collect_hit(url)
                or _is_ccm_pageview_hit(url, page_domain)
                or _is_comscore_hit(url)
            ):
                continue
            item["url"] = url
            item["method"] = request.get("method", item.get("method", "GET"))
            item["request_headers"] = _safe_headers(request.get("headers", {})) or item.get("request_headers", {})
            item["request_body"] = _truncate_text(str(request.get("postData") or item.get("request_body") or ""))
            item["timestamp"] = params.get("timestamp")
        elif method == "Network.requestWillBeSentExtraInfo":
            headers = _safe_headers(params.get("headers", {}))
            if headers:
                item["request_headers"] = headers
        elif method == "Network.responseReceived":
            response = params.get("response", {})
            url = str(response.get("url") or item.get("url") or "")
            if not (
                _is_ga4_collect_hit(url)
                or _is_ccm_pageview_hit(url, page_domain)
                or _is_comscore_hit(url)
            ):
                continue
            item["url"] = url
            item["status"] = response.get("status", item.get("status"))
            item["response_status"] = response.get("status", item.get("response_status"))
            item["content_type"] = response.get("mimeType") or item.get("content_type")
            response_headers = _safe_headers(response.get("headers", {}))
            if response_headers:
                item["response_headers"] = response_headers
        elif method == "Network.responseReceivedExtraInfo":
            status_code = params.get("statusCode")
            if status_code is not None:
                item["status"] = status_code
                item["response_status"] = status_code
            response_headers = _safe_headers(params.get("headers", {}))
            if response_headers:
                item["response_headers"] = response_headers

    ga4_collects: List[Dict[str, Any]] = []
    ccm_pageviews: List[Dict[str, Any]] = []
    comscore_hits: List[Dict[str, Any]] = []

    for request_id, item in requests_by_id.items():
        url = str(item.get("url") or "")
        if not url:
            continue
        if not (
            _is_ga4_collect_hit(url)
            or _is_ccm_pageview_hit(url, page_domain)
            or _is_comscore_hit(url)
        ):
            continue

        response_headers = _safe_headers(item.get("response_headers", {}))
        request_body = _truncate_text(str(item.get("request_body") or ""))
        response_body = _try_get_response_body_from_cdp(driver, request_id)
        hit = {
            "source": "performance_log",
            "request_id": request_id,
            "url": url,
            "method": item.get("method", "GET"),
            "status": item.get("status"),
            "response_status": item.get("response_status"),
            "content_type": item.get("content_type") or _case_insensitive_get(response_headers, "Content-Type"),
            "headers": response_headers,
            "request_headers": _safe_headers(item.get("request_headers", {})),
            "response_headers": response_headers,
            "request_body": request_body,
            "response_body": response_body,
            "decoded_events": decode_ga4_collect_request(url, request_body),
        }

        if _is_comscore_hit(url):
            comscore_hits.append(hit)
        elif _is_ccm_pageview_hit(url, page_domain):
            ccm_pageviews.append(hit)
        else:
            ga4_collects.append(hit)

    return ga4_collects, ccm_pageviews, comscore_hits


def _merge_hit_record(base_hit: Dict[str, Any], new_hit: Dict[str, Any]) -> Dict[str, Any]:
    merged = dict(base_hit)
    for field in (
        "source",
        "request_id",
        "status",
        "response_status",
        "content_type",
        "request_body",
        "response_body",
    ):
        if not merged.get(field) and new_hit.get(field):
            merged[field] = new_hit[field]

    for field in ("request_headers", "response_headers", "headers"):
        combined = dict(merged.get(field) or {})
        combined.update(new_hit.get(field) or {})
        if combined:
            merged[field] = combined

    if not merged.get("decoded_events") and new_hit.get("decoded_events"):
        merged["decoded_events"] = new_hit["decoded_events"]

    return merged


def merge_network_hits(*hit_groups: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    merged_hits: Dict[Tuple[str, str, str], Dict[str, Any]] = {}

    for group in hit_groups:
        for hit in group or []:
            if not isinstance(hit, dict):
                continue
            url = str(hit.get("url") or hit.get("request_url") or "")
            method = str(hit.get("method") or "GET")
            request_body = str(hit.get("request_body") or "")
            key = (url, method, request_body)
            if key in merged_hits:
                merged_hits[key] = _merge_hit_record(merged_hits[key], hit)
            else:
                merged_hits[key] = dict(hit)

    return list(merged_hits.values())


def categorize_network_requests(driver, page_domain: str) -> Dict[str, Any]:
    asset_seen = set()
    gtm_scripts: List[Dict[str, Any]] = []
    gtag_scripts: List[Dict[str, Any]] = []
    ga4_collects: List[Dict[str, Any]] = []
    ccm_pageviews: List[Dict[str, Any]] = []
    comscore_hits: List[Dict[str, Any]] = []

    for request in driver.requests:
        url = getattr(request, "url", "")
        if not url:
            continue

        hit = _build_network_hit(request)

        if GTM_SCRIPT_PATTERN.search(url):
            key = (hit["url"], hit["status"])
            if key not in asset_seen:
                asset_seen.add(key)
                gtm_scripts.append(hit)
        elif GTAG_SCRIPT_PATTERN.search(url):
            key = (hit["url"], hit["status"])
            if key not in asset_seen:
                asset_seen.add(key)
                gtag_scripts.append(hit)
        elif _is_ga4_collect_hit(url):
            ga4_collects.append(hit)
        elif _is_ccm_pageview_hit(url, page_domain):
            ccm_pageviews.append(hit)
        elif _is_comscore_hit(url):
            comscore_hits.append(hit)

    perf_ga4_collects, perf_ccm_pageviews, perf_comscore_hits = extract_collect_hits_from_performance_logs(driver, page_domain)
    ga4_collects = merge_network_hits(ga4_collects, perf_ga4_collects)
    ccm_pageviews = merge_network_hits(ccm_pageviews, perf_ccm_pageviews)
    comscore_hits = merge_network_hits(comscore_hits, perf_comscore_hits)

    return {
        "gtm_present": bool(gtm_scripts),
        "gtag_present": bool(gtag_scripts),
        "ga4_collect_present": bool(ga4_collects),
        "ccm_pageview_present": bool(ccm_pageviews),
        "comscore_present": bool(comscore_hits),
        "gtm_scripts": gtm_scripts,
        "gtag_scripts": gtag_scripts,
        "ga4_collects": ga4_collects,
        "ccm_pageviews": ccm_pageviews,
        "comscore_hits": comscore_hits,
    }


def hook_ga4_gtag(driver) -> None:
    install_preload_instrumentation(driver)


# -------------------------
# JSON sanitizer
# -------------------------

def sanitize_for_json(obj: Any) -> Any:
    if isinstance(obj, dict):
        return {k: sanitize_for_json(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [sanitize_for_json(v) for v in obj]
    elif isinstance(obj, WebElement):
        try:
            tag = obj.tag_name
            el_id = obj.get_attribute("id")
            el_class = obj.get_attribute("class")
            meta = " ".join(
                x
                for x in [
                    tag,
                    f"#{el_id}" if el_id else "",
                    f".{el_class}" if el_class else "",
                ]
                if x
            )
            return f"<WebElement {meta.strip()}>"
        except Exception:
            return "<WebElement>"
    else:
        try:
            json.dumps(obj)
            return obj
        except TypeError:
            return str(obj)


# -------------------------
# Scroll helper – stop before Taboola
# -------------------------

def scroll_before_taboola(driver, scroll_pause: float = 1.0, max_steps: int = 20) -> None:
    try:
        info = driver.execute_script(
            """
var elements = document.querySelectorAll('[id*="taboola"],[class*="taboola"]');
var viewportHeight = window.innerHeight || document.documentElement.clientHeight || 800;
var docHeight = Math.max(
    document.body.scrollHeight,
    document.documentElement.scrollHeight,
    document.body.offsetHeight,
    document.documentElement.offsetHeight,
    document.body.clientHeight,
    document.documentElement.clientHeight
);
if (elements.length === 0) {
    return {taboolaY: null, viewportHeight: viewportHeight, docHeight: docHeight};
}
var el = elements[0];
var rect = el.getBoundingClientRect();
var top = rect.top + window.scrollY;
return {taboolaY: top, viewportHeight: viewportHeight, docHeight: docHeight};
"""
        )
    except Exception:
        return

    if not isinstance(info, dict):
        return

    taboola_y = info.get("taboolaY")
    viewport_h = info.get("viewportHeight") or 800
    doc_h = info.get("docHeight") or 0

    if taboola_y is None:
        target = doc_h
    else:
        target = max(int(taboola_y - 0.5 * viewport_h), 0)

    if target <= 0:
        return

    step = max(int(target / max_steps), int(viewport_h * 0.3))
    current = 0

    print(f"  ↕ Scrolling page up to ~{target}px (Taboola-safe)")

    while current < target:
        current = min(current + step, target)
        try:
            driver.execute_script("window.scrollTo(0, arguments[0]);", current)
        except Exception:
            break
        time.sleep(scroll_pause)


# -------------------------
# Consent helper
# -------------------------

def _click_candidate_elements(driver, actions: List[Dict[str, Any]]) -> None:
    for selector in COMMON_CONSENT_SELECTORS:
        try:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
        except Exception:
            continue

        for element in elements[:20]:
            try:
                text = (element.text or "").strip()
                aria_label = (element.get_attribute("aria-label") or "").strip()
                label = " ".join(part for part in [text, aria_label] if part).strip()
                if label and not CONSENT_BUTTON_TEXT_PATTERN.search(label):
                    continue
                if not label and selector in {"button", "[role='button']", "a"}:
                    continue
                if not element.is_displayed():
                    continue
                driver.execute_script("arguments[0].click();", element)
                actions.append(
                    {
                        "selector": selector,
                        "label": label or "(matched by selector)",
                    }
                )
                time.sleep(0.4)
                return
            except Exception:
                continue


def accept_common_consent(driver) -> List[Dict[str, Any]]:
    actions: List[Dict[str, Any]] = []

    try:
        driver.switch_to.default_content()
        _click_candidate_elements(driver, actions)
        if actions:
            return actions
    except Exception:
        return actions

    try:
        frames = driver.find_elements(By.TAG_NAME, "iframe")
    except Exception:
        return actions

    for index, frame in enumerate(frames[:10]):
        try:
            driver.switch_to.default_content()
            driver.switch_to.frame(frame)
            before_count = len(actions)
            _click_candidate_elements(driver, actions)
            if len(actions) > before_count:
                actions[-1]["frame_index"] = index
                driver.switch_to.default_content()
                return actions
        except Exception:
            continue
        finally:
            try:
                driver.switch_to.default_content()
            except Exception:
                pass

    return actions


# -------------------------
# Flattening & scorecard
# -------------------------

def extract_flat_pageview_fields(pageview_event: Optional[dict]) -> Dict[str, Any]:
    pv = pageview_event or {}

    flat: Dict[str, Any] = {
        "pv_event_name": pv.get("event"),
        "pv_page_location": pv.get("page_location") or pv.get("page_location_url"),
        "pv_page_referrer": pv.get("page_referrer") or pv.get("page_referrer_url"),
        "pv_page_title": pv.get("page_title"),
        "pv_language": pv.get("language") or pv.get("page_language"),
        "pv_content_type": pv.get("content_type") or pv.get("page_category"),
        "pv_tvc_page_type": pv.get("tvc_page_type"),
        "pv_page_type": pv.get("page_type"),
        "pv_pagetype": pv.get("pagetype"),
    }

    flat["page_template"] = (
        flat["pv_tvc_page_type"]
        or flat["pv_page_type"]
        or flat["pv_pagetype"]
        or ""
    )
    return flat


def compute_implementation_score(
    base_result: Dict[str, Any], pageview_event: Optional[dict]
) -> Tuple[str, str]:
    issues: List[str] = []

    datalayer_found = bool(base_result.get("datalayer_found"))
    has_pv = bool(base_result.get("pageview_event_found"))
    ga4_or_ccm = bool(
        base_result.get("ga4_execution_present")
        or base_result.get("ga4_collect_present")
        or base_result.get("ccm_pageview_present")
    )

    if not datalayer_found and not ga4_or_ccm:
        issues.append("No dataLayer and no GA4/CCM hit observed")
        status = "FAIL"
        return status, " | ".join(issues)

    if datalayer_found and not has_pv:
        issues.append("dataLayer present but no page_view/pageview event found")
        status = "WARN"
        return status, " | ".join(issues)

    if not datalayer_found and ga4_or_ccm:
        issues.append("GA4/CCM hit observed but dataLayer not accessible")
        status = "WARN"
        return status, " | ".join(issues)

    status = "PASS"

    if not base_result.get("gtm_present") and not base_result.get("gtag_present"):
        issues.append("No GTM/gtag script detected (check implementation pattern)")
    elif not base_result.get("ga4_execution_present") and not base_result.get("ga4_collect_present"):
        issues.append("Tag library found but no GA4 send observed during audit window")

    return status, " | ".join(issues)


def _format_hits_sample(hits: List[Dict[str, Any]]) -> str:
    if not hits:
        return ""
    lines: List[str] = []
    for h in hits[:5]:
        status = h.get("status")
        url = h.get("url")
        ctype = h.get("content_type")
        line1 = f"[{status}] {url}"
        lines.append(line1)
        if ctype:
            lines.append(f"    content_type: {ctype}")
    return "\n".join(lines)


# -------------------------
# Core auditor
# -------------------------

def audit_single_url(driver, url: str, wait_seconds: int = 8) -> Dict[str, Any]:
    print(f"\n🔍 Auditing: {url}")

    audit_start = time.time()

    result: Dict[str, Any] = {
        "page_url": url,
        "page_title": "",
        "http_status_hint": "",
        "preload_hook_installed": False,
        "preload_hook_error": "",
        "consent_clicked": False,
        "consent_clicks_json": "",
        "datalayer_found": False,
        "datalayer_length": 0,
        "datalayer_error": "",
        "pageview_event_found": False,
        "pageview_event_json": "",
        "all_datalayer_json": "",
        "gtm_present": False,
        "gtag_present": False,
        "ga4_collect_present": False,
        "ccm_pageview_present": False,
        "comscore_present": False,
        "gtm_scripts_sample": "",
        "gtag_scripts_sample": "",
        "ga4_collects_sample": "",
        "ccm_pageviews_sample": "",
        "comscore_hits_sample": "",
        "pv_event_name": "",
        "pv_page_location": "",
        "pv_page_referrer": "",
        "pv_page_title": "",
        "pv_language": "",
        "pv_content_type": "",
        "pv_tvc_page_type": "",
        "pv_page_type": "",
        "pv_pagetype": "",
        "page_template": "",
        "status": "",
        "issues": "",
        "scroll_event_found": False,
        "scroll_event_json": "",
        "ga4_execution_present": False,
        "ga4_gtag_calls_json": "",
        "ga4_events_json": "",
        "ga4_execution_hits_json": "",
        "ga4_execution_events_json": "",
        "ga4_network_hits_json": "",
        "ga4_network_events_json": "",
        "ga4_decoded_events_json": "",
        "comscore_hits_json": "",
        "mapping_table": "",
        "audit_duration_seconds": 0.0,
    }

    # HTTP hint
    try:
        resp = requests.get(url, timeout=8)
        result["http_status_hint"] = resp.status_code
    except Exception as e:
        result["http_status_hint"] = f"Error: {e}"

    # Clear selenium-wire history
    try:
        del driver.requests
    except Exception:
        pass
    try:
        driver.get_log("performance")
    except Exception:
        pass

    preload_ok, preload_error = install_preload_instrumentation(driver)
    result["preload_hook_installed"] = preload_ok
    result["preload_hook_error"] = preload_error

    # Load page
    try:
        driver.get(url)
    except Exception as e:
        result["datalayer_error"] = f"Error loading page in Selenium: {e}"
        result["audit_duration_seconds"] = round(time.time() - audit_start, 2)
        return result

    consent_actions = accept_common_consent(driver)
    result["consent_clicked"] = bool(consent_actions)
    result["consent_clicks_json"] = safe_json(consent_actions)

    # Try to force consent granted (so GA4 is allowed to fire)
    try:
        driver.execute_script("""
            try {
                if (typeof gtag === "function") {
                    gtag('consent', 'update', {
                        ad_user_data: 'granted',
                        ad_personalization: 'granted',
                        ad_storage: 'granted',
                        analytics_storage: 'granted'
                    });
                }
            } catch (e) {}
        """)
    except Exception:
        pass

    # Scroll the page (Taboola-safe) then extra scrolls to trigger scroll-depth
    scroll_before_taboola(driver)
    try:
        for p in range(0, 71, 10):
            driver.execute_script(
                "window.scrollTo(0, document.body.scrollHeight * arguments[0] / 100);",
                p,
            )
            time.sleep(0.6)
    except Exception:
        pass

    # Wait a bit more for GA4/dataLayer to finish firing
    time.sleep(wait_seconds)

    # Title
    try:
        result["page_title"] = driver.title
    except Exception:
        result["page_title"] = ""

    # DataLayer
    dl_list, dl_error = extract_datalayer(driver)
    if dl_error:
        result["datalayer_error"] = dl_error

    result["datalayer_found"] = len(dl_list) > 0
    result["datalayer_length"] = len(dl_list)

    pageview_event = find_pageview_event(dl_list)
    result["pageview_event_found"] = pageview_event is not None

    if pageview_event is not None:
        try:
            safe_pageview = sanitize_for_json(pageview_event)
            result["pageview_event_json"] = json.dumps(
                safe_pageview, ensure_ascii=False, indent=2, sort_keys=True
            )
        except Exception as e:
            result["pageview_event_json"] = f"Error serializing pageview event: {e}"

    # Full dataLayer JSON
    try:
        safe_dl_list = sanitize_for_json(dl_list)
        result["all_datalayer_json"] = json.dumps(
            safe_dl_list, ensure_ascii=False, indent=2, sort_keys=True
        )
    except Exception as e:
        result["all_datalayer_json"] = f"Error serializing dataLayer: {e}"

    # Scroll-related events
    scroll_events = find_events_by_name(dl_list, ["scroll", "scroll_event", "scrolldepth"])
    if scroll_events:
        result["scroll_event_found"] = True
        try:
            safe_scroll = sanitize_for_json(scroll_events[-1])
            result["scroll_event_json"] = json.dumps(
                safe_scroll, ensure_ascii=False, indent=2, sort_keys=True
            )
        except Exception as e:
            result["scroll_event_json"] = f"Error serializing scroll event: {e}"

    # Network hits
    page_domain = urlparse(url).netloc
    net_info = categorize_network_requests(driver, page_domain)

    result["gtm_present"] = net_info["gtm_present"]
    result["gtag_present"] = net_info["gtag_present"]
    result["ga4_collect_present"] = net_info["ga4_collect_present"]
    result["ccm_pageview_present"] = net_info["ccm_pageview_present"]
    result["comscore_present"] = net_info["comscore_present"]

    result["gtm_scripts_sample"] = _format_hits_sample(net_info["gtm_scripts"])
    result["gtag_scripts_sample"] = _format_hits_sample(net_info["gtag_scripts"])
    result["ga4_collects_sample"] = _format_hits_sample(net_info["ga4_collects"])
    result["ccm_pageviews_sample"] = _format_hits_sample(net_info["ccm_pageviews"])
    result["comscore_hits_sample"] = _format_hits_sample(net_info["comscore_hits"])

    preload_state = extract_preload_state(driver)
    gtag_calls = preload_state.get("gtagCalls", []) or []
    gtag_events = normalize_gtag_calls(gtag_calls)
    result["ga4_gtag_calls_json"] = safe_json(gtag_calls)
    result["ga4_events_json"] = safe_json(gtag_events)

    execution_hits, execution_events = normalize_transport_hits(preload_state)
    result["ga4_execution_present"] = bool(execution_hits or execution_events)
    result["ga4_execution_hits_json"] = safe_json(execution_hits)
    result["ga4_execution_events_json"] = safe_json(execution_events)

    # GA4 events decoded from actual network requests
    decoded_events: List[dict] = []
    network_hits = [*net_info["ga4_collects"], *net_info["ccm_pageviews"]]
    for hit in network_hits:
        for decoded_event in hit.get("decoded_events", []) or []:
            if isinstance(decoded_event, dict):
                decoded_events.append(decoded_event)

    result["ga4_network_hits_json"] = safe_json(network_hits)
    result["ga4_network_events_json"] = safe_json(decoded_events)
    result["ga4_decoded_events_json"] = safe_json(decoded_events)
    result["comscore_hits_json"] = safe_json(
        build_comscore_capture_rows(net_info["comscore_hits"])
    )

    # Flatten page_view
    flat_pv = extract_flat_pageview_fields(pageview_event)
    result.update(flat_pv)

    execution_for_mapping = execution_events or gtag_events
    result["mapping_table"] = safe_json(
        map_dl_to_execution_and_ga4(
            result.get("pageview_event_json") or "{}",
            execution_for_mapping,
            decoded_events,
        )
    )

    # Scorecard
    status, issues = compute_implementation_score(result, pageview_event)
    if result["preload_hook_error"]:
        issues = f"{issues} | Early instrumentation unavailable" if issues else "Early instrumentation unavailable"
    result["status"] = status
    result["issues"] = issues

    result["audit_duration_seconds"] = round(time.time() - audit_start, 2)

    print(
        f"  ▶ dataLayer: {result['datalayer_length']} entries, "
        f"page_view/pageview event: {result['pageview_event_found']}, "
        f"execution-stage hits: {result['ga4_execution_present']}, "
        f"GA4 collect: {result['ga4_collect_present']}, "
        f"status: {result['status']}"
    )
    return result

# Streamlit app

st.set_page_config(page_title="GA4 / dataLayer Auditor", layout="wide")
st.title("GA4 / dataLayer Auditor")
st.markdown(
    """
<style>
div[data-testid="stDataFrame"] div[role="columnheader"],
div[data-testid="stDataFrame"] div[role="gridcell"] {
    font-size: 0.82rem !important;
    line-height: 1.2 !important;
}
</style>
""",
    unsafe_allow_html=True,
)

JAGRAN_EMAIL_DOMAIN = "@jagrannewmedia.com"
TEMPLATE_ADMIN_EMAIL = f"kartikay.khosla{JAGRAN_EMAIL_DOMAIN}"
DEFAULT_LOG_SHEET_ID = "1e_fp0fAOeEAHaRtFJUv-rt-i0sqUOhszYOrOk7Cv5QU"
DEFAULT_LOG_WORKSHEET = "Audit Logs"
DEFAULT_TEMPLATE_WORKSHEET = "Audit Templates"
DEFAULT_TEMPLATE_RULES_WORKSHEET = "Audit Template Rules"
FIXED_LOG_HEADERS = [
    "date",
    "email_id",
    "url_checked",
    "pageview_trigger_found",
]
LEGACY_EXECUTION_SUMMARY_HEADER = "execution_custom_dimensions"
LOG_HEADERS = [
    *FIXED_LOG_HEADERS,
    LEGACY_EXECUTION_SUMMARY_HEADER,
]
LOG_TIMEZONE = ZoneInfo("Asia/Kolkata")
LOGIN_COOKIE_NAME = "ga_audit_login_email"
LOGIN_COOKIE_DAYS = 30
TEMPLATE_HEADERS = [
    "template_id",
    "template_name",
    "domain_name",
    "measurement_id",
    "container_id",
    "url_pattern",
    "active",
    "created_by",
    "created_at",
]
TEMPLATE_RULE_HEADERS = [
    "rule_id",
    "template_id",
    "rule_scope",
    "field_name",
    "rule_type",
    "expected_values",
    "notes",
    "created_by",
    "created_at",
]
RULE_SCOPE_OPTIONS = {
    "Execution field": "execution",
    "Event": "event",
}
RULE_TYPE_OPTIONS = ["exact", "one_of", "contains", "regex", "required", "optional"]
VALIDATION_PASS_LABEL = "Matched"
VALIDATION_FAIL_LABEL = "Mismatch"
VALIDATION_OPTIONAL_LABEL = "Optional"


def get_cookie_manager():
    if not stx:
        return None
    cookie_manager = st.session_state.get("_ga_audit_cookie_manager")
    if cookie_manager is None:
        cookie_manager = stx.CookieManager()
        st.session_state["_ga_audit_cookie_manager"] = cookie_manager
    return cookie_manager


def read_login_cookie():
    cookie_manager = get_cookie_manager()
    if not cookie_manager:
        return ""
    try:
        value = cookie_manager.get(LOGIN_COOKIE_NAME)
    except Exception:
        return ""
    return str(value or "").strip().lower()


def write_login_cookie(email: str):
    cookie_manager = get_cookie_manager()
    if not cookie_manager:
        return
    expires_at = datetime.now(timezone.utc) + timedelta(days=LOGIN_COOKIE_DAYS)
    try:
        cookie_manager.set(
            LOGIN_COOKIE_NAME,
            email,
            expires_at=expires_at,
            key=f"{LOGIN_COOKIE_NAME}_set",
        )
    except Exception:
        pass


def clear_login_cookie():
    cookie_manager = get_cookie_manager()
    if not cookie_manager:
        return
    try:
        cookie_manager.delete(LOGIN_COOKIE_NAME, key=f"{LOGIN_COOKIE_NAME}_delete")
    except Exception:
        pass


def build_login_email(username: str):
    value = str(username or "").strip().lower()
    if not value:
        return "", "Please enter your username."
    if "@" in value:
        return "", "Enter only your username, not the full email."
    if not re.fullmatch(r"[a-z0-9._-]+", value):
        return "", "Username can only contain letters, numbers, dot, underscore, or hyphen."
    return f"{value}{JAGRAN_EMAIL_DOMAIN}", ""


def require_login():
    logged_in_email = st.session_state.get("logged_in_email")
    if logged_in_email:
        return logged_in_email

    cookie_email = read_login_cookie()
    if cookie_email.endswith(JAGRAN_EMAIL_DOMAIN):
        st.session_state["logged_in_email"] = cookie_email
        return cookie_email

    st.subheader("Login")
    st.info(f"Use your Jagran username. The app will identify you as `username{JAGRAN_EMAIL_DOMAIN}`.")
    with st.form("login_form", clear_on_submit=False):
        username = st.text_input("Username")
        submitted = st.form_submit_button("Continue")
    if submitted:
        email, error = build_login_email(username)
        if error:
            st.error(error)
        else:
            st.session_state["logged_in_email"] = email
            write_login_cookie(email)
            st.rerun()
    st.stop()


def get_service_account_info():
    try:
        raw = st.secrets.get("gcp_service_account", {})
    except Exception:
        return {}
    info = dict(raw) if raw else {}
    cleaned = {}
    for key, value in info.items():
        if isinstance(value, str):
            cleaned[key] = value.strip()
        else:
            cleaned[key] = value

    private_key = cleaned.get("private_key")
    if isinstance(private_key, str):
        normalized_key = private_key
        if len(normalized_key) >= 2 and normalized_key[0] == normalized_key[-1] and normalized_key[0] in {"'", '"'}:
            normalized_key = normalized_key[1:-1]
        normalized_key = normalized_key.replace("\\n", "\n").replace("\r\n", "\n").replace("\r", "\n").strip()
        begin_marker = "-----BEGIN PRIVATE KEY-----"
        if begin_marker in normalized_key:
            normalized_key = normalized_key[normalized_key.index(begin_marker):]
        cleaned["private_key"] = normalized_key

    return cleaned


def get_sheet_settings():
    try:
        raw = st.secrets.get("sheets", {})
    except Exception:
        raw = {}
    settings = dict(raw) if raw else {}
    return {
        "spreadsheet_id": settings.get("spreadsheet_id") or DEFAULT_LOG_SHEET_ID,
        "worksheet_name": settings.get("worksheet_name") or DEFAULT_LOG_WORKSHEET,
    }


def get_template_sheet_settings():
    try:
        raw = st.secrets.get("sheets", {})
    except Exception:
        raw = {}
    settings = dict(raw) if raw else {}
    return {
        "spreadsheet_id": settings.get("spreadsheet_id") or DEFAULT_LOG_SHEET_ID,
        "template_worksheet_name": settings.get("template_worksheet_name") or DEFAULT_TEMPLATE_WORKSHEET,
        "template_rules_worksheet_name": settings.get("template_rules_worksheet_name") or DEFAULT_TEMPLATE_RULES_WORKSHEET,
    }


def is_template_admin(email_id: str) -> bool:
    return str(email_id or "").strip().lower() == TEMPLATE_ADMIN_EMAIL


def sheet_column_label(index: int) -> str:
    label = ""
    while index > 0:
        index, remainder = divmod(index - 1, 26)
        label = chr(65 + remainder) + label
    return label


def ensure_fixed_headers(worksheet, headers):
    existing_headers = worksheet.row_values(1)
    target_headers = list(headers)

    if len(target_headers) > worksheet.col_count:
        worksheet.add_cols(len(target_headers) - worksheet.col_count)

    if existing_headers[: len(target_headers)] != target_headers:
        last_cell = f"{sheet_column_label(len(target_headers))}1"
        worksheet.update(
            range_name=f"A1:{last_cell}",
            values=[target_headers],
            value_input_option="USER_ENTERED",
        )

    return target_headers


def ensure_log_headers(worksheet, dimension_headers):
    existing_headers = worksheet.row_values(1)
    if not any(existing_headers):
        target_headers = list(LOG_HEADERS)
    else:
        target_headers = list(existing_headers)
        for header in LOG_HEADERS:
            if header not in target_headers:
                target_headers.append(header)

    for header in sorted({str(value or "").strip() for value in dimension_headers if str(value or "").strip()}, key=str.lower):
        if header not in target_headers:
            target_headers.append(header)

    if len(target_headers) > worksheet.col_count:
        worksheet.add_cols(len(target_headers) - worksheet.col_count)

    if target_headers != existing_headers:
        last_cell = f"{sheet_column_label(len(target_headers))}1"
        worksheet.update(
            range_name=f"A1:{last_cell}",
            values=[target_headers],
            value_input_option="USER_ENTERED",
        )

    return target_headers


def format_log_worksheet(worksheet, headers):
    requests = [
        {
            "updateSheetProperties": {
                "properties": {
                    "sheetId": worksheet.id,
                    "gridProperties": {"frozenRowCount": 1},
                },
                "fields": "gridProperties.frozenRowCount",
            }
        },
        {
            "repeatCell": {
                "range": {
                    "sheetId": worksheet.id,
                    "startRowIndex": 0,
                    "endRowIndex": 1,
                },
                "cell": {
                    "userEnteredFormat": {
                        "textFormat": {"bold": True},
                        "wrapStrategy": "WRAP",
                    }
                },
                "fields": "userEnteredFormat.textFormat.bold,userEnteredFormat.wrapStrategy",
            }
        },
        {
            "repeatCell": {
                "range": {
                    "sheetId": worksheet.id,
                    "startColumnIndex": 0,
                    "endColumnIndex": len(headers),
                },
                "cell": {"userEnteredFormat": {"wrapStrategy": "WRAP"}},
                "fields": "userEnteredFormat.wrapStrategy",
            }
        },
    ]

    for index, header in enumerate(headers):
        if header == "date":
            width = 170
            hidden = False
        elif header == "email_id":
            width = 250
            hidden = False
        elif header == "url_checked":
            width = 420
            hidden = False
        elif header == "pageview_trigger_found":
            width = 170
            hidden = False
        elif header == LEGACY_EXECUTION_SUMMARY_HEADER:
            width = 320
            hidden = True
        else:
            width = 220
            hidden = False
        requests.append(
            {
                "updateDimensionProperties": {
                    "range": {
                        "sheetId": worksheet.id,
                        "dimension": "COLUMNS",
                        "startIndex": index,
                        "endIndex": index + 1,
                    },
                    "properties": {"pixelSize": width, "hiddenByUser": hidden},
                    "fields": "pixelSize,hiddenByUser",
                }
            }
        )

    worksheet.spreadsheet.batch_update({"requests": requests})


def build_execution_dimension_map(audit_summary: dict):
    execution_dimensions = {}
    for row in audit_summary.get("mapping_rows", []):
        value = row.get("execution_value")
        dimension = str(row.get("dimension") or "").strip()
        if not dimension or value in ("", None):
            continue
        execution_dimensions[dimension] = str(value)
    return execution_dimensions


@st.cache_resource
def get_spreadsheet(service_account_json: str, spreadsheet_id: str):
    if not gspread or not Credentials:
        raise RuntimeError("Google Sheets libraries are not installed.")

    service_account_info = json.loads(service_account_json)
    private_key = str(service_account_info.get("private_key") or "")
    if "-----BEGIN PRIVATE KEY-----" not in private_key or "-----END PRIVATE KEY-----" not in private_key:
        raise RuntimeError(
            "Service account private_key in Streamlit secrets is malformed. "
            "Paste the full private_key from the JSON, including the BEGIN/END lines."
        )

    scopes = [
        "https://www.googleapis.com/auth/spreadsheets",
        "https://www.googleapis.com/auth/drive",
    ]
    credentials = Credentials.from_service_account_info(
        service_account_info,
        scopes=scopes,
    )
    client = gspread.authorize(credentials)
    return client.open_by_key(spreadsheet_id)


@st.cache_resource
def get_log_worksheet(service_account_json: str, spreadsheet_id: str, worksheet_name: str):
    spreadsheet = get_spreadsheet(service_account_json, spreadsheet_id)
    try:
        worksheet = spreadsheet.worksheet(worksheet_name)
    except gspread.WorksheetNotFound:
        worksheet = spreadsheet.add_worksheet(title=worksheet_name, rows=1000, cols=len(LOG_HEADERS))

    headers = ensure_log_headers(worksheet, [])
    format_log_worksheet(worksheet, headers)

    return worksheet


@st.cache_resource
def get_template_worksheets(
    service_account_json: str,
    spreadsheet_id: str,
    template_worksheet_name: str,
    template_rules_worksheet_name: str,
):
    spreadsheet = get_spreadsheet(service_account_json, spreadsheet_id)

    try:
        template_ws = spreadsheet.worksheet(template_worksheet_name)
    except gspread.WorksheetNotFound:
        template_ws = spreadsheet.add_worksheet(
            title=template_worksheet_name,
            rows=1000,
            cols=len(TEMPLATE_HEADERS),
        )

    try:
        rules_ws = spreadsheet.worksheet(template_rules_worksheet_name)
    except gspread.WorksheetNotFound:
        rules_ws = spreadsheet.add_worksheet(
            title=template_rules_worksheet_name,
            rows=2000,
            cols=len(TEMPLATE_RULE_HEADERS),
        )

    ensure_fixed_headers(template_ws, TEMPLATE_HEADERS)
    ensure_fixed_headers(rules_ws, TEMPLATE_RULE_HEADERS)
    return template_ws, rules_ws


def append_audit_log(email_id: str, result: dict, audit_summary: dict):
    service_account_info = get_service_account_info()
    if not service_account_info:
        return False, "Google Sheets logging is not configured yet."

    settings = get_sheet_settings()
    execution_dimension_map = build_execution_dimension_map(audit_summary)
    execution_dimensions = [
        f"{dimension}={value}"
        for dimension, value in execution_dimension_map.items()
    ]

    worksheet = get_log_worksheet(
        json.dumps(service_account_info),
        settings["spreadsheet_id"],
        settings["worksheet_name"],
    )
    headers = ensure_log_headers(worksheet, execution_dimension_map.keys())
    format_log_worksheet(worksheet, headers)

    row_map = {
        "date": datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S"),
        "email_id": email_id,
        "url_checked": result.get("page_url") or "",
        "pageview_trigger_found": "Yes" if audit_summary.get("pageview_triggered") else "No",
        LEGACY_EXECUTION_SUMMARY_HEADER: "\n".join(execution_dimensions) if execution_dimensions else "None",
    }
    row_map.update(execution_dimension_map)

    ordered_row = [row_map.get(header, "") for header in headers]
    worksheet.append_row(ordered_row, value_input_option="USER_ENTERED")
    return True, ""


def _normalize_template_flag(value) -> bool:
    return str(value or "").strip().lower() not in {"", "false", "0", "no", "inactive"}


def _clean_sheet_record(record: dict, headers: List[str]) -> dict:
    cleaned = {header: "" for header in headers}
    for key, value in (record or {}).items():
        cleaned[str(key)] = "" if value is None else str(value).strip()
    return cleaned


def load_templates_and_rules():
    service_account_info = get_service_account_info()
    if not service_account_info:
        return [], [], "Google Sheets logging is not configured yet."

    settings = get_template_sheet_settings()
    template_ws, rules_ws = get_template_worksheets(
        json.dumps(service_account_info),
        settings["spreadsheet_id"],
        settings["template_worksheet_name"],
        settings["template_rules_worksheet_name"],
    )

    templates = [
        _clean_sheet_record(record, TEMPLATE_HEADERS)
        for record in template_ws.get_all_records(default_blank="")
    ]
    rules = [
        _clean_sheet_record(record, TEMPLATE_RULE_HEADERS)
        for record in rules_ws.get_all_records(default_blank="")
    ]

    for template in templates:
        template["active"] = _normalize_template_flag(template.get("active"))

    active_template_ids = {
        str(template.get("template_id") or "").strip()
        for template in templates
        if template.get("active")
    }
    rules = [
        rule
        for rule in rules
        if str(rule.get("template_id") or "").strip() in active_template_ids
    ]
    return templates, rules, ""


def build_template_option_label(template: dict) -> str:
    parts = [str(template.get("template_name") or "").strip() or "Unnamed template"]
    domain_name = str(template.get("domain_name") or "").strip()
    measurement_id = str(template.get("measurement_id") or "").strip()
    container_id = str(template.get("container_id") or "").strip()

    meta = []
    if domain_name:
        meta.append(domain_name)
    if measurement_id:
        meta.append(measurement_id)
    if container_id:
        meta.append(container_id)

    if meta:
        parts.append(f"({' | '.join(meta)})")
    return " ".join(parts)


def append_template_record(email_id: str, template_payload: dict):
    service_account_info = get_service_account_info()
    if not service_account_info:
        return False, "Google Sheets logging is not configured yet."

    settings = get_template_sheet_settings()
    template_ws, _ = get_template_worksheets(
        json.dumps(service_account_info),
        settings["spreadsheet_id"],
        settings["template_worksheet_name"],
        settings["template_rules_worksheet_name"],
    )

    row_map = {
        "template_id": f"tpl_{uuid.uuid4().hex[:8]}",
        "template_name": str(template_payload.get("template_name") or "").strip(),
        "domain_name": str(template_payload.get("domain_name") or "").strip(),
        "measurement_id": str(template_payload.get("measurement_id") or "").strip(),
        "container_id": str(template_payload.get("container_id") or "").strip(),
        "url_pattern": str(template_payload.get("url_pattern") or "").strip(),
        "active": "TRUE" if template_payload.get("active", True) else "FALSE",
        "created_by": email_id,
        "created_at": datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S"),
    }

    ordered_row = [row_map.get(header, "") for header in TEMPLATE_HEADERS]
    template_ws.append_row(ordered_row, value_input_option="USER_ENTERED")
    return True, row_map["template_id"]


def append_template_rule(email_id: str, rule_payload: dict):
    service_account_info = get_service_account_info()
    if not service_account_info:
        return False, "Google Sheets logging is not configured yet."

    settings = get_template_sheet_settings()
    _, rules_ws = get_template_worksheets(
        json.dumps(service_account_info),
        settings["spreadsheet_id"],
        settings["template_worksheet_name"],
        settings["template_rules_worksheet_name"],
    )

    row_map = {
        "rule_id": f"rule_{uuid.uuid4().hex[:8]}",
        "template_id": str(rule_payload.get("template_id") or "").strip(),
        "rule_scope": str(rule_payload.get("rule_scope") or "").strip(),
        "field_name": str(rule_payload.get("field_name") or "").strip(),
        "rule_type": str(rule_payload.get("rule_type") or "").strip(),
        "expected_values": str(rule_payload.get("expected_values") or "").strip(),
        "notes": str(rule_payload.get("notes") or "").strip(),
        "created_by": email_id,
        "created_at": datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S"),
    }

    ordered_row = [row_map.get(header, "") for header in TEMPLATE_RULE_HEADERS]
    rules_ws.append_row(ordered_row, value_input_option="USER_ENTERED")
    return True, row_map["rule_id"]


def append_template_rules(email_id: str, rule_payloads: List[dict]):
    service_account_info = get_service_account_info()
    if not service_account_info:
        return False, "Google Sheets logging is not configured yet."

    payloads = [payload for payload in (rule_payloads or []) if isinstance(payload, dict)]
    if not payloads:
        return False, "No rules to save."

    settings = get_template_sheet_settings()
    _, rules_ws = get_template_worksheets(
        json.dumps(service_account_info),
        settings["spreadsheet_id"],
        settings["template_worksheet_name"],
        settings["template_rules_worksheet_name"],
    )

    rows = []
    timestamp = datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S")
    for payload in payloads:
        row_map = {
            "rule_id": f"rule_{uuid.uuid4().hex[:8]}",
            "template_id": str(payload.get("template_id") or "").strip(),
            "rule_scope": str(payload.get("rule_scope") or "").strip(),
            "field_name": str(payload.get("field_name") or "").strip(),
            "rule_type": str(payload.get("rule_type") or "").strip(),
            "expected_values": str(payload.get("expected_values") or "").strip(),
            "notes": str(payload.get("notes") or "").strip(),
            "created_by": email_id,
            "created_at": timestamp,
        }
        rows.append([row_map.get(header, "") for header in TEMPLATE_RULE_HEADERS])

    rules_ws.append_rows(rows, value_input_option="USER_ENTERED")
    return True, str(len(rows))


def render_sidebar_session(email_id: str):
    with st.sidebar:
        st.markdown("### Session")
        st.write(email_id)
        if st.button("Log out"):
            st.session_state.pop("logged_in_email", None)
            clear_login_cookie()
            st.rerun()

        st.markdown("### Log Sheet")
        service_account_info = get_service_account_info()
        if service_account_info:
            st.success("Google Sheets logging configured")
        else:
            st.warning("Google Sheets logging not configured")
            st.caption("Add `gcp_service_account` to Streamlit secrets to enable logging.")


logged_in_email = require_login()
render_sidebar_session(logged_in_email)

template_records, template_rules, template_load_error = load_templates_and_rules()
active_templates = [
    template
    for template in template_records
    if template.get("active")
]

tab_labels = ["Audit URLs", "Compare Prod vs Stage"]
if is_template_admin(logged_in_email):
    tab_labels.append("Template Manager")

tabs = st.tabs(tab_labels)
tab_main = tabs[0]
tab_compare = tabs[1]
tab_template_manager = tabs[2] if len(tabs) > 2 else None


def load_json_payload(raw_value, fallback):
    if not raw_value:
        return fallback
    try:
        return json.loads(raw_value)
    except Exception:
        return fallback


def render_json_block(title: str, raw_value: str, fallback_label: str):
    st.markdown(f"### {title}")
    if not raw_value:
        st.info(fallback_label)
        return

    try:
        st.json(json.loads(raw_value))
    except Exception:
        st.code(raw_value, language="json")


def render_event_list(title: str, raw_value: str, empty_label: str):
    st.markdown(f"### {title}")
    events = load_json_payload(raw_value, [])
    if not isinstance(events, list) or not events:
        st.info(empty_label)
        return

    for index, event in enumerate(events):
        if isinstance(event, dict):
            event_name = event.get("event_name") or event.get("command") or "(no name)"
        else:
            event_name = "(non-dict entry)"
        with st.expander(f"{index}: {event_name}", expanded=(index == 0)):
            st.json(event)


def render_signal_summary(result: dict):
    st.markdown("### Signal Summary")
    rows = [
        {"signal": "GTM script detected", "value": result.get("gtm_present")},
        {"signal": "gtag script detected", "value": result.get("gtag_present")},
        {"signal": "Consent banner clicked", "value": result.get("consent_clicked")},
        {"signal": "Execution-stage hit captured", "value": result.get("ga4_execution_present")},
        {"signal": "Network GA4 hit captured", "value": result.get("ga4_collect_present")},
    ]
    st.dataframe(pd.DataFrame(rows), use_container_width=True, hide_index=True)


def render_network_hits(raw_value: str, title: str = "### Final collect?v Request / Response"):
    if title:
        st.markdown(title)
    hits = load_json_payload(raw_value, [])
    if not isinstance(hits, list) or not hits:
        st.info("No GA4 request / response hits captured.")
        return

    for index, hit in enumerate(hits):
        if not isinstance(hit, dict):
            continue
        title = f"{index}: {hit.get('method') or 'GET'} {hit.get('url') or hit.get('request_url') or ''}"
        with st.expander(title, expanded=(index == 0)):
            st.write("Source:", hit.get("source") or "n/a")
            st.write("Status:", hit.get("response_status", hit.get("status")))
            st.write("Content-Type:", hit.get("content_type") or "n/a")
            st.markdown("**Request headers**")
            st.json(hit.get("request_headers") or {})
            st.markdown("**Request body**")
            st.code(hit.get("request_body") or "", language="text")
            st.markdown("**Response headers**")
            st.json(hit.get("response_headers") or hit.get("headers") or {})
            st.markdown("**Response body**")
            st.code(hit.get("response_body") or "", language="text")
            decoded = hit.get("decoded_events")
            if decoded:
                st.markdown("**Decoded events**")
                st.json(decoded)


def export_filename(prefix: str, extension: str) -> str:
    timestamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    return f"{prefix}_{timestamp}.{extension}"


def parse_result_json_fields(result: dict):
    json_fields = [
        "all_datalayer_json",
        "pageview_event_json",
        "scroll_event_json",
        "ga4_execution_events_json",
        "ga4_execution_hits_json",
        "ga4_gtag_calls_json",
        "ga4_network_events_json",
        "ga4_network_hits_json",
        "ga4_decoded_events_json",
        "comscore_hits_json",
        "consent_clicks_json",
        "mapping_table",
    ]
    parsed = {}
    for field in json_fields:
        parsed[field] = load_json_payload(result.get(field, ""), None)
    return parsed


def build_share_payload(results):
    summary_rows = []
    export_results = []

    for result in results:
        audit_summary = build_audit_focus_summary(result)
        summary = {
            "status": result.get("status"),
            "page_url": result.get("page_url"),
            "page_title": result.get("page_title"),
            "page_template": result.get("page_template"),
            "datalayer_found": result.get("datalayer_found"),
            "pageview_event_found": result.get("pageview_event_found"),
            "pageview_triggered": audit_summary["pageview_triggered"],
            "pageview_source": audit_summary["pageview_source"],
            "events_fired": audit_summary["events_fired"],
            "captured_in_network": audit_summary["captured_network"],
            "captured_in_execution": audit_summary["captured_execution"],
            "trigger_only": audit_summary["trigger_only"],
            "ga4_execution_present": result.get("ga4_execution_present"),
            "ga4_collect_present": result.get("ga4_collect_present"),
            "comscore_present": result.get("comscore_present"),
            "comscore_values": audit_summary["comscore_preview"],
            "issues": result.get("issues"),
        }
        summary_rows.append(summary)
        export_results.append(
            {
                "page_url": result.get("page_url"),
                "summary": summary,
                "audit_mapping": audit_summary["mapping_rows"],
                "raw_result": result,
                "parsed_debug": parse_result_json_fields(result),
            }
        )

    return {
        "generated_at_utc": datetime.now(timezone.utc).isoformat(),
        "result_count": len(results),
        "summary": summary_rows,
        "results": export_results,
    }


def normalize_event_name(value) -> str:
    return str(value or "").strip().lower().replace("_", "")


def normalize_dimension_name(value) -> str:
    name = str(value or "").strip()
    for prefix in ("tvc_", "user.", "ep.", "epn.", "epf.", "up.", "upn."):
        if name.startswith(prefix):
            name = name[len(prefix):]
            break
    return name.replace("_", "").lower()


def stringify_value(value):
    if isinstance(value, (dict, list)):
        return json.dumps(value, ensure_ascii=False)
    if value is None:
        return ""
    return str(value)


def payload_rows(payload):
    if not isinstance(payload, dict) or not payload:
        return pd.DataFrame(columns=["key", "value"])
    rows = [{"key": key, "value": stringify_value(value)} for key, value in payload.items()]
    return pd.DataFrame(rows)


def build_datalayer_summary_rows(data_layer):
    rows = []
    for index, item in enumerate(data_layer):
        if not isinstance(item, dict):
            rows.append(
                {
                    "index": index,
                    "event": "(non-dict entry)",
                    "details": stringify_value(item),
                }
            )
            continue

        event_name = item.get("event") or "(no event)"
        detail_keys = [key for key in item.keys() if key != "event"]
        details = ", ".join(detail_keys[:4])
        if len(detail_keys) > 4:
            details += "..."
        rows.append(
            {
                "index": index,
                "event": event_name,
                "details": details,
            }
        )
    return pd.DataFrame(rows)


def build_computed_state(data_layer, selected_index: int):
    state = {}
    for item in data_layer[: selected_index + 1]:
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if value is None:
                state.pop(key, None)
            else:
                state[key] = value
    return state


def _matching_score_for_snapshot(candidate_payload: dict, reference_payload: dict):
    candidate_keys = {
        normalize_dimension_name(key)
        for key in (candidate_payload or {}).keys()
        if str(key or "").strip()
    }
    reference_keys = {
        normalize_dimension_name(key)
        for key in (reference_payload or {}).keys()
        if key != "event" and not str(key).startswith("gtm") and str(key or "").strip()
    }
    overlap_count = len(candidate_keys & reference_keys)
    return overlap_count, len(candidate_keys)


def find_matching_datalayer_index(data_layer, selected_event: dict):
    if not isinstance(data_layer, list) or not isinstance(selected_event, dict):
        return None

    target_event = normalize_event_name(selected_event.get("event"))
    best_index = None
    best_score = (-1, -1, -1)

    for index, item in enumerate(data_layer):
        if not isinstance(item, dict):
            continue
        if target_event and normalize_event_name(item.get("event")) != target_event:
            continue
        overlap_count, key_count = _matching_score_for_snapshot(item, selected_event)
        score = (overlap_count, key_count, index)
        if score >= best_score:
            best_index = index
            best_score = score

    return best_index


def best_matching_event(selected_event: dict, events):
    if not isinstance(events, list) or not events:
        return None

    target = normalize_event_name(selected_event.get("event"))
    best_event = None
    best_score = (-1, -1, -1)

    for index, event in enumerate(events):
        if not isinstance(event, dict):
            continue
        if target and normalize_event_name(event.get("event_name")) != target:
            continue
        payload = merged_event_payload(event)
        overlap_count, key_count = _matching_score_for_snapshot(payload, selected_event)
        score = (overlap_count, key_count, index)
        if score >= best_score:
            best_event = event
            best_score = score

    if best_event:
        return best_event

    return events[-1] if events else None


def ga4_event_rows(event):
    if not isinstance(event, dict):
        return pd.DataFrame(columns=["key", "value"])

    rows = [{"key": "event_name", "value": stringify_value(event.get("event_name"))}]

    for key, value in (event.get("params") or {}).items():
        rows.append({"key": key, "value": stringify_value(value)})

    for key, value in (event.get("user_properties") or {}).items():
        rows.append({"key": f"user.{key}", "value": stringify_value(value)})

    return pd.DataFrame(rows)


def snapshot_rows_from_payload(payload, ordered_keys=None):
    if not isinstance(payload, dict) or not payload:
        return pd.DataFrame(columns=["Field", "Value"])

    keys = ordered_keys or list(payload.keys())
    rows = []
    for key in keys:
        if key not in payload:
            continue
        value = payload.get(key)
        if not include_snapshot_field(key):
            continue
        formatted = format_exact_value(value)
        rows.append({"Field": str(key), "Value": formatted})

    return pd.DataFrame(rows)


def snapshot_ga4_payload(event):
    if not isinstance(event, dict):
        return {}

    payload = {}
    event_name = event.get("event_name")
    if event_name not in (None, ""):
        payload["event_name"] = event_name

    params = event.get("params") or {}
    if isinstance(params, dict):
        payload.update(params)

    user_properties = event.get("user_properties") or {}
    if isinstance(user_properties, dict):
        for key, value in user_properties.items():
            payload[f"user.{key}"] = value

    return payload


def include_snapshot_field(key: str) -> bool:
    key_text = str(key or "").strip()
    if not key_text:
        return False
    if key_text in {"event", "event_name"}:
        return True
    if key_text.startswith("gtm."):
        return False
    if normalize_dimension_name(key_text) in SNAPSHOT_HIDDEN_NORMALIZED_KEYS:
        return False
    return True


def is_missing_snapshot_value(value) -> bool:
    text = format_exact_value(value).strip().lower()
    return text in {"", "na", "n/a", "none", "null", "not available"}


def build_snapshot_ordered_keys(*payloads):
    ordered_keys = []
    for key in SNAPSHOT_PRIORITY_KEYS:
        if any(isinstance(payload, dict) and key in payload for payload in payloads):
            ordered_keys.append(key)

    remaining_keys = []
    for payload in payloads:
        if not isinstance(payload, dict):
            continue
        for key in payload.keys():
            if key not in ordered_keys and key not in remaining_keys:
                remaining_keys.append(key)

    for key in sorted(remaining_keys, key=str.lower):
        ordered_keys.append(key)

    filtered_keys = []
    for key in ordered_keys:
        if not include_snapshot_field(key):
            continue
        values = [
            payload.get(key)
            for payload in payloads
            if isinstance(payload, dict) and key in payload
        ]
        if values and all(is_missing_snapshot_value(value) for value in values):
            continue
        filtered_keys.append(key)

    return filtered_keys


def build_datalayer_snapshot_export(result: dict):
    data_layer = load_json_payload(result.get("all_datalayer_json", ""), [])
    selected_event = load_json_payload(result.get("pageview_event_json", ""), {})
    execution_events = load_json_payload(result.get("ga4_execution_events_json", ""), [])
    network_events = load_json_payload(result.get("ga4_network_events_json", ""), [])

    if not isinstance(selected_event, dict):
        selected_event = {}

    if not selected_event and isinstance(data_layer, list):
        for item in reversed(data_layer):
            if not isinstance(item, dict):
                continue
            if normalize_event_name(item.get("event")) == "pageview":
                selected_event = item
                break

    selected_index = None
    if selected_event:
        selected_index = find_matching_datalayer_index(data_layer, selected_event)
        if selected_index is None:
            selected_index = max(len(data_layer) - 1, 0) if isinstance(data_layer, list) and data_layer else 0

    computed_state = build_computed_state(data_layer, selected_index) if selected_index is not None else {}

    if selected_event:
        matched_execution = best_matching_event(selected_event, execution_events)
        matched_network = best_matching_event(selected_event, network_events)
    else:
        matched_execution = (
            find_event_by_name(execution_events, "page_view")
            or find_event_by_name(execution_events, "pageview")
        )
        matched_network = (
            find_event_by_name(network_events, "page_view")
            or find_event_by_name(network_events, "pageview")
        )

    execution_payload = snapshot_ga4_payload(matched_execution)
    network_payload = snapshot_ga4_payload(matched_network)
    ordered_keys = build_snapshot_ordered_keys(
        selected_event,
        computed_state,
        execution_payload,
        network_payload,
    )
    trigger_df = snapshot_rows_from_payload(selected_event, ordered_keys)
    computed_df = snapshot_rows_from_payload(computed_state, ordered_keys)
    execution_df = snapshot_rows_from_payload(execution_payload, ordered_keys)
    network_df = snapshot_rows_from_payload(network_payload, ordered_keys)

    export_frames = []
    for section_name, frame in (
        ("Trigger Event", trigger_df),
        ("Computed State", computed_df),
        ("Execution Payload", execution_df),
        ("Network Payload", network_df),
    ):
        if frame.empty:
            continue
        export_frames.append(frame.assign(Section=section_name))

    export_df = pd.concat(export_frames, ignore_index=True) if export_frames else pd.DataFrame(columns=["Section", "Field", "Value"])
    if not export_df.empty:
        export_df = export_df[["Section", "Field", "Value"]]

    return {
        "selected_index": selected_index,
        "selected_event": selected_event,
        "computed_state": computed_state,
        "execution_payload": execution_payload,
        "network_payload": network_payload,
        "trigger_df": trigger_df,
        "computed_df": computed_df,
        "execution_df": execution_df,
        "network_df": network_df,
        "export_df": export_df,
        "has_trigger_data": not trigger_df.empty,
        "has_computed_data": not computed_df.empty,
        "has_execution_data": not execution_df.empty,
        "has_network_data": not network_df.empty,
    }


def find_event_by_name(events, target_name: str):
    target = normalize_event_name(target_name)
    for event in events or []:
        if not isinstance(event, dict):
            continue
        if normalize_event_name(event.get("event_name")) == target:
            return event
    return None


def count_datalayer_events(result: dict, target_name: str) -> int:
    data_layer = load_json_payload(result.get("all_datalayer_json", ""), [])
    if not isinstance(data_layer, list):
        return 0

    target = normalize_event_name(target_name)
    count = 0
    for item in data_layer:
        if not isinstance(item, dict):
            continue
        if normalize_event_name(item.get("event")) == target:
            count += 1
    return count


def extract_event_names(result: dict):
    names = []
    seen = set()
    for field in ("ga4_execution_events_json", "ga4_network_events_json"):
        events = load_json_payload(result.get(field, ""), [])
        if not isinstance(events, list):
            continue
        for event in events:
            if not isinstance(event, dict):
                continue
            event_name = str(event.get("event_name") or "").strip()
            if not event_name or event_name in seen:
                continue
            seen.add(event_name)
            names.append(event_name)
    return names


def extract_container_id(result: dict):
    execution_events = load_json_payload(result.get("ga4_execution_events_json", ""), [])
    network_events = load_json_payload(result.get("ga4_network_events_json", ""), [])

    candidate_events = [
        find_event_by_name(network_events, "page_view"),
        find_event_by_name(execution_events, "page_view"),
    ]

    if isinstance(network_events, list):
        candidate_events.extend(network_events)
    if isinstance(execution_events, list):
        candidate_events.extend(execution_events)

    for event in candidate_events:
        if not isinstance(event, dict):
            continue
        payload = merged_event_payload(event)
        container_id = payload.get("gtm_container_id")
        if container_id not in (None, ""):
            return format_exact_value(container_id)

    return "Not found"


def extract_measurement_id(result: dict):
    execution_events = load_json_payload(result.get("ga4_execution_events_json", ""), [])
    network_events = load_json_payload(result.get("ga4_network_events_json", ""), [])

    candidate_events = [
        find_event_by_name(network_events, "page_view"),
        find_event_by_name(execution_events, "page_view"),
    ]

    if isinstance(network_events, list):
        candidate_events.extend(network_events)
    if isinstance(execution_events, list):
        candidate_events.extend(execution_events)

    for event in candidate_events:
        if not isinstance(event, dict):
            continue
        payload = merged_event_payload(event)
        measurement_id = payload.get("measurement_id")
        if measurement_id not in (None, ""):
            return format_exact_value(measurement_id)

    return "Not found"


def parse_expected_values(raw_value: str) -> List[str]:
    pieces = re.split(r"[|\n\r]+", str(raw_value or ""))
    return [part.strip() for part in pieces if part.strip()]


def normalize_expected_values_input(raw_value: str) -> str:
    return "|".join(parse_expected_values(raw_value))


def format_expected_values_display(raw_value: str) -> str:
    values = parse_expected_values(raw_value)
    if not values:
        return ""
    return ", ".join(values)


def parse_bulk_execution_rule_lines(raw_value: str, rule_type: str):
    entries = []
    errors = []

    for index, raw_line in enumerate(str(raw_value or "").splitlines(), start=1):
        line = raw_line.strip()
        if not line:
            continue

        field_name = ""
        expected_values = ""

        if rule_type in {"required", "optional"}:
            field_name = line
        else:
            if "=" in line:
                field_name, expected_values = line.split("=", 1)
            elif ":" in line:
                field_name, expected_values = line.split(":", 1)
            else:
                errors.append(f"Line {index}: use `field_name = expected value` format.")
                continue

        field_name = str(field_name or "").strip()
        expected_values = normalize_expected_values_input(expected_values)

        if not field_name:
            errors.append(f"Line {index}: field name is missing.")
            continue

        if rule_type not in {"required", "optional"} and not expected_values:
            errors.append(f"Line {index}: expected value is missing.")
            continue

        entries.append(
            {
                "field_name": field_name,
                "expected_values": expected_values,
            }
        )

    return entries, errors


def split_actual_tokens(raw_value: str) -> List[str]:
    text = str(raw_value or "").strip()
    if not text:
        return []
    pieces = [piece.strip() for piece in re.split(r"[,\n]", text) if piece.strip()]
    if text not in pieces:
        pieces.insert(0, text)
    return pieces


def find_payload_value(payload: dict, field_name: str):
    if not isinstance(payload, dict):
        return "", ""

    target = str(field_name or "").strip()
    if target in payload:
        return target, format_exact_value(payload.get(target))

    target_norm = normalize_dimension_name(target)
    for key, value in payload.items():
        if normalize_dimension_name(key) == target_norm:
            return str(key), format_exact_value(value)

    return "", ""


def evaluate_value_rule(rule_type: str, expected_values_text: str, actual_value: str):
    rule = str(rule_type or "").strip().lower()
    actual_text = str(actual_value or "").strip()
    expected_values = parse_expected_values(expected_values_text)
    actual_tokens = [token.lower() for token in split_actual_tokens(actual_text)]
    actual_text_lower = actual_text.lower()

    if rule == "optional":
        if not actual_text:
            return True, VALIDATION_OPTIONAL_LABEL
        if not expected_values:
            return True, VALIDATION_OPTIONAL_LABEL
        return evaluate_value_rule("one_of", expected_values_text, actual_text)

    if rule == "required":
        return bool(actual_text), VALIDATION_PASS_LABEL if actual_text else VALIDATION_FAIL_LABEL

    if not actual_text:
        return False, VALIDATION_FAIL_LABEL

    if rule == "regex":
        matched = any(re.search(pattern, actual_text) for pattern in expected_values if pattern)
        return matched, VALIDATION_PASS_LABEL if matched else VALIDATION_FAIL_LABEL

    if rule == "contains":
        matched = any(expected.lower() in actual_text_lower for expected in expected_values)
        return matched, VALIDATION_PASS_LABEL if matched else VALIDATION_FAIL_LABEL

    if rule in {"exact", "one_of"}:
        expected_lowers = [value.lower() for value in expected_values]
        matched = actual_text_lower in expected_lowers or any(
            token in expected_lowers for token in actual_tokens
        )
        return matched, VALIDATION_PASS_LABEL if matched else VALIDATION_FAIL_LABEL

    return False, VALIDATION_FAIL_LABEL


def build_execution_validation_rows(snapshot: dict, template_rules: List[dict]):
    execution_payload = snapshot.get("execution_payload") or {}
    execution_df = snapshot.get("execution_df", pd.DataFrame(columns=["Field", "Value"]))

    field_rules = [
        rule
        for rule in template_rules or []
        if str(rule.get("rule_scope") or "").strip().lower() == "execution"
    ]

    if not field_rules:
        return execution_df.copy(), []

    value_rows = []
    used_fields = set()
    validation_rows = []

    for rule in field_rules:
        field_name = str(rule.get("field_name") or "").strip()
        if not field_name:
            continue

        actual_key, actual_value = find_payload_value(execution_payload, field_name)
        used_fields.add(actual_key or field_name)
        matched, validation_label = evaluate_value_rule(
            rule.get("rule_type"),
            rule.get("expected_values"),
            actual_value,
        )
        display_value = actual_value or "Not observed"
        expected_text = str(rule.get("expected_values") or "").strip()
        if rule.get("rule_type") == "required" and not expected_text:
            expected_text = "Required"
        elif rule.get("rule_type") == "optional" and not expected_text:
            expected_text = "Optional"

        value_rows.append(
            {
                "Field": actual_key or field_name,
                "Value": display_value,
                "Expected": expected_text,
                "Validation": validation_label,
            }
        )
        validation_rows.append(
            {
                "field_name": field_name,
                "actual_key": actual_key or field_name,
                "actual_value": display_value,
                "expected": expected_text,
                "matched": matched,
                "validation": validation_label,
                "rule_type": rule.get("rule_type"),
            }
        )

    for _, row in execution_df.iterrows():
        field = str(row.get("Field") or "").strip()
        if field in used_fields:
            continue
        value_rows.append(
            {
                "Field": field,
                "Value": row.get("Value") or "",
                "Expected": "",
                "Validation": "",
            }
        )

    display_df = pd.DataFrame(value_rows)
    if not display_df.empty:
        display_df = display_df.drop_duplicates(subset=["Field", "Value", "Expected", "Validation"], keep="first")

    return display_df, validation_rows


def build_event_validation_rows(event_rows: List[dict], template_rules: List[dict]):
    event_rules = [
        rule
        for rule in template_rules or []
        if str(rule.get("rule_scope") or "").strip().lower() == "event"
    ]
    if not event_rules:
        return pd.DataFrame(event_rows)

    observed_by_name = {
        normalize_event_name(row.get("event_name")): row
        for row in (event_rows or [])
        if str(row.get("event_name") or "").strip()
    }
    display_rows = []
    handled_event_names = set()

    for row in event_rows or []:
        row_copy = dict(row)
        row_copy["expected"] = ""
        row_copy["validation"] = ""
        display_rows.append(row_copy)

    for rule in event_rules:
        configured_values = parse_expected_values(rule.get("expected_values"))
        if not configured_values:
            configured_values = [str(rule.get("field_name") or "").strip()]

        matched_names = []
        for configured in configured_values:
            configured_norm = normalize_event_name(configured)
            if configured_norm in observed_by_name:
                matched_names.append(configured_norm)

        matched = bool(matched_names)
        validation_label = VALIDATION_PASS_LABEL if matched else (
            VALIDATION_OPTIONAL_LABEL if str(rule.get("rule_type") or "").strip().lower() == "optional" else VALIDATION_FAIL_LABEL
        )

        if matched_names:
            for event_name in matched_names:
                handled_event_names.add(event_name)
                for row in display_rows:
                    if normalize_event_name(row.get("event_name")) != event_name:
                        continue
                    row["expected"] = " | ".join(configured_values)
                    row["validation"] = validation_label
        else:
            display_rows.append(
                {
                    "event_name": " | ".join(configured_values),
                    "status": "Expected but not fired",
                    "times_fired": 0,
                    "capture_layer": "Not observed",
                    "key_values_seen": "",
                    "details": [],
                    "technical_details": [],
                    "expected": " | ".join(configured_values),
                    "validation": validation_label,
                }
            )

    return pd.DataFrame(display_rows)


def style_validation_table(dataframe: pd.DataFrame, validation_column: str):
    if dataframe.empty or validation_column not in dataframe.columns:
        return dataframe

    def row_style(row):
        value = str(row.get(validation_column) or "").strip()
        if value == VALIDATION_PASS_LABEL:
            return ["background-color: rgba(22, 163, 74, 0.18)"] * len(row)
        if value == VALIDATION_FAIL_LABEL:
            return ["background-color: rgba(220, 38, 38, 0.18)"] * len(row)
        if value == VALIDATION_OPTIONAL_LABEL:
            return ["background-color: rgba(202, 138, 4, 0.18)"] * len(row)
        return [""] * len(row)

    return dataframe.style.apply(row_style, axis=1)


STATUS_SORT_ORDER = {
    "Captured in network": 0,
    "Captured in execution": 1,
    "Only in trigger": 2,
    "Missing": 3,
    "Not observed": 4,
}

INTERNAL_EVENT_KEYS = {
    "gtm_container_id",
    "measurement_id",
    "client_id",
    "session_id",
    "ads_data_redaction",
    "page_location",
    "page_title",
    "browser_language",
}

NON_CUSTOM_MAPPING_KEYS = {
    "gtmcontainerid",
    "measurementid",
    "clientid",
    "clientidevent",
    "clientiduser",
    "sessionid",
    "adsdataredaction",
    "pagelocation",
    "pagetitle",
    "pagereferrer",
    "browserlanguage",
    "tvceventname",
}

KEY_LABEL_OVERRIDES = {
    "sub_category": "Subcategory",
    "publish_date": "Published",
    "update_date": "Updated",
    "story_id": "Story ID",
    "author_id": "Author ID",
    "page_type": "Page Type",
    "article_type": "Article Type",
    "event_category": "Event Category",
    "event_action": "Event Action",
    "event_label": "Event Label",
    "gtm_container_id": "GTM Container ID",
    "page_location": "Page URL",
    "page_title": "Page Title",
    "browser_language": "Browser Language",
}

SNAPSHOT_HIDDEN_NORMALIZED_KEYS = {
    "gtmuniqueeventid",
    "gtmcontainerid",
    "browserlanguage",
    "uid",
    "usertype",
    "clientid",
    "clientidevent",
    "clientiduser",
    "sessionid",
    "adsdataredaction",
    "tvceventname",
}

SNAPSHOT_PRIORITY_KEYS = [
    "event",
    "event_name",
    "language",
    "category",
    "sub_category",
    "page_type",
    "article_type",
    "placement",
    "page_location",
    "page_title",
    "scroll_percent",
    "story_id",
    "author",
    "publish_date",
    "update_date",
]


def merged_event_payload(event: dict):
    payload = {}
    for field in ("params", "event_params"):
        raw = event.get(field)
        if isinstance(raw, dict):
            payload.update(raw)

    user_properties = event.get("user_properties")
    if isinstance(user_properties, dict):
        for key, value in user_properties.items():
            payload[f"user.{key}"] = value

    return payload


def build_event_groups(events):
    groups = {}

    for event in events or []:
        if not isinstance(event, dict):
            continue

        display_name = str(event.get("event_name") or "").strip() or "(unnamed event)"
        event_key = normalize_event_name(display_name) or display_name
        group = groups.setdefault(
            event_key,
            {
                "event_name": display_name,
                "count": 0,
                "unique_count": 0,
                "signatures": set(),
                "values": {},
            },
        )
        group["count"] += 1

        payload = merged_event_payload(event)
        signature_items = []
        for key, value in payload.items():
            value_text = stringify_value(value)
            if value_text == "":
                continue
            seen_values = group["values"].setdefault(key, [])
            if value_text not in seen_values:
                seen_values.append(value_text)
            if key not in INTERNAL_EVENT_KEYS:
                signature_items.append((normalize_dimension_name(key), value_text))

        signature = tuple(sorted(signature_items))
        if signature not in group["signatures"]:
            group["signatures"].add(signature)
            group["unique_count"] += 1

    return groups


def preview_value_set(values, limit: int = 6):
    if not values:
        return ""
    if len(values) <= limit:
        return " | ".join(values)
    return " | ".join(values[:limit]) + f" (+{len(values) - limit} more)"


def humanize_key(key: str) -> str:
    key_text = str(key or "").strip()
    if key_text in KEY_LABEL_OVERRIDES:
        return KEY_LABEL_OVERRIDES[key_text]
    text = key_text.replace("user.", "user ")
    text = text.replace("_", " ").strip()
    return text.title() if text else ""


def format_readable_value(key: str, value: str) -> str:
    text = str(value or "").strip()
    if not text:
        return ""

    if text.lower() in {"na", "n/a", "none", "null"}:
        return "Not available"

    if key in {"publish_date", "update_date"} or ("T" in text and ":" in text):
        try:
            parsed = datetime.fromisoformat(text.replace("Z", "+00:00"))
            return parsed.strftime("%d %b %Y, %I:%M %p")
        except Exception:
            pass

    if re.fullmatch(r"\d+(?:\.\d+)?", text):
        lower_key = key.lower()
        if key in {"percent_scrolled", "scroll_percentage", "video_percent"} or any(
            token in lower_key for token in ("percent", "percentage", "scroll")
        ):
            return f"{text}%"

    if key in {"percent_scrolled", "scroll_percentage", "video_percent"} and re.fullmatch(r"\d+(?:\.\d+)?", text):
        return f"{text}%"

    return text


def format_readable_values(key: str, values):
    readable = []
    for value in values or []:
        formatted = format_readable_value(key, value)
        if formatted and formatted not in readable:
            readable.append(formatted)
    return readable


def build_event_detail_rows(value_map, *, internal_only: bool = False):
    varying_keys = {
        key
        for key, values in value_map.items()
        if len(format_readable_values(key, values)) > 1
    }
    rows = []
    ordered_items = sorted(
        value_map.items(),
        key=lambda item: (item[0] not in varying_keys, humanize_key(item[0]).lower()),
    )
    for key, values in ordered_items:
        is_internal = key in INTERNAL_EVENT_KEYS
        if internal_only and not is_internal:
            continue
        if not internal_only and is_internal:
            continue

        readable_values = format_readable_values(key, values)
        if not readable_values:
            continue

        rows.append(
            {
                "Field": humanize_key(key),
                "Value": ", ".join(readable_values),
            }
        )

    return rows


def concise_event_highlights(value_map, max_items: int = 4):
    if not value_map:
        return ""

    priority_keys = [
        "percent_scrolled",
        "scroll_percentage",
        "video_percent",
        "category",
        "sub_category",
        "page_type",
        "article_type",
        "author",
        "story_id",
        "publish_date",
        "update_date",
        "link_url",
        "link_text",
        "video_title",
        "video_provider",
        "event_label",
        "event_category",
        "event_action",
        "name",
        "label",
    ]

    candidate_keys = [key for key in value_map.keys() if key not in INTERNAL_EVENT_KEYS]
    if not candidate_keys:
        candidate_keys = list(value_map.keys())

    selected_keys = []
    varying_keys = [
        key
        for key in candidate_keys
        if len(format_readable_values(key, value_map.get(key, []))) > 1
    ]
    for key in varying_keys:
        if key not in selected_keys:
            selected_keys.append(key)
        if len(selected_keys) >= max_items:
            break

    for key in priority_keys:
        if key in candidate_keys and key not in selected_keys:
            selected_keys.append(key)
        if len(selected_keys) >= max_items:
            break

    if len(selected_keys) < max_items:
        for key in candidate_keys:
            if key not in selected_keys:
                selected_keys.append(key)
            if len(selected_keys) >= max_items:
                break

    highlights = []
    for key in selected_keys:
        readable_values = format_readable_values(key, value_map.get(key, []))
        if not readable_values:
            continue
        label = humanize_key(key)
        if len(readable_values) == 1:
            highlights.append(f"{label}: {readable_values[0]}")
        else:
            highlights.append(f"{label}: {', '.join(readable_values)}")

    remaining = len(candidate_keys) - len(selected_keys)
    if remaining > 0:
        highlights.append(f"+{remaining} more fields")

    return " | ".join(highlights)


def is_scroll_event_name(event_name: str) -> bool:
    normalized = normalize_event_name(event_name)
    return "scroll" in normalized


def extract_scroll_percent_values(value_map):
    if not isinstance(value_map, dict):
        return []

    preferred_keys = [
        key
        for key in value_map.keys()
        if "percent" in str(key).lower()
    ]

    readable_values = []
    for key in preferred_keys:
        for value in format_readable_values(key, value_map.get(key, [])):
            if value and value not in readable_values:
                readable_values.append(value)

    return readable_values


def format_mapping_value(key, value):
    if isinstance(value, list):
        readable = format_readable_values(str(key or ""), value)
        return ", ".join(readable) if readable else ""

    formatted = format_readable_value(str(key or ""), value)
    return formatted if formatted else stringify_value(value)


def format_exact_value(value):
    if value is None:
        return ""
    if isinstance(value, list):
        parts = [format_exact_value(item) for item in value]
        parts = [part for part in parts if part != ""]
        return ", ".join(parts)
    if isinstance(value, dict):
        return json.dumps(value, ensure_ascii=False, sort_keys=True)
    return str(value)


def build_event_audit_rows(result: dict):
    execution_events = load_json_payload(result.get("ga4_execution_events_json", ""), [])
    network_events = load_json_payload(result.get("ga4_network_events_json", ""), [])

    execution_groups = build_event_groups(execution_events)
    network_groups = build_event_groups(network_events)

    ordered_event_keys = []
    for event in network_events + execution_events:
        if not isinstance(event, dict):
            continue
        event_name = str(event.get("event_name") or "").strip() or "(unnamed event)"
        event_key = normalize_event_name(event_name) or event_name
        if event_key not in ordered_event_keys:
            ordered_event_keys.append(event_key)

    rows = []
    for event_key in ordered_event_keys:
        execution_group = execution_groups.get(event_key, {})
        network_group = network_groups.get(event_key, {})
        event_name = (
            network_group.get("event_name")
            or execution_group.get("event_name")
            or event_key
        )

        network_count = int(network_group.get("unique_count", 0) or network_group.get("count", 0) or 0)
        execution_count = int(execution_group.get("unique_count", 0) or execution_group.get("count", 0) or 0)

        if network_count:
            status = "Captured in network"
        elif execution_count:
            status = "Captured in execution"
        else:
            status = "Not observed"

        display_count = network_count or execution_count
        if normalize_event_name(event_name) == "pageview":
            datalayer_count = count_datalayer_events(result, "page_view")
            if datalayer_count:
                display_count = datalayer_count

        event_values = network_group.get("values", {}) or execution_group.get("values", {})
        scroll_percent_values = (
            extract_scroll_percent_values(event_values)
            if is_scroll_event_name(event_name)
            else []
        )
        details = build_event_detail_rows(event_values)
        if scroll_percent_values:
            summary_text = f"Scroll Percent: {', '.join(scroll_percent_values)}"
            details = [
                {
                    "Field": "Scroll Percent",
                    "Value": ", ".join(scroll_percent_values),
                }
            ]
        else:
            summary_text = concise_event_highlights(event_values)

        rows.append(
            {
                "event_name": event_name,
                "status": status,
                "times_fired": display_count,
                "capture_layer": "Network" if network_count else "Execution only",
                "key_values_seen": summary_text,
                "details": details,
                "technical_details": build_event_detail_rows(
                    event_values,
                    internal_only=True,
                ),
            }
        )

    rows.sort(key=lambda row: (STATUS_SORT_ORDER.get(row["status"], 99), row["event_name"].lower()))
    return rows


def build_event_detail_table(event_rows):
    detail_rows = []

    for event_row in event_rows or []:
        event_name = event_row.get("event_name") or "(unnamed event)"
        times_fired = event_row.get("times_fired") or 0
        status = event_row.get("status") or ""
        capture_layer = event_row.get("capture_layer") or ""

        for field_type, details in (
            ("User-facing", event_row.get("details") or []),
            ("Technical", event_row.get("technical_details") or []),
        ):
            for detail in details:
                detail_rows.append(
                    {
                        "Event": event_name,
                        "Times Fired": times_fired,
                        "Status": status,
                        "Seen In": capture_layer,
                        "Field Type": field_type,
                        "Field": detail.get("Field") or "",
                        "Value": detail.get("Value") or "",
                    }
                )

        if not (event_row.get("details") or event_row.get("technical_details")):
            detail_rows.append(
                {
                    "Event": event_name,
                    "Times Fired": times_fired,
                    "Status": status,
                    "Seen In": capture_layer,
                    "Field Type": "User-facing",
                    "Field": "(no values)",
                    "Value": "No values captured for this event.",
                }
            )

    return pd.DataFrame(detail_rows)


def is_user_facing_row(row: dict) -> bool:
    keys = [row.get("dl_key"), row.get("exec_key"), row.get("ga4_key")]
    for key in keys:
        key_text = str(key or "")
        if not key_text:
            continue
        if key_text == "event":
            return False
        if key_text.startswith("gtm."):
            return False
    return True


def build_audit_mapping_rows(result: dict):
    mapping_rows = load_json_payload(result.get("mapping_table", ""), [])
    if not isinstance(mapping_rows, list):
        mapping_rows = []

    cleaned_rows = []

    for row in mapping_rows:
        if not isinstance(row, dict) or not is_user_facing_row(row):
            continue

        dimension = row.get("ga4_key") or row.get("exec_key") or row.get("dl_key")
        dimension = str(dimension or "").strip()
        if not dimension:
            continue
        if normalize_dimension_name(dimension) in NON_CUSTOM_MAPPING_KEYS:
            continue

        ga4_value = row.get("ga4_value")
        exec_value = row.get("exec_value")
        dl_value = row.get("dl_value")

        if ga4_value not in (None, ""):
            status = "Captured in network"
        elif exec_value not in (None, ""):
            status = "Captured in execution"
        elif dl_value not in (None, ""):
            status = "Only in trigger"
        else:
            status = "Missing"

        cleaned = {
            "dimension": dimension,
            "trigger_value": format_exact_value(dl_value),
            "execution_value": format_exact_value(exec_value),
            "network_value": format_exact_value(ga4_value),
            "status": status,
        }
        cleaned_rows.append(cleaned)

    cleaned_rows.sort(key=lambda row: (STATUS_SORT_ORDER.get(row["status"], 99), row["dimension"].lower()))
    return cleaned_rows


def summarize_mapping_values(mapping_rows):
    captured_network = []
    captured_execution = []
    trigger_only = []

    for row in mapping_rows:
        dimension = row.get("dimension")
        if row.get("status") == "Captured in network":
            captured_network.append(f"{dimension}={stringify_value(row.get('network_value'))}")
        elif row.get("status") == "Captured in execution":
            captured_execution.append(f"{dimension}={stringify_value(row.get('execution_value'))}")
        elif row.get("status") == "Only in trigger":
            trigger_only.append(f"{dimension}={stringify_value(row.get('trigger_value'))}")

    return captured_network, captured_execution, trigger_only


def preview_list(values, limit: int = 5):
    if not values:
        return "None"
    if len(values) <= limit:
        return ", ".join(values)
    return ", ".join(values[:limit]) + f" (+{len(values) - limit} more)"


def build_comscore_preview(rows: List[Dict[str, Any]]) -> str:
    if not rows:
        return "Not found"

    highlights = []
    for row in rows:
        parts = []
        for key in COMSCORE_PARAM_KEYS:
            value = str(row.get(key) or "").strip()
            if value:
                parts.append(f"{key}={value}")
        if parts:
            highlights.append(", ".join(parts))

    if not highlights:
        return "Tag found"
    return " | ".join(highlights[:2])


def build_audit_focus_summary(result: dict):
    execution_events = load_json_payload(result.get("ga4_execution_events_json", ""), [])
    network_events = load_json_payload(result.get("ga4_network_events_json", ""), [])
    comscore_rows = load_json_payload(result.get("comscore_hits_json", ""), [])
    if not isinstance(comscore_rows, list):
        comscore_rows = []

    execution_pageview = find_event_by_name(execution_events, "page_view")
    network_pageview = find_event_by_name(network_events, "page_view")

    if network_pageview:
        pageview_triggered = True
        pageview_source = "Network"
    elif execution_pageview:
        pageview_triggered = True
        pageview_source = "Execution only"
    else:
        pageview_triggered = False
        pageview_source = "Not fired"

    mapping_rows = build_audit_mapping_rows(result)
    captured_network, captured_execution, trigger_only = summarize_mapping_values(mapping_rows)

    return {
        "pageview_triggered": pageview_triggered,
        "pageview_source": pageview_source,
        "container_id": extract_container_id(result),
        "measurement_id": extract_measurement_id(result),
        "events_fired": extract_event_names(result),
        "event_rows": build_event_audit_rows(result),
        "mapping_rows": mapping_rows,
        "captured_network": captured_network,
        "captured_execution": captured_execution,
        "trigger_only": trigger_only,
        "comscore_present": bool(result.get("comscore_present")),
        "comscore_rows": comscore_rows,
        "comscore_preview": build_comscore_preview(comscore_rows),
    }


with tab_main:
    st.markdown(
        """
Paste one URL and run the audit.

This capture is split into three layers:
- `dataLayer` trigger state
- execution-stage GA4 values intercepted before transport
- final network request / response hits
"""
    )

    if template_load_error:
        st.info(template_load_error)

    url_text = st.text_input(
        "URL",
        placeholder="https://www.example.com/article-1 or www.example.com/article-1",
    )

    template_options = [None, *active_templates]
    selected_template = st.selectbox(
        "Template",
        options=template_options,
        format_func=lambda template: "No template selected" if template is None else build_template_option_label(template),
    )

    wait_seconds = st.slider(
        "Wait time after page load (seconds)",
        min_value=4,
        max_value=20,
        value=8,
    )

    if st.button("Run audit"):
        original_url, normalized_url, input_error = normalize_single_url(url_text)

        if input_error:
            st.error(input_error)
        else:
            if normalized_url != original_url:
                st.info(f"Using normalized URL: `{normalized_url}`")

            results = []
            progress = st.progress(0)
            status_box = st.empty()

            status_box.write(f"Auditing {normalized_url} (1/1)")
            try:
                driver = create_driver(headless=True)
                try:
                    results.append(audit_single_url(driver, normalized_url, wait_seconds))
                finally:
                    driver.quit()
            except Exception as exc:
                st.error(f"Error auditing {normalized_url}")
                st.exception(exc)
            progress.progress(1.0)

            status_box.write("Done.")

            if results:
                summary_rows = []
                for result in results:
                    audit_summary = build_audit_focus_summary(result)
                    summary_rows.append(
                        {
                            "status": result.get("status"),
                            "page_url": result.get("page_url"),
                            "page_title": result.get("page_title"),
                            "pageview_in_datalayer": result.get("pageview_event_found"),
                            "pageview_triggered": audit_summary["pageview_triggered"],
                            "pageview_source": audit_summary["pageview_source"],
                            "comscore_present": audit_summary["comscore_present"],
                            "comscore_values": audit_summary["comscore_preview"],
                            "events_fired": ", ".join(audit_summary["events_fired"]) or "None",
                            "captured_in_network": preview_list(audit_summary["captured_network"]),
                            "captured_in_execution": preview_list(audit_summary["captured_execution"]),
                            "trigger_only": preview_list(audit_summary["trigger_only"]),
                            "issues": result.get("issues"),
                        }
                    )

                summary_df = pd.DataFrame(summary_rows)
                display_columns = [
                    "page_url",
                    "pageview_triggered",
                    "pageview_source",
                    "comscore_present",
                    "events_fired",
                    "issues",
                ]
                display_summary_df = summary_df[display_columns]
                st.subheader("Summary")
                st.dataframe(display_summary_df, use_container_width=True, hide_index=True)

                csv = summary_df.to_csv(index=False).encode("utf-8")
                st.download_button(
                    "Download audit summary CSV",
                    csv,
                    export_filename("ga4_audit_summary", "csv"),
                    "text/csv",
                )

                if len(results) == 1:
                    result = results[0]
                    audit_summary = build_audit_focus_summary(result)
                    selected_template_rules = []
                    if selected_template:
                        selected_template_rules = [
                            rule
                            for rule in template_rules
                            if str(rule.get("template_id") or "").strip()
                            == str(selected_template.get("template_id") or "").strip()
                        ]

                    log_written = False
                    log_error = ""
                    try:
                        log_written, log_error = append_audit_log(
                            logged_in_email,
                            result,
                            audit_summary,
                        )
                    except Exception as exc:
                        log_error = str(exc)

                    if log_written:
                        st.success("Audit logged to Google Sheet.")
                    elif log_error:
                        st.warning(f"Audit finished, but log entry could not be written. {log_error}")

                    if result.get("preload_hook_error"):
                        st.warning(
                            "Early instrumentation was not installed cleanly. "
                            f"Details: {result['preload_hook_error']}"
                        )

                    stat_col1, stat_col2, stat_col3, stat_col4, stat_col5, stat_col6 = st.columns(6)
                    stat_col1.metric(
                        "Pageview Triggered",
                        "Yes" if audit_summary["pageview_triggered"] else "No",
                    )
                    stat_col2.metric("Pageview Source", audit_summary["pageview_source"])
                    stat_col3.metric("Events Fired", str(len(audit_summary["events_fired"])))
                    stat_col4.metric("Container ID", audit_summary["container_id"])
                    stat_col5.metric("Measurement ID", audit_summary["measurement_id"])
                    stat_col6.metric(
                        "Comscore",
                        "Yes" if audit_summary["comscore_present"] else "No",
                    )

                    snapshot = build_datalayer_snapshot_export(result)
                    if selected_template:
                        st.caption(
                            f"Template validation active: **{selected_template.get('template_name') or 'Unnamed template'}**"
                        )
                        if not selected_template_rules:
                            st.info("This template has no rules yet. Add execution-field or event rules in Template Manager.")

                    st.markdown("### DataLayer Snapshot")
                    st.caption(
                        "Primary audit view. This is the closest in-app match to the GTM dataLayer extension, using exact raw values from the captured run."
                    )
                    selected_index_label = (
                        str(snapshot["selected_index"])
                        if snapshot.get("selected_index") is not None
                        else "Unavailable in this run"
                    )
                    st.caption(f"Selected dataLayer index: {selected_index_label}")

                    trigger_col, state_col, exec_col = st.columns(3)
                    with trigger_col:
                        st.markdown("#### Trigger Event")
                        if snapshot["trigger_df"].empty:
                            st.info("Trigger event was not accessible in this run.")
                        else:
                            st.dataframe(snapshot["trigger_df"], use_container_width=True, hide_index=True)
                    with state_col:
                        st.markdown("#### Computed State")
                        if snapshot["computed_df"].empty:
                            st.info("Computed state could not be built for this run.")
                        else:
                            st.dataframe(snapshot["computed_df"], use_container_width=True, hide_index=True)
                    with exec_col:
                        st.markdown("#### Execution Payload")
                        if selected_template_rules:
                            execution_display_df, _ = build_execution_validation_rows(
                                snapshot,
                                selected_template_rules,
                            )
                            if snapshot["execution_df"].empty:
                                st.caption(
                                    "Execution payload was not isolated in this run. Template checks below stay tied to execution-layer availability."
                                )
                        else:
                            execution_display_df = snapshot["execution_df"]
                            if execution_display_df.empty and not snapshot["network_df"].empty:
                                st.caption("Execution payload unavailable in this run. Showing final matched payload instead.")
                                execution_display_df = snapshot["network_df"]

                        if execution_display_df.empty:
                            st.info("No execution payload matched this event.")
                        else:
                            if selected_template_rules and "Validation" in execution_display_df.columns:
                                st.dataframe(
                                    style_validation_table(execution_display_df, "Validation"),
                                    use_container_width=True,
                                    hide_index=True,
                                )
                            else:
                                st.dataframe(execution_display_df, use_container_width=True, hide_index=True)

                    st.markdown("### Events")
                    event_df = (
                        build_event_validation_rows(audit_summary["event_rows"], selected_template_rules)
                        if selected_template_rules
                        else pd.DataFrame(audit_summary["event_rows"])
                    )
                    if event_df.empty:
                        st.info("No GA4 events were detected during the audit window.")
                    else:
                        st.caption(
                            "Quick event summary only. Use DataLayer Snapshot above for the detailed field-by-field audit."
                        )
                        event_display_columns = ["event_name", "status", "times_fired", "capture_layer"]
                        if "expected" in event_df.columns:
                            event_display_columns.append("expected")
                        if "validation" in event_df.columns:
                            event_display_columns.append("validation")
                        event_display_df = event_df[event_display_columns].rename(
                            columns={
                                "event_name": "Event",
                                "status": "Status",
                                "times_fired": "Times Fired",
                                "capture_layer": "Seen In",
                                "expected": "Expected",
                                "validation": "Validation",
                            }
                        )
                        if "Validation" in event_display_df.columns:
                            st.dataframe(
                                style_validation_table(event_display_df, "Validation"),
                                use_container_width=True,
                                hide_index=True,
                            )
                        else:
                            st.dataframe(event_display_df, use_container_width=True, hide_index=True)

                    st.markdown("### Comscore")
                    if not audit_summary["comscore_present"]:
                        st.info("No Comscore tag hit was captured during this audit run.")
                    else:
                        st.caption(
                            "Exact Comscore values captured from scorecardresearch requests and beacon.js during this run."
                        )
                        comscore_df = pd.DataFrame(audit_summary["comscore_rows"])
                        if comscore_df.empty:
                            st.info("Comscore requests were seen, but no c1/c2/c7/c8 values could be extracted.")
                        else:
                            comscore_display_df = comscore_df[
                                ["hit_type", "times_fired", "status_chain", "c1", "c2", "c7", "c8", "request_url"]
                            ].rename(
                                columns={
                                    "hit_type": "Hit Type",
                                    "times_fired": "Times Fired",
                                    "status_chain": "Status Chain",
                                    "c1": "c1",
                                    "c2": "c2",
                                    "c7": "c7",
                                    "c8": "c8",
                                    "request_url": "Request URL",
                                }
                            )
                            st.dataframe(comscore_display_df, use_container_width=True, hide_index=True)

                    with st.expander("Advanced debug", expanded=False):
                        left_col, right_col = st.columns(2)

                        with left_col:
                            render_json_block(
                                "dataLayer snapshot",
                                result.get("all_datalayer_json", ""),
                                "No dataLayer snapshot captured.",
                            )
                            render_json_block(
                                "page_view / pageview event",
                                result.get("pageview_event_json", ""),
                                "No page_view event found in dataLayer.",
                            )
                            render_json_block(
                                "Scroll event",
                                result.get("scroll_event_json", ""),
                                "No scroll event captured.",
                            )

                        with right_col:
                            render_event_list(
                                "Execution-stage GA4 values",
                                result.get("ga4_execution_events_json", ""),
                                "No execution-stage GA4 events captured.",
                            )
                            render_event_list(
                                "Execution transport hits (pre-network)",
                                result.get("ga4_execution_hits_json", ""),
                                "No pre-network transport hits captured.",
                            )
                            st.caption("`Raw gtag calls` can stay empty when the site fires GA4 through GTM rather than direct `window.gtag(...)` calls.")
                            render_event_list(
                                "Raw gtag calls",
                                result.get("ga4_gtag_calls_json", ""),
                                "No gtag calls captured.",
                            )
                            render_event_list(
                                "Final GA4 events decoded from network",
                                result.get("ga4_network_events_json", ""),
                                "No network GA4 events decoded.",
                            )
                            render_json_block(
                                "Comscore captures",
                                result.get("comscore_hits_json", ""),
                                "No Comscore values captured.",
                            )

                        render_json_block(
                            "Consent actions",
                            result.get("consent_clicks_json", ""),
                            "No consent click was performed.",
                        )

with tab_compare:
    st.markdown("Compare tagging between two URLs, typically Prod vs Stage.")

    prod_col, stage_col = st.columns(2)
    prod_url = prod_col.text_input("Prod URL")
    stage_url = stage_col.text_input("Stage URL")

    wait_cmp = st.slider("Wait seconds", 4, 20, 8, key="wait_compare")
    if st.button("Run comparison"):
        if not prod_url or not stage_url:
            st.error("Enter both URLs.")
        else:
            driver = create_driver(headless=True)
            try:
                prod = audit_single_url(driver, prod_url, wait_cmp)
                stage = audit_single_url(driver, stage_url, wait_cmp)
            finally:
                driver.quit()

            st.subheader("Comparison summary")
            st.dataframe(
                pd.DataFrame(
                    [
                        {
                            "env": "Prod",
                            "status": prod.get("status"),
                            "page_template": prod.get("page_template"),
                            "ga4_execution_present": prod.get("ga4_execution_present"),
                            "ga4_collect_present": prod.get("ga4_collect_present"),
                            "comscore_present": prod.get("comscore_present"),
                            "pv_page_location": prod.get("pv_page_location"),
                            "pv_page_title": prod.get("pv_page_title"),
                            "issues": prod.get("issues"),
                        },
                        {
                            "env": "Stage",
                            "status": stage.get("status"),
                            "page_template": stage.get("page_template"),
                            "ga4_execution_present": stage.get("ga4_execution_present"),
                            "ga4_collect_present": stage.get("ga4_collect_present"),
                            "comscore_present": stage.get("comscore_present"),
                            "pv_page_location": stage.get("pv_page_location"),
                            "pv_page_title": stage.get("pv_page_title"),
                            "issues": stage.get("issues"),
                        },
                    ]
                ),
                use_container_width=True,
            )


if tab_template_manager is not None:
    with tab_template_manager:
        st.markdown("Manage audit templates and expected values for execution fields and events.")

        if template_load_error:
            st.error(template_load_error)
        else:
            st.caption(
                "Templates are stored in the same Google Sheet backing this app. Only your account can add or edit them."
            )

            template_rules_by_template = {}
            for rule in template_rules:
                template_rules_by_template.setdefault(str(rule.get("template_id") or "").strip(), []).append(rule)

            st.markdown("### Add Template")
            with st.form("template_manager_add_template", clear_on_submit=True):
                template_name = st.text_input("Template name", placeholder="Daily Jagran Article")
                meta_col1, meta_col2 = st.columns(2)
                with meta_col1:
                    domain_name = st.text_input("Domain / site name", placeholder="www.example.com")
                    measurement_id = st.text_input("GA4 measurement ID", placeholder="G-XXXXXXXXXX")
                with meta_col2:
                    container_id = st.text_input("GTM container ID", placeholder="GTM-XXXXXXX")
                    url_pattern = st.text_input("Reference URL / pattern", placeholder="https://www.example.com/world/*")
                template_active = st.checkbox("Active", value=True)
                add_template_submitted = st.form_submit_button("Add template")

            if add_template_submitted:
                if not str(template_name or "").strip():
                    st.error("Template name is required.")
                elif not any(
                    str(value or "").strip()
                    for value in (domain_name, measurement_id, container_id, url_pattern)
                ):
                    st.error("Add at least one identifier: domain, measurement ID, container ID, or URL pattern.")
                else:
                    success, response = append_template_record(
                        logged_in_email,
                        {
                            "template_name": template_name,
                            "domain_name": domain_name,
                            "measurement_id": measurement_id,
                            "container_id": container_id,
                            "url_pattern": url_pattern,
                            "active": template_active,
                        },
                    )
                    if success:
                        st.success(f"Template added: {template_name}")
                        st.rerun()
                    else:
                        st.error(response)

            st.markdown("### Add Template Rule")
            if not active_templates:
                st.info("Create a template first, then add its execution-field and event rules here.")
            else:
                template_choice_for_rule = st.selectbox(
                    "Template for this rule",
                    options=active_templates,
                    format_func=build_template_option_label,
                    key="template_rule_template_selector",
                )
                with st.form("template_manager_add_rule", clear_on_submit=True):
                    rule_col1, rule_col2 = st.columns(2)
                    with rule_col1:
                        scope_label = st.selectbox("Rule scope", options=list(RULE_SCOPE_OPTIONS.keys()))
                    with rule_col2:
                        rule_type = st.selectbox("Rule type", options=RULE_TYPE_OPTIONS)

                    if RULE_SCOPE_OPTIONS[scope_label] == "execution":
                        field_label = "Execution field rules"
                        field_help = (
                            "Add one execution rule per line using `field_name = expected value`. "
                            "Examples: `page_type = article detail` or `category = world|india`."
                        )
                        expected_label = "Execution field rules"
                        expected_help = (
                            "Enter one rule per line. Pipe-separated expected values still work inside a line."
                        )
                        expected_placeholder = (
                            "page_type = article detail\n"
                            "category = world|india\n"
                            "scroll_percent = 0%|25%|50%|75%|100%"
                        )
                    else:
                        field_label = "Rule label / event group"
                        field_help = "Use a short label for this event rule, like `Core article events`."
                        expected_label = "Expected event names"
                        expected_help = "Enter one event name per line. Pipe-separated values also work."
                        expected_placeholder = "page_view\npage_scroll"

                    if RULE_SCOPE_OPTIONS[scope_label] == "execution":
                        field_name = ""
                        execution_rule_lines = st.text_area(
                            expected_label,
                            help=expected_help,
                            placeholder=expected_placeholder,
                            height=180,
                        )
                        parsed_execution_rules, parsed_execution_rule_errors = parse_bulk_execution_rule_lines(
                            execution_rule_lines,
                            rule_type,
                        )
                        if parsed_execution_rules:
                            st.caption(f"{len(parsed_execution_rules)} execution rule(s) ready to save.")
                        if parsed_execution_rule_errors:
                            st.caption("Preview issues: " + " ".join(parsed_execution_rule_errors[:3]))
                    else:
                        field_name = st.text_input(field_label, help=field_help)
                        expected_values_input = st.text_area(
                            expected_label,
                            help=expected_help,
                            placeholder=expected_placeholder,
                            height=110,
                        )
                        parsed_preview_values = parse_expected_values(expected_values_input)
                        if parsed_preview_values:
                            st.caption(f"Will be stored as: {' | '.join(parsed_preview_values)}")
                    notes = st.text_input("Notes (optional)")
                    add_rule_submitted = st.form_submit_button("Add rule")

                if add_rule_submitted:
                    if RULE_SCOPE_OPTIONS[scope_label] == "execution":
                        parsed_execution_rules, parsed_execution_rule_errors = parse_bulk_execution_rule_lines(
                            execution_rule_lines,
                            rule_type,
                        )
                        if not parsed_execution_rules:
                            if parsed_execution_rule_errors:
                                st.error(" ".join(parsed_execution_rule_errors[:5]))
                            else:
                                st.error("Add at least one execution field rule.")
                        elif parsed_execution_rule_errors:
                            st.error(" ".join(parsed_execution_rule_errors[:5]))
                        else:
                            success, response = append_template_rules(
                                logged_in_email,
                                [
                                    {
                                        "template_id": template_choice_for_rule.get("template_id"),
                                        "rule_scope": RULE_SCOPE_OPTIONS[scope_label],
                                        "field_name": entry["field_name"],
                                        "rule_type": rule_type,
                                        "expected_values": entry["expected_values"],
                                        "notes": notes,
                                    }
                                    for entry in parsed_execution_rules
                                ],
                            )
                            if success:
                                st.success(f"{response} rule(s) added.")
                                st.rerun()
                            else:
                                st.error(response)
                    else:
                        expected_values = normalize_expected_values_input(expected_values_input)
                        if not str(field_name or "").strip():
                            st.error(f"{field_label} is required.")
                        elif rule_type not in {"required", "optional"} and not str(expected_values or "").strip():
                            st.error("Expected values are required for this rule type.")
                        else:
                            success, response = append_template_rule(
                                logged_in_email,
                                {
                                    "template_id": template_choice_for_rule.get("template_id"),
                                    "rule_scope": RULE_SCOPE_OPTIONS[scope_label],
                                    "field_name": field_name,
                                    "rule_type": rule_type,
                                    "expected_values": expected_values,
                                    "notes": notes,
                                },
                            )
                            if success:
                                st.success("Rule added.")
                                st.rerun()
                            else:
                                st.error(response)

            st.markdown("### Existing Templates")
            if not template_records:
                st.info("No templates saved yet.")
            else:
                template_table_rows = []
                for template in template_records:
                    template_id = str(template.get("template_id") or "").strip()
                    template_table_rows.append(
                        {
                            "Template": template.get("template_name") or "",
                            "Domain": template.get("domain_name") or "",
                            "Measurement ID": template.get("measurement_id") or "",
                            "Container ID": template.get("container_id") or "",
                            "URL Pattern": template.get("url_pattern") or "",
                            "Active": "Yes" if template.get("active") else "No",
                            "Rules": len(template_rules_by_template.get(template_id, [])),
                        }
                    )
                st.dataframe(pd.DataFrame(template_table_rows), use_container_width=True, hide_index=True)

                inspect_template = st.selectbox(
                    "View rules for template",
                    options=template_records,
                    format_func=build_template_option_label,
                    key="template_manager_view_selector",
                )
                inspect_template_id = str(inspect_template.get("template_id") or "").strip()
                selected_template_rules_table = pd.DataFrame(template_rules_by_template.get(inspect_template_id, []))
                st.markdown("### Template Rules")
                if selected_template_rules_table.empty:
                    st.info("No rules for this template yet.")
                else:
                    selected_template_rules_table["expected_values_display"] = selected_template_rules_table["expected_values"].apply(
                        format_expected_values_display
                    )
                    st.dataframe(
                        selected_template_rules_table[
                            ["rule_scope", "field_name", "rule_type", "expected_values_display", "notes", "created_at"]
                        ].rename(
                            columns={
                                "rule_scope": "Scope",
                                "field_name": "Field / Event",
                                "rule_type": "Rule Type",
                                "expected_values_display": "Expected Values",
                                "notes": "Notes",
                                "created_at": "Created At",
                            }
                        ),
                        use_container_width=True,
                        hide_index=True,
                    )
