import os
import re
import io
import gc
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
    from streamlit_autorefresh import st_autorefresh
except Exception:
    st_autorefresh = None
try:
    import extra_streamlit_components as stx
except Exception:
    stx = None
from selenium import webdriver as selenium_webdriver
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

NETWORK_CAPTURE_SCOPES = [
    r".*googletagmanager\.com/.*",
    r".*google-analytics\.com/.*collect.*",
    r".*google\.com/ccm/collect.*",
    r".*scorecardresearch\.com/.*",
    r".*chartbeat\.net/.*",
]


def create_driver(
    headless: bool = True,
    performance_logs: bool = True,
    capture_network: bool = True,
):
    chrome_options = Options()
    if headless:
        chrome_options.add_argument("--headless=new")

    chrome_options.add_argument("--no-sandbox")
    chrome_options.add_argument("--disable-dev-shm-usage")
    chrome_options.add_argument("--disable-gpu")
    chrome_options.add_argument("--disable-quic")
    chrome_options.add_argument("--disable-extensions")
    chrome_options.add_argument("--disable-background-networking")
    chrome_options.add_argument("--autoplay-policy=no-user-gesture-required")
    chrome_options.add_argument("--disable-default-apps")
    chrome_options.add_argument("--disable-sync")
    chrome_options.add_argument("--metrics-recording-only")
    chrome_options.add_argument("--no-first-run")
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
        "--disable-features=PreloadMediaEngagementData,MediaEngagementBypassAutoplayPolicies"
    )
    chrome_options.add_argument(
        "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"
    )
    if performance_logs:
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
    seleniumwire_options = {
        "request_storage": "memory",
        "request_storage_max_size": 120,
        "disable_encoding": True,
    }

    try:
        driver_module = webdriver if capture_network else selenium_webdriver
        if service:
            if capture_network:
                driver = driver_module.Chrome(
                    options=chrome_options,
                    service=service,
                    seleniumwire_options=seleniumwire_options,
                )
            else:
                driver = driver_module.Chrome(options=chrome_options, service=service)
        else:
            if capture_network:
                driver = driver_module.Chrome(
                    options=chrome_options,
                    seleniumwire_options=seleniumwire_options,
                )
            else:
                driver = driver_module.Chrome(options=chrome_options)
        if capture_network:
            try:
                driver.scopes = NETWORK_CAPTURE_SCOPES
            except Exception:
                pass
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
CHARTBEAT_HOST_PATTERN = re.compile(r"(?:^|[.])chartbeat\.(?:net|com)$", re.I)
CHARTBEAT_PING_PATH_PATTERN = re.compile(r"/ping(?:$|[/?])", re.I)
CHARTBEAT_PARAM_KEYS = ("h", "p", "d", "g", "u", "x", "m", "t", "title")
CHARTBEAT_GENERIC_PARAM_RE = re.compile(
    r"(?:[?&]|\b)(h|p|d|g|u|x|m|t|title)=([^&'\"\\s]+)",
    re.I,
)

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


def _is_chartbeat_hit(url: str) -> bool:
    parsed = urlparse(str(url or ""))
    host = parsed.netloc.lower().split(":", 1)[0]
    path = parsed.path or ""
    if not CHARTBEAT_HOST_PATTERN.search(host):
        return False
    return bool(CHARTBEAT_PING_PATH_PATTERN.search(path))


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


def _filter_chartbeat_params(values: Dict[str, List[str]]) -> Dict[str, List[str]]:
    filtered: Dict[str, List[str]] = {}
    for key, raw_values in (values or {}).items():
        key_text = str(key or "").strip().lower()
        if key_text not in CHARTBEAT_PARAM_KEYS:
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


def _extract_chartbeat_params_from_text(value: str) -> Dict[str, List[str]]:
    text = str(value or "")
    if not text:
        return {}

    try:
        parsed = parse_qs(unquote_plus(text), keep_blank_values=True)
        filtered = _filter_chartbeat_params(parsed)
        if filtered:
            return filtered
    except Exception:
        pass

    matches: Dict[str, List[str]] = {}
    for match in CHARTBEAT_GENERIC_PARAM_RE.finditer(text):
        key = match.group(1).lower()
        val = unquote_plus(match.group(2))
        matches.setdefault(key, [])
        if val not in matches[key]:
            matches[key].append(val)
    if matches:
        return matches

    decoded = _base64_decode_attempt(text)
    if decoded and decoded != text:
        return _extract_chartbeat_params_from_text(decoded)

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


def _build_chartbeat_capture_row(hit: Dict[str, Any]) -> Dict[str, Any]:
    url = str(hit.get("url") or hit.get("request_url") or "")
    combined: Dict[str, List[str]] = {}

    try:
        query_params = _filter_chartbeat_params(parse_qs(urlparse(url).query, keep_blank_values=True))
        combined = _merge_multivalue_dicts(combined, query_params)
    except Exception:
        pass

    combined = _merge_multivalue_dicts(
        combined,
        _extract_chartbeat_params_from_text(hit.get("request_body") or ""),
    )

    for headers_field in ("request_headers", "response_headers", "headers"):
        headers = hit.get(headers_field) or {}
        if not isinstance(headers, dict):
            continue
        for header_value in headers.values():
            combined = _merge_multivalue_dicts(
                combined,
                _extract_chartbeat_params_from_text(header_value),
            )

    response_headers = hit.get("response_headers") or hit.get("headers") or {}
    if isinstance(response_headers, dict):
        location_value = _case_insensitive_get(response_headers, "Location")
        combined = _merge_multivalue_dicts(
            combined,
            _extract_chartbeat_params_from_text(location_value or ""),
        )

    summary_parts = []
    for key in ("h", "p", "d", "g", "title", "t", "u", "x", "m"):
        value_text = format_exact_value(combined.get(key) or [])
        if value_text:
            if key == "t" and combined.get("title"):
                continue
            summary_parts.append(f"{key}={value_text}")

    return {
        "hit_type": "Ping Request",
        "source": hit.get("source") or "",
        "status": hit.get("status") or hit.get("response_status") or "",
        "request_url": url,
        "h": format_exact_value(combined.get("h") or []),
        "p": format_exact_value(combined.get("p") or []),
        "d": format_exact_value(combined.get("d") or []),
        "g": format_exact_value(combined.get("g") or []),
        "title": format_exact_value(combined.get("title") or combined.get("t") or []),
        "u": format_exact_value(combined.get("u") or []),
        "x": format_exact_value(combined.get("x") or []),
        "m": format_exact_value(combined.get("m") or []),
        "params_summary": " | ".join(summary_parts),
    }


def _has_chartbeat_values(row: Dict[str, Any]) -> bool:
    return any(
        str(row.get(key) or "").strip()
        for key in ("h", "p", "d", "g", "title", "u", "x", "m")
    )


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


def build_chartbeat_capture_rows(hits: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    grouped_rows: Dict[Tuple[str, str, str, str, str, str, str, str], Dict[str, Any]] = {}

    for hit in hits or []:
        if not isinstance(hit, dict):
            continue
        row = _build_chartbeat_capture_row(hit)
        if not _has_chartbeat_values(row):
            continue

        key = (
            row["h"],
            row["p"],
            row["d"],
            row["g"],
            row["title"],
            row["u"],
            row["x"],
            row["m"],
        )
        grouped = grouped_rows.setdefault(
            key,
            {
                "hit_type": row["hit_type"],
                "times_fired": 0,
                "status_chain": [],
                "h": row["h"],
                "p": row["p"],
                "d": row["d"],
                "g": row["g"],
                "title": row["title"],
                "u": row["u"],
                "x": row["x"],
                "m": row["m"],
                "params_summary": row["params_summary"],
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
                "h": grouped["h"],
                "p": grouped["p"],
                "d": grouped["d"],
                "g": grouped["g"],
                "title": grouped["title"],
                "u": grouped["u"],
                "x": grouped["x"],
                "m": grouped["m"],
                "params_summary": grouped["params_summary"],
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
) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]], List[Dict[str, Any]]]:
    try:
        raw_entries = driver.get_log("performance")
    except Exception:
        return [], [], [], []

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
                or _is_chartbeat_hit(url)
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
                or _is_chartbeat_hit(url)
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
    chartbeat_hits: List[Dict[str, Any]] = []

    for request_id, item in requests_by_id.items():
        url = str(item.get("url") or "")
        if not url:
            continue
        if not (
            _is_ga4_collect_hit(url)
            or _is_ccm_pageview_hit(url, page_domain)
            or _is_comscore_hit(url)
            or _is_chartbeat_hit(url)
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
        elif _is_chartbeat_hit(url):
            chartbeat_hits.append(hit)
        elif _is_ccm_pageview_hit(url, page_domain):
            ccm_pageviews.append(hit)
        else:
            ga4_collects.append(hit)

    return ga4_collects, ccm_pageviews, comscore_hits, chartbeat_hits


def detect_tag_scripts_in_dom(driver) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
    try:
        page_source = str(driver.page_source or "")
    except Exception:
        page_source = ""

    gtm_scripts: List[Dict[str, Any]] = []
    gtag_scripts: List[Dict[str, Any]] = []

    for match in GTM_SCRIPT_PATTERN.findall(page_source):
        gtm_scripts.append(
            {
                "source": "dom",
                "url": match,
                "method": "GET",
                "status": "Observed",
                "response_status": "Observed",
                "content_type": "script",
                "headers": {},
                "request_headers": {},
                "response_headers": {},
                "request_body": "",
                "response_body": "",
                "decoded_events": [],
            }
        )

    for match in GTAG_SCRIPT_PATTERN.findall(page_source):
        gtag_scripts.append(
            {
                "source": "dom",
                "url": match,
                "method": "GET",
                "status": "Observed",
                "response_status": "Observed",
                "content_type": "script",
                "headers": {},
                "request_headers": {},
                "response_headers": {},
                "request_body": "",
                "response_body": "",
                "decoded_events": [],
            }
        )

    return gtm_scripts, gtag_scripts


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
    chartbeat_hits: List[Dict[str, Any]] = []

    for request in getattr(driver, "requests", []) or []:
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
        elif _is_chartbeat_hit(url):
            chartbeat_hits.append(hit)

    perf_ga4_collects, perf_ccm_pageviews, perf_comscore_hits, perf_chartbeat_hits = extract_collect_hits_from_performance_logs(driver, page_domain)
    ga4_collects = merge_network_hits(ga4_collects, perf_ga4_collects)
    ccm_pageviews = merge_network_hits(ccm_pageviews, perf_ccm_pageviews)
    comscore_hits = merge_network_hits(comscore_hits, perf_comscore_hits)
    chartbeat_hits = merge_network_hits(chartbeat_hits, perf_chartbeat_hits)

    if not gtm_scripts and not gtag_scripts:
        dom_gtm_scripts, dom_gtag_scripts = detect_tag_scripts_in_dom(driver)
        gtm_scripts = dom_gtm_scripts
        gtag_scripts = dom_gtag_scripts

    return {
        "gtm_present": bool(gtm_scripts),
        "gtag_present": bool(gtag_scripts),
        "ga4_collect_present": bool(ga4_collects),
        "ccm_pageview_present": bool(ccm_pageviews),
        "comscore_present": bool(comscore_hits),
        "chartbeat_present": bool(chartbeat_hits),
        "gtm_scripts": gtm_scripts,
        "gtag_scripts": gtag_scripts,
        "ga4_collects": ga4_collects,
        "ccm_pageviews": ccm_pageviews,
        "comscore_hits": comscore_hits,
        "chartbeat_hits": chartbeat_hits,
    }


def categorize_preload_transport_hits(hits: List[Dict[str, Any]], page_domain: str) -> Dict[str, Any]:
    ga4_collects: List[Dict[str, Any]] = []
    ccm_pageviews: List[Dict[str, Any]] = []
    comscore_hits: List[Dict[str, Any]] = []
    chartbeat_hits: List[Dict[str, Any]] = []

    for hit in hits or []:
        url = str(hit.get("url") or hit.get("request_url") or "")
        normalized_hit = dict(hit)
        if "url" not in normalized_hit:
            normalized_hit["url"] = url
        normalized_hit.setdefault("source", "preload_transport")
        normalized_hit.setdefault("status", "Observed")
        normalized_hit.setdefault("response_status", "Observed")

        if _is_comscore_hit(url):
            comscore_hits.append(normalized_hit)
        elif _is_chartbeat_hit(url):
            chartbeat_hits.append(normalized_hit)
        elif _is_ccm_pageview_hit(url, page_domain):
            ccm_pageviews.append(normalized_hit)
        elif _is_ga4_collect_hit(url):
            ga4_collects.append(normalized_hit)

    return {
        "gtm_present": False,
        "gtag_present": False,
        "ga4_collect_present": bool(ga4_collects),
        "ccm_pageview_present": bool(ccm_pageviews),
        "comscore_present": bool(comscore_hits),
        "chartbeat_present": bool(chartbeat_hits),
        "gtm_scripts": [],
        "gtag_scripts": [],
        "ga4_collects": ga4_collects,
        "ccm_pageviews": ccm_pageviews,
        "comscore_hits": comscore_hits,
        "chartbeat_hits": chartbeat_hits,
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

def scroll_before_taboola(driver, scroll_pause: float = 0.2, max_steps: int = 8) -> None:
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
# Video playback helpers
# -------------------------

VIDEO_PLAY_SELECTORS = [
    "video",
    "button[aria-label*='play' i]",
    "button[title*='play' i]",
    "[aria-label*='video' i]",
    "[data-testid*='video' i]",
    "[class*='play' i]",
    "[class*='video' i] button",
    "[class*='video' i] [role='button']",
    "[class*='video' i] img",
    "img[src*='/videos/' i][src*='thumbnail' i]",
    "img[src$='.gif' i]",
    "[poster]",
    "[data-testid*='play' i]",
]

ARTICLE_HERO_VIDEO_SELECTORS = [
    ".ArticleDetail_relatedvideo__wvgRP img",
    ".ArticleDetail_relatedvideo__wvgRP .article",
    ".ArticleDetail_relatedvideo__wvgRP i.videoImage",
    ".relatedvideo img",
    ".relatedvideo .article",
    "i.videoImage",
]


def _click_element(driver, element) -> bool:
    try:
        driver.execute_script("arguments[0].scrollIntoView({block:'center', inline:'center'});", element)
    except Exception:
        pass
    time.sleep(0.05)
    for click_attempt in (
        lambda: element.click(),
        lambda: driver.execute_script("arguments[0].click();", element),
    ):
        try:
            click_attempt()
            return True
        except Exception:
            continue
    return False


def _play_visible_videos_in_current_context(driver) -> bool:
    try:
        played = driver.execute_script(
            """
            const elements = Array.from(document.querySelectorAll("video"));
            let started = false;
            elements.forEach((video) => {
              const rect = video.getBoundingClientRect();
              if (!rect.width || !rect.height) return;
              try {
                video.muted = true;
                video.defaultMuted = true;
                video.playsInline = true;
                const playResult = video.play();
                if (playResult && typeof playResult.catch === "function") {
                  playResult.catch(() => {});
                }
                started = true;
              } catch (e) {}
            });
            return started;
            """
        )
        return bool(played)
    except Exception:
        return False


def _click_video_controls_in_current_context(driver) -> bool:
    for selector in VIDEO_PLAY_SELECTORS:
        try:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
        except Exception:
            continue
        for element in elements[:10]:
            try:
                if not element.is_displayed():
                    continue
                if _click_element(driver, element):
                    return True
            except Exception:
                continue
    return False


def _click_video_text_targets_in_current_context(driver) -> bool:
    xpath_candidates = [
        "//*[contains(translate(normalize-space(.), 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'view this video also')]",
        "//*[contains(translate(normalize-space(.), 'ABCDEFGHIJKLMNOPQRSTUVWXYZ', 'abcdefghijklmnopqrstuvwxyz'), 'featured video')]",
    ]
    for xpath in xpath_candidates:
        try:
            elements = driver.find_elements(By.XPATH, xpath)
        except Exception:
            continue
        for element in elements[:10]:
            try:
                if not element.is_displayed():
                    continue
                if _click_element(driver, element):
                    time.sleep(0.4)
                    return True
            except Exception:
                continue
    return False


def _click_article_hero_video_in_current_context(driver) -> bool:
    for selector in ARTICLE_HERO_VIDEO_SELECTORS:
        try:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
        except Exception:
            continue
        for element in elements[:8]:
            try:
                if not element.is_displayed():
                    continue
                if _click_element(driver, element):
                    time.sleep(0.5)
                    return True
            except Exception:
                continue
    return False


def _attempt_video_start_in_current_context(driver) -> bool:
    attempted = False
    if _click_article_hero_video_in_current_context(driver):
        attempted = True
        time.sleep(0.6)
    if _play_visible_videos_in_current_context(driver):
        attempted = True
        time.sleep(0.25)
    if _click_video_controls_in_current_context(driver):
        attempted = True
        time.sleep(0.35)
    if _click_video_text_targets_in_current_context(driver):
        attempted = True
        time.sleep(0.35)
    if _click_video_controls_in_current_context(driver):
        attempted = True
        time.sleep(0.35)
    if _play_visible_videos_in_current_context(driver):
        attempted = True
        time.sleep(0.25)
    return attempted


def _attempt_video_start_in_frames(driver, depth: int = 0, max_depth: int = 1) -> bool:
    if depth > max_depth:
        return False
    attempted = False
    try:
        frames = driver.find_elements(By.TAG_NAME, "iframe")
    except Exception:
        return False

    for frame_index, frame in enumerate(frames[:10]):
        try:
            driver.switch_to.default_content()
            frames = driver.find_elements(By.TAG_NAME, "iframe")
            if frame_index >= len(frames):
                continue
            driver.switch_to.frame(frames[frame_index])
            attempted = _attempt_video_start_in_current_context(driver) or attempted
            if depth + 1 <= max_depth:
                attempted = _attempt_video_start_in_frames(driver, depth=depth + 1, max_depth=max_depth) or attempted
        except Exception:
            continue
        finally:
            try:
                driver.switch_to.default_content()
            except Exception:
                pass
    return attempted


def _seek_visible_videos_in_current_context(driver, target_percent: float = 26.0) -> bool:
    try:
        sought = driver.execute_script(
            """
            const targetPercent = Math.max(1, Math.min(99, Number(arguments[0]) || 26));
            const videos = Array.from(document.querySelectorAll("video"));
            let updated = false;
            videos.forEach((video) => {
              const rect = video.getBoundingClientRect();
              if (!rect.width || !rect.height) return;
              const duration = Number(video.duration || 0);
              if (!Number.isFinite(duration) || duration <= 1) return;
              const targetTime = Math.max(0.1, Math.min(duration - 0.25, duration * targetPercent / 100));
              try {
                video.muted = true;
                video.defaultMuted = true;
                video.playsInline = true;
                video.playbackRate = Math.max(Number(video.playbackRate || 1), 8);
              } catch (e) {}
              try {
                const playResult = video.play();
                if (playResult && typeof playResult.catch === "function") {
                  playResult.catch(() => {});
                }
              } catch (e) {}
              try {
                video.currentTime = targetTime;
                ["seeking", "seeked", "timeupdate", "playing"].forEach((eventName) => {
                  try {
                    video.dispatchEvent(new Event(eventName, { bubbles: true }));
                  } catch (e) {}
                });
                updated = true;
              } catch (e) {}
            });
            return updated;
            """,
            target_percent,
        )
        return bool(sought)
    except Exception:
        return False


def _seek_visible_videos_in_frames(driver, target_percent: float = 26.0, depth: int = 0, max_depth: int = 1) -> bool:
    if depth > max_depth:
        return False
    updated = False
    try:
        frames = driver.find_elements(By.TAG_NAME, "iframe")
    except Exception:
        return False

    for frame_index, frame in enumerate(frames[:10]):
        try:
            driver.switch_to.default_content()
            frames = driver.find_elements(By.TAG_NAME, "iframe")
            if frame_index >= len(frames):
                continue
            driver.switch_to.frame(frames[frame_index])
            updated = _seek_visible_videos_in_current_context(driver, target_percent=target_percent) or updated
            if depth + 1 <= max_depth:
                updated = _seek_visible_videos_in_frames(driver, target_percent=target_percent, depth=depth + 1, max_depth=max_depth) or updated
        except Exception:
            continue
        finally:
            try:
                driver.switch_to.default_content()
            except Exception:
                pass
    return updated


def trigger_video_playback(driver) -> bool:
    started = False
    try:
        driver.switch_to.default_content()
    except Exception:
        return False

    # Try the hero media near the top of the article before we scroll past it.
    for percent in (0, 4, 10, 20, 35):
        try:
            driver.execute_script(
                """
                const scrollHeight = Math.max(
                    document.body.scrollHeight || 0,
                    document.documentElement.scrollHeight || 0
                );
                window.scrollTo(0, scrollHeight * arguments[0] / 100);
                """,
                percent,
            )
            time.sleep(0.25)
        except Exception:
            pass
        started = _attempt_video_start_in_current_context(driver) or started
        started = _attempt_video_start_in_frames(driver) or started
    return started


def seek_video_progress(driver, target_percent: float = 26.0) -> bool:
    updated = False
    try:
        driver.switch_to.default_content()
    except Exception:
        return False
    updated = _seek_visible_videos_in_current_context(driver, target_percent=target_percent) or updated
    updated = _seek_visible_videos_in_frames(driver, target_percent=target_percent) or updated
    if updated:
        time.sleep(0.2)
    return updated


def single_audit_requires_video_playback(rules: Optional[List[dict]]) -> bool:
    video_fields = {
        normalize_dimension_name(value) for value in VIDEO_INTERACTION_FIELD_NAMES
    }
    for rule in rules or []:
        rule_scope = str(rule.get("rule_scope") or "").strip().lower()
        field_name = str(rule.get("field_name") or "").strip()
        if not field_name:
            continue
        if rule_scope == "event":
            if canonical_event_name(field_name) == "videointeraction":
                return True
        elif rule_scope == "execution":
            if normalize_dimension_name(field_name) in video_fields:
                return True
    return False


def single_audit_requires_scroll_capture(rules: Optional[List[dict]]) -> bool:
    for rule in rules or []:
        rule_scope = str(rule.get("rule_scope") or "").strip().lower()
        field_name = str(rule.get("field_name") or "").strip()
        if not field_name:
            continue
        if rule_scope == "event" and canonical_event_name(field_name) == "pagescroll":
            return True
        if rule_scope == "execution" and normalize_dimension_name(field_name) == "scrollpercent":
            return True
    return False


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

def audit_single_url(
    driver,
    url: str,
    wait_seconds: int = 8,
    compact: bool = False,
    template_rules: Optional[List[dict]] = None,
    force_video_playback: bool = False,
    force_scroll_capture: bool = False,
) -> Dict[str, Any]:
    print(f"\n🔍 Auditing: {url}")

    audit_start = time.time()
    requires_video_playback = force_video_playback or single_audit_requires_video_playback(template_rules)
    requires_scroll_capture = force_scroll_capture or single_audit_requires_scroll_capture(template_rules)

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
        "chartbeat_present": False,
        "gtm_scripts_sample": "",
        "gtag_scripts_sample": "",
        "ga4_collects_sample": "",
        "ccm_pageviews_sample": "",
        "comscore_hits_sample": "",
        "chartbeat_hits_sample": "",
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
        "chartbeat_hits_json": "",
        "mapping_table": "",
        "audit_duration_seconds": 0.0,
    }

    # HTTP hint
    try:
        resp = requests.get(url, timeout=4)
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

    # Keep a single post-load interaction budget so scroll/playback time does not stack
    # on top of the configured wait.
    interaction_start = time.time()

    # Scroll only when this audit path actually needs interaction-driven signals.
    try:
        if requires_scroll_capture or requires_video_playback:
            scroll_before_taboola(driver, scroll_pause=0.08, max_steps=4)
            scroll_points = (0, 25, 50, 75, 100)
            scroll_pause = 0.35
            for p in scroll_points:
                driver.execute_script(
                    "window.scrollTo(0, document.body.scrollHeight * arguments[0] / 100);",
                    p,
                )
                time.sleep(scroll_pause)
    except Exception:
        pass

    if requires_video_playback:
        try:
            video_started = trigger_video_playback(driver)
        except Exception:
            video_started = False
        if video_started:
            try:
                seek_video_progress(driver, target_percent=26.0)
            except Exception:
                pass
            time.sleep(0.8)
        else:
            time.sleep(0.4)

    remaining_wait = max(0.0, max(1, int(wait_seconds or 8)) - (time.time() - interaction_start))
    if remaining_wait:
        time.sleep(remaining_wait)

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

    # Full dataLayer JSON is useful for the one-URL UI, but too heavy for domain-scale runs.
    if compact:
        compact_datalayer = []
        if pageview_event is not None:
            compact_datalayer.append(pageview_event)
        result["all_datalayer_json"] = safe_json(sanitize_for_json(compact_datalayer))
    else:
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

    preload_state = extract_preload_state(driver)
    gtag_calls = preload_state.get("gtagCalls", []) or []
    gtag_events = normalize_gtag_calls(gtag_calls)
    result["ga4_gtag_calls_json"] = "" if compact else safe_json(gtag_calls)
    result["ga4_events_json"] = safe_json(gtag_events)

    execution_hits, execution_events = normalize_transport_hits(preload_state)
    result["ga4_execution_present"] = bool(execution_hits or execution_events)
    result["ga4_execution_hits_json"] = "" if compact else safe_json(execution_hits)
    result["ga4_execution_events_json"] = safe_json(execution_events)

    # Network hits. Domain-scale compact mode avoids Selenium Wire and uses the preload transport hook.
    page_domain = urlparse(url).netloc
    if compact:
        net_info = categorize_preload_transport_hits(execution_hits, page_domain)
    else:
        net_info = categorize_network_requests(driver, page_domain)

    result["gtm_present"] = net_info["gtm_present"]
    result["gtag_present"] = net_info["gtag_present"]
    result["ga4_collect_present"] = net_info["ga4_collect_present"]
    result["ccm_pageview_present"] = net_info["ccm_pageview_present"]
    result["comscore_present"] = net_info["comscore_present"]
    result["chartbeat_present"] = net_info["chartbeat_present"]

    result["gtm_scripts_sample"] = _format_hits_sample(net_info["gtm_scripts"])
    result["gtag_scripts_sample"] = _format_hits_sample(net_info["gtag_scripts"])
    result["ga4_collects_sample"] = _format_hits_sample(net_info["ga4_collects"])
    result["ccm_pageviews_sample"] = _format_hits_sample(net_info["ccm_pageviews"])
    result["comscore_hits_sample"] = _format_hits_sample(net_info["comscore_hits"])
    result["chartbeat_hits_sample"] = _format_hits_sample(net_info["chartbeat_hits"])

    # GA4 events decoded from actual network requests
    decoded_events: List[dict] = []
    network_hits = [*net_info["ga4_collects"], *net_info["ccm_pageviews"]]
    for hit in network_hits:
        for decoded_event in hit.get("decoded_events", []) or []:
            if isinstance(decoded_event, dict):
                decoded_events.append(decoded_event)

    result["ga4_network_hits_json"] = "" if compact else safe_json(network_hits)
    result["ga4_network_events_json"] = safe_json(decoded_events)
    result["ga4_decoded_events_json"] = safe_json(decoded_events)
    result["comscore_hits_json"] = safe_json(
        build_comscore_capture_rows(net_info["comscore_hits"])
    )
    result["chartbeat_hits_json"] = safe_json(
        build_chartbeat_capture_rows(net_info["chartbeat_hits"])
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
MAPPING_DATE_TIME_REGEX = r"^\d{4}-\d{2}-\d{2}T\d{2}:\d{2}:\d{2}(?:[+-]\d{2}:\d{2}|Z)$"
MAPPING_INTEGER_REGEX = r"^\d+$"
MAPPING_FIELD_ALIASES = {
    "article_type": "article_type",
    "author": "author",
    "category": "category",
    "dynamic_video_embed_type": "dynamic_video_embed_type",
    "event": "event name",
    "event name": "event name",
    "event_name": "event name",
    "language": "Language",
    "online_offline": "online_offline",
    "page_type": "page_type",
    "player_type": "player_type",
    "planned_trending": "planned_trending",
    "position_fold": "position_fold",
    "posted_by": "posted_by",
    "publish_date": "publish_date",
    "registration_status": "registration_status",
    "scroll_percent": "scroll_percent",
    "section_name": "section_name",
    "smart_view_enabled": "smart_view_enabled",
    "story_id": "story_id",
    "sub_category": "sub_category",
    "tags": "tags",
    "tvc_event_name": "tvc_event_name",
    "update_date": "update_date",
    "user id": "User_Id",
    "user_id": "User_Id",
    "user_status": "User_Status",
    "usertype": "usertype",
    "video_orientation": "video_orientation",
    "video_percent": "video_percent",
    "word_count": "word_count",
}
JAGRAN_STARTER_TEMPLATES = [
    {
        "template_name": "Home Page",
        "domain_name": "www.jagran.com",
        "measurement_id": "G-3RLQSM7QQQ",
        "container_id": "GTM-5CTQK3",
        "url_pattern": "https://www.jagran.com",
        "rules": [
            {"rule_scope": "event", "field_name": "page_view", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "event", "field_name": "test_event", "rule_type": "exact", "expected_values": "test_event"},
            {"rule_scope": "execution", "field_name": "Language", "rule_type": "exact", "expected_values": "hindi"},
            {"rule_scope": "execution", "field_name": "page_type", "rule_type": "exact", "expected_values": "homepage"},
            {"rule_scope": "execution", "field_name": "tvc_event_name", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "execution", "field_name": "User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "User_Status", "rule_type": "exact", "expected_values": "guest"},
            {"rule_scope": "execution", "field_name": "tvc_User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "tvc_user_id_staging", "rule_type": "exact", "expected_values": "na"},
        ],
    },
    {
        "template_name": "Jagran Latest News Listing",
        "domain_name": "www.jagran.com",
        "measurement_id": "G-3RLQSM7QQQ",
        "container_id": "GTM-5CTQK3",
        "url_pattern": "https://www.jagran.com/latest-news.html",
        "rules": [
            {"rule_scope": "event", "field_name": "page_view", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "event", "field_name": "test_event", "rule_type": "exact", "expected_values": "test_event"},
            {"rule_scope": "event", "field_name": "initVdo", "rule_type": "exact", "expected_values": "initVdo"},
            {"rule_scope": "event", "field_name": "banner_blocked_size", "rule_type": "exact", "expected_values": "banner_blocked_size"},
            {"rule_scope": "event", "field_name": "t_max", "rule_type": "exact", "expected_values": "t_max"},
            {"rule_scope": "event", "field_name": "vdo_pageview", "rule_type": "exact", "expected_values": "vdo_pageview"},
            {"rule_scope": "event", "field_name": "website_pageview", "rule_type": "exact", "expected_values": "website_pageview"},
            {"rule_scope": "event", "field_name": "began_btf", "rule_type": "exact", "expected_values": "began_btf"},
            {"rule_scope": "event", "field_name": "came_in_view", "rule_type": "exact", "expected_values": "came_in_view"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm", "rule_type": "exact", "expected_values": "adrequest_google_mcm"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm_apac", "rule_type": "exact", "expected_values": "adrequest_google_mcm_apac"},
            {"rule_scope": "event", "field_name": "timing_complete", "rule_type": "exact", "expected_values": "timing_complete"},
            {"rule_scope": "event", "field_name": "autoplay_1th_interaction", "rule_type": "exact", "expected_values": "autoplay_1th_interaction"},
            {"rule_scope": "execution", "field_name": "Language", "rule_type": "exact", "expected_values": "hindi"},
            {"rule_scope": "execution", "field_name": "category", "rule_type": "exact", "expected_values": "latest news"},
            {"rule_scope": "execution", "field_name": "page_type", "rule_type": "exact", "expected_values": "latest news listing page"},
            {"rule_scope": "execution", "field_name": "tvc_event_name", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "execution", "field_name": "User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "User_Status", "rule_type": "exact", "expected_values": "guest"},
            {"rule_scope": "execution", "field_name": "tvc_User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "tvc_user_id_staging", "rule_type": "exact", "expected_values": "na"},
        ],
    },
    {
        "template_name": "Jagran Elections Landing",
        "domain_name": "www.jagran.com",
        "measurement_id": "G-3RLQSM7QQQ",
        "container_id": "GTM-5CTQK3",
        "url_pattern": "https://www.jagran.com/elections.html",
        "rules": [
            {"rule_scope": "event", "field_name": "page_view", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "event", "field_name": "test_event", "rule_type": "exact", "expected_values": "test_event"},
            {"rule_scope": "event", "field_name": "initVdo", "rule_type": "exact", "expected_values": "initVdo"},
            {"rule_scope": "event", "field_name": "banner_blocked_size", "rule_type": "exact", "expected_values": "banner_blocked_size"},
            {"rule_scope": "event", "field_name": "t_max", "rule_type": "exact", "expected_values": "t_max"},
            {"rule_scope": "event", "field_name": "vdo_pageview", "rule_type": "exact", "expected_values": "vdo_pageview"},
            {"rule_scope": "event", "field_name": "website_pageview", "rule_type": "exact", "expected_values": "website_pageview"},
            {"rule_scope": "event", "field_name": "began_atf", "rule_type": "exact", "expected_values": "began_atf"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm", "rule_type": "exact", "expected_values": "adrequest_google_mcm"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm_apac", "rule_type": "exact", "expected_values": "adrequest_google_mcm_apac"},
            {"rule_scope": "event", "field_name": "timing_complete", "rule_type": "exact", "expected_values": "timing_complete"},
            {"rule_scope": "execution", "field_name": "Language", "rule_type": "exact", "expected_values": "hindi"},
            {"rule_scope": "execution", "field_name": "category", "rule_type": "exact", "expected_values": "election"},
            {"rule_scope": "execution", "field_name": "page_type", "rule_type": "exact", "expected_values": "election landing page"},
            {"rule_scope": "execution", "field_name": "tvc_event_name", "rule_type": "exact", "expected_values": "page_view"},
        ],
    },
    {
        "template_name": "Jagran Cricket Landing",
        "domain_name": "www.jagran.com",
        "measurement_id": "G-3RLQSM7QQQ",
        "container_id": "GTM-5CTQK3",
        "url_pattern": "https://www.jagran.com/cricket-hindi.html",
        "rules": [
            {"rule_scope": "event", "field_name": "page_view", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "event", "field_name": "test_event", "rule_type": "exact", "expected_values": "test_event"},
            {"rule_scope": "event", "field_name": "initVdo", "rule_type": "exact", "expected_values": "initVdo"},
            {"rule_scope": "event", "field_name": "banner_blocked_size", "rule_type": "exact", "expected_values": "banner_blocked_size"},
            {"rule_scope": "event", "field_name": "t_max", "rule_type": "exact", "expected_values": "t_max"},
            {"rule_scope": "event", "field_name": "vdo_pageview", "rule_type": "exact", "expected_values": "vdo_pageview"},
            {"rule_scope": "event", "field_name": "website_pageview", "rule_type": "exact", "expected_values": "website_pageview"},
            {"rule_scope": "event", "field_name": "began_atf", "rule_type": "exact", "expected_values": "began_atf"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm", "rule_type": "exact", "expected_values": "adrequest_google_mcm"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm_apac", "rule_type": "exact", "expected_values": "adrequest_google_mcm_apac"},
            {"rule_scope": "event", "field_name": "timing_complete", "rule_type": "exact", "expected_values": "timing_complete"},
            {"rule_scope": "execution", "field_name": "Language", "rule_type": "exact", "expected_values": "hindi"},
            {"rule_scope": "execution", "field_name": "category", "rule_type": "exact", "expected_values": "cricket"},
            {"rule_scope": "execution", "field_name": "page_type", "rule_type": "exact", "expected_values": "cricket landing page"},
            {"rule_scope": "execution", "field_name": "tvc_event_name", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "execution", "field_name": "User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "User_Status", "rule_type": "exact", "expected_values": "guest"},
            {"rule_scope": "execution", "field_name": "tvc_User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "tvc_user_id_staging", "rule_type": "exact", "expected_values": "na"},
        ],
    },
    {
        "template_name": "Jagran Breaking News Listing",
        "domain_name": "www.jagran.com",
        "measurement_id": "G-3RLQSM7QQQ",
        "container_id": "GTM-5CTQK3",
        "url_pattern": "https://www.jagran.com/breaking-news.html",
        "rules": [
            {"rule_scope": "event", "field_name": "page_view", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "event", "field_name": "test_event", "rule_type": "exact", "expected_values": "test_event"},
            {"rule_scope": "event", "field_name": "initVdo", "rule_type": "exact", "expected_values": "initVdo"},
            {"rule_scope": "event", "field_name": "banner_blocked_size", "rule_type": "exact", "expected_values": "banner_blocked_size"},
            {"rule_scope": "event", "field_name": "came_in_view", "rule_type": "exact", "expected_values": "came_in_view"},
            {"rule_scope": "event", "field_name": "t_max", "rule_type": "exact", "expected_values": "t_max"},
            {"rule_scope": "event", "field_name": "vdo_pageview", "rule_type": "exact", "expected_values": "vdo_pageview"},
            {"rule_scope": "event", "field_name": "website_pageview", "rule_type": "exact", "expected_values": "website_pageview"},
            {"rule_scope": "event", "field_name": "began_atf", "rule_type": "exact", "expected_values": "began_atf"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm", "rule_type": "exact", "expected_values": "adrequest_google_mcm"},
            {"rule_scope": "event", "field_name": "adrequest_google_mcm_apac", "rule_type": "exact", "expected_values": "adrequest_google_mcm_apac"},
            {"rule_scope": "event", "field_name": "timing_complete", "rule_type": "exact", "expected_values": "timing_complete"},
            {"rule_scope": "event", "field_name": "autoplay_1th_interaction", "rule_type": "exact", "expected_values": "autoplay_1th_interaction"},
            {"rule_scope": "event", "field_name": "requests_btwn_3_to_4", "rule_type": "exact", "expected_values": "requests_btwn_3_to_4"},
            {"rule_scope": "execution", "field_name": "Language", "rule_type": "exact", "expected_values": "hindi"},
            {"rule_scope": "execution", "field_name": "category", "rule_type": "exact", "expected_values": "breaking news"},
            {"rule_scope": "execution", "field_name": "page_type", "rule_type": "exact", "expected_values": "breaking news listing page"},
            {"rule_scope": "execution", "field_name": "tvc_event_name", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "execution", "field_name": "User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "User_Status", "rule_type": "exact", "expected_values": "guest"},
            {"rule_scope": "execution", "field_name": "tvc_User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "tvc_user_id_staging", "rule_type": "exact", "expected_values": "na"},
        ],
    },
    {
        "template_name": "Jagran Article Detail",
        "domain_name": "www.jagran.com",
        "measurement_id": "G-3RLQSM7QQQ",
        "container_id": "GTM-5CTQK3",
        "url_pattern": "\n".join([
            "https://www.jagran.com/uttar-pradesh/moradabad-city-moradabad-crime-woman-kills-sister-over-live-in-relationship-with-husband-40199730.html",
            "https://www.jagran.com/world/america-us-warns-iran-if-ceasefire-break-means-war-resumes-america-top-general-statement-40199707.html",
            "https://www.jagran.com/lifestyle/health-the-new-cholesterol-rules-what-the-latest-accaha-guidelines-mean-for-your-heart-health-in-2026-40199634.html",
        ]),
        "rules": [
            {"rule_scope": "event", "field_name": "page_view", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "event", "field_name": "page_scroll", "rule_type": "exact", "expected_values": "page_scroll"},
            {"rule_scope": "event", "field_name": "test_event", "rule_type": "exact", "expected_values": "test_event"},
            {"rule_scope": "execution", "field_name": "Language", "rule_type": "exact", "expected_values": "hindi"},
            {"rule_scope": "execution", "field_name": "article_type", "rule_type": "exact", "expected_values": "jagran hindi jnm"},
            {"rule_scope": "execution", "field_name": "dynamic_video_embed_type", "rule_type": "exact", "expected_values": "view this video also"},
            {"rule_scope": "execution", "field_name": "online_offline", "rule_type": "exact", "expected_values": "online"},
            {"rule_scope": "execution", "field_name": "page_type", "rule_type": "exact", "expected_values": "article detail"},
            {"rule_scope": "execution", "field_name": "tvc_event_name", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "execution", "field_name": "author", "rule_type": "required", "expected_values": ""},
            {"rule_scope": "execution", "field_name": "posted_by", "rule_type": "required", "expected_values": ""},
            {"rule_scope": "execution", "field_name": "category", "rule_type": "required", "expected_values": ""},
            {"rule_scope": "execution", "field_name": "tags", "rule_type": "required", "expected_values": ""},
            {"rule_scope": "execution", "field_name": "publish_date", "rule_type": "regex", "expected_values": "^\\\\d{4}-\\\\d{2}-\\\\d{2}T\\\\d{2}:\\\\d{2}:\\\\d{2}(?:[+-]\\\\d{2}:\\\\d{2}|Z)$"},
            {"rule_scope": "execution", "field_name": "update_date", "rule_type": "regex", "expected_values": "^\\\\d{4}-\\\\d{2}-\\\\d{2}T\\\\d{2}:\\\\d{2}:\\\\d{2}(?:[+-]\\\\d{2}:\\\\d{2}|Z)$"},
            {"rule_scope": "execution", "field_name": "story_id", "rule_type": "regex", "expected_values": "^\\\\d+$"},
            {"rule_scope": "execution", "field_name": "word_count", "rule_type": "regex", "expected_values": "^\\\\d+$"},
            {"rule_scope": "execution", "field_name": "planned_trending", "rule_type": "one_of", "expected_values": "regular news|planned"},
            {"rule_scope": "execution", "field_name": "smart_view_enabled", "rule_type": "one_of", "expected_values": "yes|no"},
            {"rule_scope": "execution", "field_name": "sub_category", "rule_type": "optional", "expected_values": ""},
        ],
    },
    {
        "template_name": "Jagran Video Landing",
        "domain_name": "www.jagran.com",
        "measurement_id": "G-3RLQSM7QQQ",
        "container_id": "GTM-5CTQK3",
        "url_pattern": "https://www.jagran.com/videos.html",
        "rules": [
            {"rule_scope": "event", "field_name": "page_view", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "event", "field_name": "test_event", "rule_type": "exact", "expected_values": "test_event"},
            {"rule_scope": "execution", "field_name": "Language", "rule_type": "exact", "expected_values": "hindi"},
            {"rule_scope": "execution", "field_name": "page_type", "rule_type": "exact", "expected_values": "video landing page"},
            {"rule_scope": "execution", "field_name": "tvc_event_name", "rule_type": "exact", "expected_values": "page_view"},
            {"rule_scope": "execution", "field_name": "User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "User_Status", "rule_type": "exact", "expected_values": "guest"},
            {"rule_scope": "execution", "field_name": "tvc_User_Id", "rule_type": "exact", "expected_values": "na"},
            {"rule_scope": "execution", "field_name": "tvc_user_id_staging", "rule_type": "exact", "expected_values": "na"},
        ],
    },
]


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
    return True


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


def update_template_record(email_id: str, template_id: str, template_payload: dict):
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

    template_id_text = str(template_id or "").strip()
    if not template_id_text:
        return False, "Template ID is missing."

    template_ids = template_ws.col_values(1)
    row_index = None
    for index, value in enumerate(template_ids[1:], start=2):
        if str(value or "").strip() == template_id_text:
            row_index = index
            break

    if row_index is None:
        return False, "Template not found."

    existing_row = template_ws.row_values(row_index)
    existing_map = {
        header: (existing_row[idx] if idx < len(existing_row) else "")
        for idx, header in enumerate(TEMPLATE_HEADERS)
    }

    row_map = {
        "template_id": template_id_text,
        "template_name": str(template_payload.get("template_name") or "").strip(),
        "domain_name": str(template_payload.get("domain_name") or "").strip(),
        "measurement_id": str(template_payload.get("measurement_id") or "").strip(),
        "container_id": str(template_payload.get("container_id") or "").strip(),
        "url_pattern": str(template_payload.get("url_pattern") or "").strip(),
        "active": "TRUE" if template_payload.get("active", True) else "FALSE",
        "created_by": existing_map.get("created_by") or email_id,
        "created_at": existing_map.get("created_at") or datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S"),
    }

    last_cell = f"{sheet_column_label(len(TEMPLATE_HEADERS))}{row_index}"
    ordered_row = [row_map.get(header, "") for header in TEMPLATE_HEADERS]
    template_ws.update(
        range_name=f"A{row_index}:{last_cell}",
        values=[ordered_row],
        value_input_option="USER_ENTERED",
    )
    return True, template_id_text


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


def update_template_rule(email_id: str, rule_id: str, rule_payload: dict):
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

    rule_id_text = str(rule_id or "").strip()
    if not rule_id_text:
        return False, "Rule ID is missing."

    rule_ids = rules_ws.col_values(1)
    row_index = None
    for index, value in enumerate(rule_ids[1:], start=2):
        if str(value or "").strip() == rule_id_text:
            row_index = index
            break

    if row_index is None:
        return False, "Rule not found."

    existing_row = rules_ws.row_values(row_index)
    existing_map = {
        header: (existing_row[idx] if idx < len(existing_row) else "")
        for idx, header in enumerate(TEMPLATE_RULE_HEADERS)
    }

    row_map = {
        "rule_id": rule_id_text,
        "template_id": str(rule_payload.get("template_id") or existing_map.get("template_id") or "").strip(),
        "rule_scope": str(rule_payload.get("rule_scope") or existing_map.get("rule_scope") or "").strip(),
        "field_name": str(rule_payload.get("field_name") or "").strip(),
        "rule_type": str(rule_payload.get("rule_type") or "").strip(),
        "expected_values": str(rule_payload.get("expected_values") or "").strip(),
        "notes": str(rule_payload.get("notes") or "").strip(),
        "created_by": existing_map.get("created_by") or email_id,
        "created_at": existing_map.get("created_at") or datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S"),
    }

    last_cell = f"{sheet_column_label(len(TEMPLATE_RULE_HEADERS))}{row_index}"
    ordered_row = [row_map.get(header, "") for header in TEMPLATE_RULE_HEADERS]
    rules_ws.update(
        range_name=f"A{row_index}:{last_cell}",
        values=[ordered_row],
        value_input_option="USER_ENTERED",
    )
    return True, rule_id_text


def delete_template_rule(rule_id: str):
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

    rule_id_text = str(rule_id or "").strip()
    if not rule_id_text:
        return False, "Rule ID is missing."

    rule_ids = rules_ws.col_values(1)
    row_index = None
    for index, value in enumerate(rule_ids[1:], start=2):
        if str(value or "").strip() == rule_id_text:
            row_index = index
            break

    if row_index is None:
        return False, "Rule not found."

    rules_ws.delete_rows(row_index)
    return True, rule_id_text


# -------------------------
# Supabase persistence
# -------------------------

SUPABASE_TEMPLATE_TABLE = "ga_audit_templates"
SUPABASE_TEMPLATE_RULE_TABLE = "ga_audit_template_rules"
SUPABASE_LOG_TABLE = "ga_audit_logs"
SUPABASE_BULK_JOB_TABLE = "bulk_audit_jobs"
SUPABASE_BULK_RESULT_TABLE = "bulk_audit_results"


def get_supabase_settings() -> Dict[str, str]:
    settings = {
        "url": os.environ.get("SUPABASE_URL", "").strip(),
        "key": (
            os.environ.get("SUPABASE_SERVICE_ROLE_KEY")
            or os.environ.get("SUPABASE_ANON_KEY")
            or ""
        ).strip(),
    }
    try:
        raw = st.secrets.get("supabase", {})
    except Exception:
        raw = {}
    if raw:
        raw_settings = dict(raw)
        settings["url"] = settings["url"] or str(raw_settings.get("url") or "").strip()
        settings["key"] = settings["key"] or str(
            raw_settings.get("service_role_key")
            or raw_settings.get("anon_key")
            or raw_settings.get("key")
            or ""
        ).strip()
    settings["url"] = settings["url"].rstrip("/")
    return settings


def supabase_is_configured() -> bool:
    settings = get_supabase_settings()
    return bool(settings["url"] and settings["key"])


def supabase_headers(prefer: str = "") -> Dict[str, str]:
    settings = get_supabase_settings()
    headers = {
        "apikey": settings["key"],
        "Authorization": f"Bearer {settings['key']}",
        "Content-Type": "application/json",
    }
    if prefer:
        headers["Prefer"] = prefer
    return headers


def supabase_request(method: str, table: str, params: Optional[dict] = None, payload: Any = None, prefer: str = ""):
    settings = get_supabase_settings()
    if not settings["url"] or not settings["key"]:
        raise RuntimeError("Supabase is not configured. Add SUPABASE_URL and SUPABASE_SERVICE_ROLE_KEY.")
    url = f"{settings['url']}/rest/v1/{table}"
    response = requests.request(
        method,
        url,
        headers=supabase_headers(prefer=prefer),
        params=params or {},
        json=payload,
        timeout=30,
    )
    if response.status_code >= 400:
        raise RuntimeError(f"Supabase {method} {table} failed: {response.status_code} {response.text}")
    if not response.text:
        return []
    try:
        return response.json()
    except Exception:
        return []


def _supabase_clean_record(record: dict, headers: List[str]) -> dict:
    cleaned = {header: "" for header in headers}
    for key, value in (record or {}).items():
        if key == "active":
            cleaned[key] = _normalize_template_flag(value)
        elif value is None:
            cleaned[str(key)] = ""
        else:
            cleaned[str(key)] = str(value).strip()
    return cleaned


def _template_payload_for_supabase(email_id: str, template_payload: dict, template_id: str = "", existing: Optional[dict] = None) -> dict:
    now_text = datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S")
    existing = existing or {}
    return {
        "template_id": template_id or f"tpl_{uuid.uuid4().hex[:8]}",
        "template_name": str(template_payload.get("template_name") or "").strip(),
        "domain_name": str(template_payload.get("domain_name") or "").strip(),
        "measurement_id": str(template_payload.get("measurement_id") or "").strip(),
        "container_id": str(template_payload.get("container_id") or "").strip(),
        "url_pattern": str(template_payload.get("url_pattern") or "").strip(),
        "active": bool(template_payload.get("active", True)),
        "created_by": str(existing.get("created_by") or email_id or "").strip(),
        "created_at": str(existing.get("created_at") or now_text),
    }


def _rule_payload_for_supabase(email_id: str, rule_payload: dict, rule_id: str = "", existing: Optional[dict] = None) -> dict:
    now_text = datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S")
    existing = existing or {}
    return {
        "rule_id": rule_id or f"rule_{uuid.uuid4().hex[:8]}",
        "template_id": str(rule_payload.get("template_id") or existing.get("template_id") or "").strip(),
        "rule_scope": str(rule_payload.get("rule_scope") or existing.get("rule_scope") or "").strip(),
        "field_name": str(rule_payload.get("field_name") or "").strip(),
        "rule_type": str(rule_payload.get("rule_type") or "").strip(),
        "expected_values": str(rule_payload.get("expected_values") or "").strip(),
        "notes": str(rule_payload.get("notes") or "").strip(),
        "created_by": str(existing.get("created_by") or email_id or "").strip(),
        "created_at": str(existing.get("created_at") or now_text),
    }


def append_audit_log(email_id: str, result: dict, audit_summary: dict):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."

    execution_dimension_map = build_execution_dimension_map(audit_summary)
    execution_dimensions = [
        f"{dimension}={value}"
        for dimension, value in execution_dimension_map.items()
    ]
    payload = {
        "date": datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S"),
        "email_id": email_id,
        "url_checked": result.get("page_url") or "",
        "pageview_trigger_found": bool(audit_summary.get("pageview_triggered")),
        LEGACY_EXECUTION_SUMMARY_HEADER: "\n".join(execution_dimensions) if execution_dimensions else "None",
        "execution_dimensions": execution_dimension_map,
    }
    try:
        supabase_request("POST", SUPABASE_LOG_TABLE, payload=payload, prefer="return=minimal")
        return True, ""
    except Exception as exc:
        return False, str(exc)


def load_templates_and_rules():
    if not supabase_is_configured():
        return [], [], "Supabase is not configured yet. Add `supabase.url` and `supabase.service_role_key` to Streamlit secrets."

    try:
        template_rows = supabase_request(
            "GET",
            SUPABASE_TEMPLATE_TABLE,
            params={"select": "*", "order": "template_name.asc"},
        )
        rule_rows = supabase_request(
            "GET",
            SUPABASE_TEMPLATE_RULE_TABLE,
            params={"select": "*", "order": "field_name.asc"},
        )
    except Exception as exc:
        return [], [], str(exc)

    templates = [_supabase_clean_record(record, TEMPLATE_HEADERS) for record in template_rows]
    rules = [_supabase_clean_record(record, TEMPLATE_RULE_HEADERS) for record in rule_rows]

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


def append_template_record(email_id: str, template_payload: dict):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    row_map = _template_payload_for_supabase(email_id, template_payload)
    try:
        response = supabase_request(
            "POST",
            SUPABASE_TEMPLATE_TABLE,
            payload=row_map,
            prefer="return=representation",
        )
        if isinstance(response, list) and response:
            return True, str(response[0].get("template_id") or row_map["template_id"])
        return True, row_map["template_id"]
    except Exception as exc:
        return False, str(exc)


def update_template_record(email_id: str, template_id: str, template_payload: dict):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    template_id_text = str(template_id or "").strip()
    if not template_id_text:
        return False, "Template ID is missing."
    try:
        existing_rows = supabase_request(
            "GET",
            SUPABASE_TEMPLATE_TABLE,
            params={"select": "*", "template_id": f"eq.{template_id_text}", "limit": "1"},
        )
        existing = existing_rows[0] if isinstance(existing_rows, list) and existing_rows else {}
        row_map = _template_payload_for_supabase(email_id, template_payload, template_id_text, existing)
        supabase_request(
            "PATCH",
            SUPABASE_TEMPLATE_TABLE,
            params={"template_id": f"eq.{template_id_text}"},
            payload=row_map,
            prefer="return=minimal",
        )
        return True, template_id_text
    except Exception as exc:
        return False, str(exc)


def append_template_rule(email_id: str, rule_payload: dict):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    row_map = _rule_payload_for_supabase(email_id, rule_payload)
    try:
        response = supabase_request(
            "POST",
            SUPABASE_TEMPLATE_RULE_TABLE,
            payload=row_map,
            prefer="return=representation",
        )
        if isinstance(response, list) and response:
            return True, str(response[0].get("rule_id") or row_map["rule_id"])
        return True, row_map["rule_id"]
    except Exception as exc:
        return False, str(exc)


def append_template_rules(email_id: str, rule_payloads: List[dict]):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    payloads = [payload for payload in (rule_payloads or []) if isinstance(payload, dict)]
    if not payloads:
        return False, "No rules to save."
    rows = [_rule_payload_for_supabase(email_id, payload) for payload in payloads]
    try:
        supabase_request(
            "POST",
            SUPABASE_TEMPLATE_RULE_TABLE,
            payload=rows,
            prefer="return=minimal",
        )
        return True, str(len(rows))
    except Exception as exc:
        return False, str(exc)


def update_template_rule(email_id: str, rule_id: str, rule_payload: dict):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    rule_id_text = str(rule_id or "").strip()
    if not rule_id_text:
        return False, "Rule ID is missing."
    try:
        existing_rows = supabase_request(
            "GET",
            SUPABASE_TEMPLATE_RULE_TABLE,
            params={"select": "*", "rule_id": f"eq.{rule_id_text}", "limit": "1"},
        )
        existing = existing_rows[0] if isinstance(existing_rows, list) and existing_rows else {}
        row_map = _rule_payload_for_supabase(email_id, rule_payload, rule_id_text, existing)
        supabase_request(
            "PATCH",
            SUPABASE_TEMPLATE_RULE_TABLE,
            params={"rule_id": f"eq.{rule_id_text}"},
            payload=row_map,
            prefer="return=minimal",
        )
        return True, rule_id_text
    except Exception as exc:
        return False, str(exc)


def delete_template_rule(rule_id: str):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    rule_id_text = str(rule_id or "").strip()
    if not rule_id_text:
        return False, "Rule ID is missing."
    try:
        supabase_request(
            "DELETE",
            SUPABASE_TEMPLATE_RULE_TABLE,
            params={"rule_id": f"eq.{rule_id_text}"},
            prefer="return=minimal",
        )
        return True, rule_id_text
    except Exception as exc:
        return False, str(exc)


def reset_templates_to_homepage_only(email_id: str):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."

    homepage_seed = get_homepage_starter_template()
    homepage_template_id = "tpl_home_page"
    timestamp = datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S")

    try:
        supabase_request("DELETE", SUPABASE_TEMPLATE_RULE_TABLE, params={"rule_id": "not.is.null"}, prefer="return=minimal")
        supabase_request("DELETE", SUPABASE_TEMPLATE_TABLE, params={"template_id": "not.is.null"}, prefer="return=minimal")

        template_row = {
            "template_id": homepage_template_id,
            "template_name": homepage_seed.get("template_name"),
            "domain_name": homepage_seed.get("domain_name"),
            "measurement_id": homepage_seed.get("measurement_id"),
            "container_id": homepage_seed.get("container_id"),
            "url_pattern": homepage_seed.get("url_pattern"),
            "active": True,
            "created_by": email_id,
            "created_at": timestamp,
        }
        supabase_request("POST", SUPABASE_TEMPLATE_TABLE, payload=template_row, prefer="return=minimal")

        rule_rows = []
        for index, rule in enumerate(homepage_seed.get("rules", []), start=1):
            rule_rows.append(
                {
                    "rule_id": f"rule_home_page_{index:02d}",
                    "template_id": homepage_template_id,
                    "rule_scope": str(rule.get("rule_scope") or "").strip(),
                    "field_name": str(rule.get("field_name") or "").strip(),
                    "rule_type": str(rule.get("rule_type") or "").strip(),
                    "expected_values": str(rule.get("expected_values") or "").strip(),
                    "notes": str(rule.get("notes") or "").strip(),
                    "created_by": email_id,
                    "created_at": timestamp,
                }
            )
        if rule_rows:
            supabase_request("POST", SUPABASE_TEMPLATE_RULE_TABLE, payload=rule_rows, prefer="return=minimal")
        return True, "Template Manager reset. Only the Home Page template remains."
    except Exception as exc:
        return False, str(exc)


def get_github_settings() -> Dict[str, str]:
    settings = {
        "owner": os.environ.get("GITHUB_OWNER", "").strip(),
        "repo": os.environ.get("GITHUB_REPO", "").strip(),
        "workflow": os.environ.get("GITHUB_WORKFLOW", "bulk-audit.yml").strip() or "bulk-audit.yml",
        "token": os.environ.get("GITHUB_TOKEN", "").strip(),
        "ref": os.environ.get("GITHUB_REF_NAME", "main").strip() or "main",
    }
    try:
        raw = st.secrets.get("github", {})
    except Exception:
        raw = {}
    if raw:
        raw_settings = dict(raw)
        settings["owner"] = settings["owner"] or str(raw_settings.get("owner") or "").strip()
        settings["repo"] = settings["repo"] or str(raw_settings.get("repo") or "").strip()
        settings["workflow"] = str(raw_settings.get("workflow") or settings["workflow"]).strip() or "bulk-audit.yml"
        settings["token"] = settings["token"] or str(raw_settings.get("token") or "").strip()
        settings["ref"] = str(raw_settings.get("ref") or settings["ref"]).strip() or "main"
    return settings


def github_is_configured() -> bool:
    settings = get_github_settings()
    return bool(settings["owner"] and settings["repo"] and settings["workflow"] and settings["token"])


def trigger_bulk_audit_workflow(job_id: str) -> Tuple[bool, str]:
    settings = get_github_settings()
    missing = [key for key in ("owner", "repo", "workflow", "token") if not settings.get(key)]
    if missing:
        return False, f"GitHub trigger is not configured. Missing: {', '.join(missing)}."
    url = (
        f"https://api.github.com/repos/{settings['owner']}/{settings['repo']}"
        f"/actions/workflows/{settings['workflow']}/dispatches"
    )
    response = requests.post(
        url,
        headers={
            "Accept": "application/vnd.github+json",
            "Authorization": f"Bearer {settings['token']}",
            "X-GitHub-Api-Version": "2022-11-28",
        },
        json={"ref": settings["ref"], "inputs": {"job_id": job_id}},
        timeout=30,
    )
    if response.status_code not in {200, 201, 204}:
        return False, f"GitHub workflow trigger failed: {response.status_code} {response.text}"
    return True, "GitHub bulk audit workflow started."


def create_bulk_audit_job(email_id: str, domain_name: str, plan_rows: List[dict], wait_seconds: int) -> Tuple[bool, str]:
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    job_id = f"job_{datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%SZ')}_{uuid.uuid4().hex[:8]}"
    compact_plan = []
    for row in compact_domain_audit_plan(plan_rows):
        template = dict(row.get("template") or {})
        rules = get_rules_for_validation_template(template, template_rules_by_template)
        compact_plan.append(
            {
                **row,
                "domain_name": domain_name,
                "rules": rules,
            }
        )
    payload = {
        "domain_name": domain_name,
        "wait_seconds": int(wait_seconds or 8),
        "plan": compact_plan,
    }
    row = {
        "job_id": job_id,
        "domain_name": domain_name,
        "status": "queued",
        "total_count": len(compact_plan),
        "completed_count": 0,
        "failed_count": 0,
        "requested_by": email_id,
        "payload": payload,
    }
    try:
        supabase_request("POST", SUPABASE_BULK_JOB_TABLE, payload=row, prefer="return=minimal")
        return True, job_id
    except Exception as exc:
        return False, str(exc)


def load_bulk_audit_jobs(domain_name: str = "", limit: int = 10) -> Tuple[List[dict], str]:
    if not supabase_is_configured():
        return [], "Supabase is not configured yet."
    params = {"select": "*", "order": "created_at.desc", "limit": str(limit)}
    if domain_name:
        params["domain_name"] = f"eq.{domain_name}"
    try:
        return supabase_request("GET", SUPABASE_BULK_JOB_TABLE, params=params), ""
    except Exception as exc:
        return [], str(exc)


def cancel_bulk_audit_job(job_id: str) -> Tuple[bool, str]:
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."
    if not str(job_id or "").strip():
        return False, "Job ID is missing."
    try:
        supabase_request(
            "PATCH",
            SUPABASE_BULK_JOB_TABLE,
            params={"job_id": f"eq.{job_id}"},
            payload={
                "status": "cancelled",
                "completed_at": datetime.now(timezone.utc).isoformat(),
            },
            prefer="return=minimal",
        )
        return True, "Bulk audit stop requested."
    except Exception as exc:
        return False, str(exc)


def load_bulk_audit_results(job_id: str) -> Tuple[List[dict], str]:
    if not supabase_is_configured():
        return [], "Supabase is not configured yet."
    if not job_id:
        return [], "Job ID is missing."
    try:
        return supabase_request(
            "GET",
            SUPABASE_BULK_RESULT_TABLE,
            params={"select": "*", "job_id": f"eq.{job_id}", "order": "created_at.asc"},
        ), ""
    except Exception as exc:
        return [], str(exc)


def bulk_result_records_to_report_rows(result_records: List[dict]) -> List[dict]:
    rows = []
    for record in result_records or []:
        result_json = record.get("result_json") or {}
        if isinstance(result_json, str):
            try:
                result_json = json.loads(result_json)
            except Exception:
                result_json = {}
        row = {
            "domain": result_json.get("domain") or "",
            "template_name": record.get("template_name") or result_json.get("template_name") or "",
            "sample_url": record.get("sample_url") or result_json.get("sample_url") or "",
            "audit_outcome": record.get("audit_outcome") or result_json.get("audit_outcome") or "",
            "implementation_status": record.get("implementation_status") or result_json.get("implementation_status") or "",
            "pageview_triggered": bool(record.get("pageview_triggered") or result_json.get("pageview_triggered")),
            "pageview_source": record.get("pageview_source") or result_json.get("pageview_source") or "",
            "ga_present": bool(record.get("ga_present") or result_json.get("ga_present")),
            "events_count": int(record.get("events_count") or result_json.get("events_count") or 0),
            "events_fired": record.get("events_fired") or result_json.get("events_fired") or "",
            "container_id": record.get("container_id") or result_json.get("container_id") or "",
            "measurement_id": record.get("measurement_id") or result_json.get("measurement_id") or "",
            "comscore_present": bool(record.get("comscore_present") or result_json.get("comscore_present")),
            "chartbeat_present": bool(record.get("chartbeat_present") or result_json.get("chartbeat_present")),
            "issues": record.get("issues") or result_json.get("issues") or "",
            "execution_failures": result_json.get("execution_failures") or [],
            "event_failures": result_json.get("event_failures") or [],
            "audit_duration_seconds": result_json.get("audit_duration_seconds") or 0,
            "detail_payload": result_json.get("detail_payload") or {},
        }
        rows.append(row)
    return rows


def _normalize_template_name_key(value: str) -> str:
    return str(value or "").strip().lower()


def get_rules_for_template(template_id: str, rules_by_template: Optional[Dict[str, List[dict]]] = None) -> List[dict]:
    template_id_text = str(template_id or "").strip()
    if not template_id_text:
        return []
    if rules_by_template is not None:
        return list(rules_by_template.get(template_id_text, []))
    return [
        rule
        for rule in template_rules
        if str(rule.get("template_id") or "").strip() == template_id_text
    ]


def get_rules_for_validation_template(
    template: Optional[dict],
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> List[dict]:
    if not template:
        return []
    runtime_rules = template.get("_runtime_rules")
    if isinstance(runtime_rules, list):
        return list(runtime_rules)
    template_id = str(template.get("template_id") or "").strip()
    return get_rules_for_template(template_id, rules_by_template)


VIDEO_INTERACTION_FIELD_NAMES = {
    "player_type",
    "position_fold",
    "section_name",
    "video_orientation",
    "video_percent",
    "video_duration",
    "video_title",
    "scroll_percent",
}


def is_video_related_rule(rule: dict) -> bool:
    rule_scope = str(rule.get("rule_scope") or "").strip().lower()
    field_name = _normalize_template_name_key(rule.get("field_name") or "")
    expected_values = _normalize_template_name_key(rule.get("expected_values") or "")

    if rule_scope == "event" and "video_interaction" in f"{field_name} {expected_values}":
        return True

    if rule_scope == "execution" and field_name in VIDEO_INTERACTION_FIELD_NAMES:
        return True

    return False


def is_video_interaction_template(template: dict, rules_by_template: Optional[Dict[str, List[dict]]] = None) -> bool:
    if template.get("_runtime_companion"):
        return True

    template_name = _normalize_template_name_key(template.get("template_name") or "")
    if "video interaction" in template_name:
        return True

    for rule in get_rules_for_validation_template(template, rules_by_template):
        rule_scope = str(rule.get("rule_scope") or "").strip().lower()
        field_name = _normalize_template_name_key(rule.get("field_name") or "")
        expected_values = _normalize_template_name_key(rule.get("expected_values") or "")
        if rule_scope == "event" and "video_interaction" in f"{field_name} {expected_values}":
            return True
    return False


def template_targets_article_detail_context(
    template: dict,
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> bool:
    template_name = _normalize_template_name_key(template.get("template_name") or "")
    if "article detail" in template_name:
        return True

    for rule in get_rules_for_validation_template(template, rules_by_template):
        rule_scope = str(rule.get("rule_scope") or "").strip().lower()
        field_name = normalize_dimension_name(rule.get("field_name") or "")
        expected_values = _normalize_template_name_key(rule.get("expected_values") or "")
        if rule_scope == "execution" and field_name == "pagetype" and "article detail" in expected_values:
            return True
        if rule_scope == "execution" and field_name == "dynamicvideoembedtype":
            return True
    return False


def is_article_detail_template(template: dict, rules_by_template: Optional[Dict[str, List[dict]]] = None) -> bool:
    template_name = _normalize_template_name_key(template.get("template_name") or "")
    return "article detail" in template_name and "video interaction" not in template_name


def find_companion_templates(
    base_template: dict,
    all_templates: List[dict],
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> List[dict]:
    if not is_article_detail_template(base_template, rules_by_template):
        return []

    base_template_id = str(base_template.get("template_id") or "").strip()
    base_domain = get_template_domain_label(base_template)
    base_measurement_id = str(base_template.get("measurement_id") or "").strip()
    base_container_id = str(base_template.get("container_id") or "").strip()

    companion_templates = []
    for candidate in all_templates or []:
        if not candidate or not candidate.get("active"):
            continue
        candidate_id = str(candidate.get("template_id") or "").strip()
        if not candidate_id or candidate_id == base_template_id:
            continue
        if get_template_domain_label(candidate) != base_domain:
            continue
        candidate_name = _normalize_template_name_key(candidate.get("template_name") or "")
        if not candidate.get("_runtime_companion") and "video interaction" not in candidate_name:
            continue
        if not candidate.get("_runtime_companion") and "article detail" not in candidate_name:
            continue
        if not is_video_interaction_template(candidate, rules_by_template):
            continue
        if not template_targets_article_detail_context(candidate, rules_by_template):
            continue

        candidate_measurement_id = str(candidate.get("measurement_id") or "").strip()
        candidate_container_id = str(candidate.get("container_id") or "").strip()
        measurement_matches = not base_measurement_id or not candidate_measurement_id or base_measurement_id == candidate_measurement_id
        container_matches = not base_container_id or not candidate_container_id or base_container_id == candidate_container_id
        if not (measurement_matches and container_matches):
            continue
        companion_templates.append(candidate)

    return sorted(
        companion_templates,
        key=lambda template: str(template.get("template_name") or "").lower(),
    )


def build_runtime_video_companion_template(
    base_template: dict,
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> Optional[dict]:
    if not is_article_detail_template(base_template, rules_by_template):
        return None

    template_rules_list = get_rules_for_validation_template(base_template, rules_by_template)
    video_rules = [rule for rule in template_rules_list if is_video_related_rule(rule)]
    if not video_rules:
        return None

    template_name = str(base_template.get("template_name") or "Unnamed template").strip()
    companion_template = dict(base_template)
    companion_template["template_id"] = f"{str(base_template.get('template_id') or '').strip()}__video_interaction"
    if "video interaction" not in _normalize_template_name_key(template_name):
        companion_template["template_name"] = f"{template_name} - video interaction"
    else:
        companion_template["template_name"] = template_name
    companion_template["_runtime_rules"] = video_rules
    companion_template["_runtime_companion"] = True
    return companion_template


def build_companion_validation_templates(
    base_template: dict,
    all_templates: List[dict],
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> List[dict]:
    runtime_companion = build_runtime_video_companion_template(base_template, rules_by_template)
    if runtime_companion:
        return [runtime_companion]

    real_companions = find_companion_templates(base_template, all_templates, rules_by_template)
    return real_companions


def get_effective_template_rules(
    template: dict,
    all_templates: Optional[List[dict]] = None,
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> List[dict]:
    template_rules_list = get_rules_for_validation_template(template, rules_by_template)
    if not template_rules_list:
        return []

    if is_article_detail_template(template, rules_by_template):
        return [rule for rule in template_rules_list if not is_video_related_rule(rule)]

    return template_rules_list


def expand_templates_with_companions(
    selected_templates: List[dict],
    all_templates: List[dict],
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> List[dict]:
    expanded_templates = []
    seen_template_ids = set()

    def append_template(template: dict):
        template_id = str(template.get("template_id") or "").strip()
        if not template_id or template_id in seen_template_ids:
            return
        seen_template_ids.add(template_id)
        expanded_templates.append(template)

    for template in selected_templates or []:
        append_template(template)
        for companion_template in build_companion_validation_templates(template, all_templates, rules_by_template):
            append_template(companion_template)

    return expanded_templates


def _normalize_rule_signature(rule_scope: str, field_name: str, rule_type: str, expected_values: str) -> Tuple[str, str, str, str]:
    return (
        str(rule_scope or "").strip().lower(),
        str(field_name or "").strip().lower(),
        str(rule_type or "").strip().lower(),
        str(expected_values or "").strip(),
    )


def _slugify_identifier(value: str, fallback: str = "template") -> str:
    slug = re.sub(r"[^a-z0-9]+", "_", str(value or "").strip().lower()).strip("_")
    return slug or fallback


def _mapping_clean_text(value) -> str:
    if value is None:
        return ""
    try:
        if pd.isna(value):
            return ""
    except Exception:
        pass
    return re.sub(r"\s+", " ", str(value).strip())


def _mapping_field_key(value) -> str:
    return _mapping_clean_text(value).lower().replace(" ", "_")


def _canonical_mapping_field(value) -> str:
    text = _mapping_clean_text(value)
    if not text:
        return ""
    return MAPPING_FIELD_ALIASES.get(text.lower()) or MAPPING_FIELD_ALIASES.get(_mapping_field_key(text), "")


def _normalize_mapping_expected_value(value: str) -> str:
    text = _mapping_clean_text(value)
    text = re.sub(r"^\(?\s*", "", text)
    text = re.sub(r"\s*\)?$", "", text)
    text = re.sub(r"^static\s*[-:]\s*", "", text, flags=re.IGNORECASE)
    return _mapping_clean_text(text)


def _extract_mapping_allowed_values(structure: str, sample_value: str) -> List[str]:
    structure_text = _mapping_clean_text(structure)
    lower_text = structure_text.lower()
    values: List[str] = []

    percent_values = re.findall(r"\b\d+(?:\.\d+)?%", structure_text)
    if percent_values:
        values.extend(percent_values)
        sample = _normalize_mapping_expected_value(sample_value)
        if sample and re.fullmatch(r"\d+(?:\.\d+)?", sample):
            values.append(f"{sample}%")

    if "yes/no" in lower_text:
        values.extend(["yes", "no"])

    if "logged_in" in lower_text or "guest" in lower_text:
        if "logged_in" in lower_text:
            values.append("logged_in")
        if "guest" in lower_text:
            values.append("guest")
        sample = _normalize_mapping_expected_value(sample_value)
        if sample.lower() in {"logged_in", "guest"}:
            values.append(sample)

    bracket_match = re.search(r"\(([^)]+)\)", structure_text)
    if bracket_match:
        inner_text = bracket_match.group(1)
        for token in re.split(r"[/,|&-]", inner_text):
            token = _normalize_mapping_expected_value(token)
            if token and token.lower() not in {"dynamic", "static"}:
                values.append(token)

    has_dynamic_choices = bool(
        percent_values
        or bracket_match
        or "yes/no" in lower_text
        or "logged_in" in lower_text
        or "guest" in lower_text
    )
    if ("dynamic" in lower_text or "dynamci" in lower_text) and has_dynamic_choices:
        sample = _normalize_mapping_expected_value(sample_value)
        if sample and sample.lower() not in {"dynamic", "static", "not available", "na"}:
            values.append(sample)

    seen = set()
    unique_values = []
    for value in values:
        key = value.lower()
        if key in seen:
            continue
        seen.add(key)
        unique_values.append(value)
    return unique_values


def _infer_mapping_rule(field_name: str, sample_value: str, structure: str, page_type: str) -> dict:
    field = _mapping_clean_text(field_name)
    sample = _normalize_mapping_expected_value(sample_value)
    expected_structure = _mapping_clean_text(structure)
    structure_lower = expected_structure.lower()

    if field == "event name":
        event_name = sample or expected_structure or "page_view"
        return {
            "rule_scope": "event",
            "field_name": event_name,
            "rule_type": "exact",
            "expected_values": event_name,
            "notes": "Imported from GA mapping Excel.",
        }

    if field == "page_type":
        expected_page_type = _mapping_clean_text(page_type) or sample or expected_structure
        return {
            "rule_scope": "execution",
            "field_name": "page_type",
            "rule_type": "exact",
            "expected_values": expected_page_type,
            "notes": f"Imported from GA mapping Excel. Sample: {sample or '-'}",
        }

    if field in {"publish_date", "update_date"} or "yyyy-mm-dd" in structure_lower:
        return {
            "rule_scope": "execution",
            "field_name": field,
            "rule_type": "regex",
            "expected_values": MAPPING_DATE_TIME_REGEX,
            "notes": f"Imported from GA mapping Excel. Expected format: {expected_structure or 'ISO datetime'}",
        }

    if field in {"story_id", "word_count"}:
        return {
            "rule_scope": "execution",
            "field_name": field,
            "rule_type": "regex",
            "expected_values": MAPPING_INTEGER_REGEX,
            "notes": f"Imported from GA mapping Excel. Numeric dynamic value. Sample: {sample or '-'}",
        }

    allowed_values = _extract_mapping_allowed_values(expected_structure, sample)
    if allowed_values:
        return {
            "rule_scope": "execution",
            "field_name": field,
            "rule_type": "one_of",
            "expected_values": "|".join(allowed_values),
            "notes": f"Imported from GA mapping Excel. Allowed by format: {expected_structure}",
        }

    if structure_lower == "static":
        return {
            "rule_scope": "execution",
            "field_name": field,
            "rule_type": "exact",
            "expected_values": sample,
            "notes": "Imported from GA mapping Excel. Static value.",
        }

    if structure_lower == "dynamic" or structure_lower.startswith("dynamic"):
        return {
            "rule_scope": "execution",
            "field_name": field,
            "rule_type": "required",
            "expected_values": "",
            "notes": f"Imported from GA mapping Excel. Dynamic value. Sample: {sample or '-'}",
        }

    if expected_structure:
        return {
            "rule_scope": "execution",
            "field_name": field,
            "rule_type": "exact",
            "expected_values": expected_structure,
            "notes": f"Imported from GA mapping Excel. Sample: {sample or '-'}",
        }

    return {
        "rule_scope": "execution",
        "field_name": field,
        "rule_type": "required",
        "expected_values": "",
        "notes": f"Imported from GA mapping Excel. Sample: {sample or '-'}",
    }


def _extract_mapping_page_type_from_row(row: List[Any]) -> str:
    column = 3
    while column < len(row):
        field_name = _canonical_mapping_field(row[column])
        if field_name == "page_type":
            sample_value = _mapping_clean_text(row[column + 1] if column + 1 < len(row) else "")
            expected_value = _mapping_clean_text(row[column + 2] if column + 2 < len(row) else "")
            return sample_value or expected_value
        column += 1
    return ""


def _split_mapping_event_names(value: str) -> List[str]:
    text = _mapping_clean_text(value)
    if not text:
        return []
    names = []
    for token in re.split(r"[,|\n]", text):
        cleaned = _normalize_mapping_expected_value(token)
        if cleaned and cleaned.lower() not in {"dynamic", "static", "not available", "na"}:
            names.append(cleaned)
    return names


def _looks_like_mapping_event_label(value: str) -> bool:
    text = _mapping_clean_text(value).lower()
    if not text:
        return False
    if text in {"detail", "listing", "landing", "lisitng/landing", "listing/landing"}:
        return False
    return text in {"video_interaction"} or text.startswith("page_") or text.endswith("_pv")


def _event_rule_from_mapping_name(event_name: str) -> dict:
    event_name = _mapping_clean_text(event_name)
    return {
        "rule_scope": "event",
        "field_name": event_name,
        "rule_type": "exact",
        "expected_values": event_name,
        "notes": "Imported from GA mapping Excel.",
    }


def _merge_mapping_rule(existing_rule: Optional[dict], incoming_rule: dict, page_type: str) -> dict:
    if not existing_rule:
        return incoming_rule

    field_name = str(existing_rule.get("field_name") or incoming_rule.get("field_name") or "").strip()
    if field_name == "page_type":
        existing_rule["rule_type"] = "exact"
        existing_rule["expected_values"] = _mapping_clean_text(page_type)
        return existing_rule

    existing_type = str(existing_rule.get("rule_type") or "").strip()
    incoming_type = str(incoming_rule.get("rule_type") or "").strip()
    existing_values = parse_expected_values(existing_rule.get("expected_values"))
    incoming_values = parse_expected_values(incoming_rule.get("expected_values"))

    if existing_type == incoming_type and existing_values == incoming_values:
        return existing_rule

    if existing_type in {"required", "optional", "regex"} or incoming_type in {"required", "optional", "regex"}:
        if existing_type == incoming_type == "regex" and existing_values == incoming_values:
            return existing_rule
        existing_rule["rule_type"] = "required"
        existing_rule["expected_values"] = ""
        existing_rule["notes"] = "Imported from GA mapping Excel. Multiple examples differ, so any non-empty value is accepted."
        return existing_rule

    combined_values = []
    for value in [*existing_values, *incoming_values]:
        cleaned = _normalize_mapping_expected_value(value)
        if cleaned and cleaned.lower() not in {item.lower() for item in combined_values}:
            combined_values.append(cleaned)

    existing_rule["rule_type"] = "one_of" if len(combined_values) > 1 else "exact"
    existing_rule["expected_values"] = "|".join(combined_values)
    existing_rule["notes"] = "Imported from GA mapping Excel. Multiple static examples were merged."
    return existing_rule


def _infer_mapping_url_patterns(page_type: str, urls: List[str]) -> str:
    page_type_lower = str(page_type or "").strip().lower()
    cleaned_urls = []
    for url in urls or []:
        url_text = _mapping_clean_text(url)
        if url_text and url_text not in cleaned_urls:
            cleaned_urls.append(url_text)

    inferred_patterns = []
    if page_type_lower == "article detail":
        inferred_patterns.extend([
            "https://www.jagran.com/*/*-*.html",
            "https://www.jagran.com/smart-choice/*/*",
        ])
    elif page_type_lower == "live blog detail":
        inferred_patterns.append("https://www.jagran.com/*/*-lb-*.html")
    elif page_type_lower == "short video detail":
        inferred_patterns.append("https://www.jagran.com/short-videos/*")
    elif page_type_lower == "photo detail":
        inferred_patterns.append("https://www.jagran.com/photo-stories/*")
    elif page_type_lower == "topic listing page":
        inferred_patterns.append("https://www.jagran.com/topics/*")

    all_patterns = []
    for pattern in [*inferred_patterns, *cleaned_urls]:
        if pattern and pattern not in all_patterns:
            all_patterns.append(pattern)
    return "\n".join(all_patterns)


def parse_ga_mapping_excel_templates(
    excel_bytes: bytes,
    default_domain: str,
    default_measurement_id: str,
    default_container_id: str,
) -> Tuple[List[dict], List[str]]:
    workbook = pd.ExcelFile(io.BytesIO(excel_bytes))
    if "Finalized" not in workbook.sheet_names:
        return [], ["The workbook must contain a sheet named 'Finalized'."]

    sheet = pd.read_excel(
        io.BytesIO(excel_bytes),
        sheet_name="Finalized",
        dtype=str,
        header=None,
        keep_default_na=False,
    )

    templates_by_key: Dict[str, dict] = {}
    notes: List[str] = []
    current_section = ""

    for row_index in range(2, len(sheet)):
        row = sheet.iloc[row_index].tolist()
        section = _mapping_clean_text(row[0] if len(row) > 0 else "")
        if section and not _looks_like_mapping_event_label(section):
            current_section = section

        page_type = _mapping_clean_text(row[1] if len(row) > 1 else "")
        if not page_type:
            page_type = _extract_mapping_page_type_from_row(row)
        if not page_type:
            continue

        page_location_raw = "" if len(row) <= 2 else str(row[2] or "")
        page_locations = [
            _mapping_clean_text(url)
            for url in re.split(r"[\r\n]+", page_location_raw)
            if _mapping_clean_text(url)
        ]
        template_key = page_type.lower()
        template = templates_by_key.setdefault(
            template_key,
            {
                "template_name": page_type,
                "domain_name": _mapping_clean_text(default_domain),
                "measurement_id": _mapping_clean_text(default_measurement_id),
                "container_id": _mapping_clean_text(default_container_id),
                "url_examples": [],
                "rules_by_key": {},
                "section": current_section,
            },
        )
        for page_location in page_locations:
            if page_location and page_location not in template["url_examples"]:
                template["url_examples"].append(page_location)

        rules_by_key = template["rules_by_key"]
        event_rule = {
            "rule_scope": "event",
            "field_name": "page_view",
            "rule_type": "exact",
            "expected_values": "page_view",
            "notes": "Added by importer because every GA4 audit template should validate page_view.",
        }
        rules_by_key[("event", "page_view")] = _merge_mapping_rule(
            rules_by_key.get(("event", "page_view")),
            event_rule,
            page_type,
        )
        if _looks_like_mapping_event_label(section):
            for event_name in _split_mapping_event_names(section):
                event_rule = _event_rule_from_mapping_name(event_name)
                event_key = ("event", event_name.lower())
                rules_by_key[event_key] = _merge_mapping_rule(
                    rules_by_key.get(event_key),
                    event_rule,
                    page_type,
                )

        seen_fields_in_row = set()
        column = 3
        while column < len(row):
            field_name = _canonical_mapping_field(row[column])
            if not field_name:
                column += 1
                continue

            next_column = column + 1
            sample_value = ""
            expected_structure = ""
            if next_column < len(row) and not _canonical_mapping_field(row[next_column]):
                sample_value = _mapping_clean_text(row[next_column])
                next_column += 1
            if next_column < len(row) and not _canonical_mapping_field(row[next_column]):
                expected_structure = _mapping_clean_text(row[next_column])
                next_column += 1

            if (
                field_name == "page_type"
                and field_name in seen_fields_in_row
                and _mapping_clean_text(sample_value).lower() != page_type.lower()
            ):
                notes.append(
                    f"Stopped reading row {row_index + 1} after a conflicting duplicate page_type value."
                )
                break

            seen_fields_in_row.add(field_name)
            rule = _infer_mapping_rule(field_name, sample_value, expected_structure, page_type)
            rule_key = (
                str(rule.get("rule_scope") or "").strip().lower(),
                str(rule.get("field_name") or "").strip().lower(),
            )
            rules_by_key[rule_key] = _merge_mapping_rule(rules_by_key.get(rule_key), rule, page_type)
            if field_name == "tvc_event_name":
                for event_name in _split_mapping_event_names(sample_value or expected_structure):
                    event_rule = _event_rule_from_mapping_name(event_name)
                    event_key = ("event", event_name.lower())
                    rules_by_key[event_key] = _merge_mapping_rule(
                        rules_by_key.get(event_key),
                        event_rule,
                        page_type,
                    )
            column = max(next_column, column + 1)

    imported_templates = []
    for template in templates_by_key.values():
        imported_templates.append(
            {
                "template_name": template["template_name"],
                "domain_name": template["domain_name"],
                "measurement_id": template["measurement_id"],
                "container_id": template["container_id"],
                "url_pattern": _infer_mapping_url_patterns(
                    template["template_name"],
                    template.get("url_examples") or [],
                ),
                "rules": list(template["rules_by_key"].values()),
            }
        )

    imported_templates.sort(key=lambda item: str(item.get("template_name") or "").lower())
    return imported_templates, notes


def add_templates_from_seed_templates(
    email_id: str,
    template_seeds: List[dict],
    template_records: List[dict],
    template_rules: List[dict],
    source_label: str,
):
    seeds = [seed for seed in (template_seeds or []) if isinstance(seed, dict)]
    if not seeds:
        return False, "No templates were found to import."

    existing_templates_by_name = {
        _normalize_template_name_key(template.get("template_name")): template
        for template in (template_records or [])
        if str(template.get("template_name") or "").strip()
    }
    rules_by_template: Dict[str, Set[Tuple[str, str, str, str]]] = {}
    for rule in template_rules or []:
        template_id = str(rule.get("template_id") or "").strip()
        if not template_id:
            continue
        rules_by_template.setdefault(template_id, set()).add(
            _normalize_rule_signature(
                rule.get("rule_scope"),
                rule.get("field_name"),
                rule.get("rule_type"),
                rule.get("expected_values"),
            )
        )

    created_templates = 0
    updated_templates = 0
    rules_to_add = []

    for seed in seeds:
        template_name_key = _normalize_template_name_key(seed.get("template_name"))
        existing_template = existing_templates_by_name.get(template_name_key)
        template_payload = {
            "template_name": str(seed.get("template_name") or "").strip(),
            "domain_name": str(seed.get("domain_name") or "").strip(),
            "measurement_id": str(seed.get("measurement_id") or "").strip(),
            "container_id": str(seed.get("container_id") or "").strip(),
            "url_pattern": str(seed.get("url_pattern") or "").strip(),
            "active": True,
        }

        if existing_template:
            success, response = update_template_record(
                email_id,
                existing_template.get("template_id"),
                template_payload,
            )
            if not success:
                return False, response
            template_id = str(existing_template.get("template_id") or "").strip()
            updated_templates += 1
        else:
            success, response = append_template_record(email_id, template_payload)
            if not success:
                return False, response
            template_id = str(response or "").strip()
            existing_templates_by_name[template_name_key] = {
                **template_payload,
                "template_id": template_id,
                "active": True,
            }
            created_templates += 1

        existing_signatures = rules_by_template.setdefault(template_id, set())
        for rule in seed.get("rules") or []:
            signature = _normalize_rule_signature(
                rule.get("rule_scope"),
                rule.get("field_name"),
                rule.get("rule_type"),
                rule.get("expected_values"),
            )
            if signature in existing_signatures:
                continue
            rules_to_add.append(
                {
                    "template_id": template_id,
                    "rule_scope": str(rule.get("rule_scope") or "").strip(),
                    "field_name": str(rule.get("field_name") or "").strip(),
                    "rule_type": str(rule.get("rule_type") or "").strip(),
                    "expected_values": str(rule.get("expected_values") or "").strip(),
                    "notes": str(rule.get("notes") or "").strip(),
                }
            )
            existing_signatures.add(signature)

    if rules_to_add:
        success, response = append_template_rules(email_id, rules_to_add)
        if not success:
            return False, response

    return True, (
        f"{source_label}: added {created_templates} template(s), "
        f"updated {updated_templates}, added {len(rules_to_add)} rule(s)."
    )


def get_homepage_starter_template() -> dict:
    for seed in JAGRAN_STARTER_TEMPLATES:
        if _normalize_template_name_key(seed.get("template_name")) in {"home page", "jagran homepage"}:
            return seed
    return JAGRAN_STARTER_TEMPLATES[0]


def import_jagran_starter_templates(email_id: str, template_records: List[dict], template_rules: List[dict]):
    existing_templates_by_name = {
        _normalize_template_name_key(template.get("template_name")): template
        for template in (template_records or [])
        if str(template.get("template_name") or "").strip()
    }
    rules_by_template: Dict[str, Set[Tuple[str, str, str, str]]] = {}
    for rule in template_rules or []:
        template_id = str(rule.get("template_id") or "").strip()
        if not template_id:
            continue
        rules_by_template.setdefault(template_id, set()).add(
            _normalize_rule_signature(
                rule.get("rule_scope"),
                rule.get("field_name"),
                rule.get("rule_type"),
                rule.get("expected_values"),
            )
        )

    created_templates = 0
    updated_templates = 0
    added_rules = 0

    for seed in [get_homepage_starter_template()]:
        template_name_key = _normalize_template_name_key(seed.get("template_name"))
        existing_template = existing_templates_by_name.get(template_name_key)

        template_payload = {
            "template_name": seed.get("template_name"),
            "domain_name": seed.get("domain_name"),
            "measurement_id": seed.get("measurement_id"),
            "container_id": seed.get("container_id"),
            "url_pattern": seed.get("url_pattern"),
            "active": True,
        }

        if existing_template:
            success, response = update_template_record(
                email_id,
                existing_template.get("template_id"),
                template_payload,
            )
            if not success:
                return False, response
            template_id = str(existing_template.get("template_id") or "").strip()
            updated_templates += 1
        else:
            success, response = append_template_record(email_id, template_payload)
            if not success:
                return False, response
            template_id = str(response or "").strip()
            created_templates += 1
            existing_templates_by_name[template_name_key] = {
                **template_payload,
                "template_id": template_id,
                "active": True,
            }

        existing_signatures = rules_by_template.setdefault(template_id, set())
        payloads_to_add = []
        for rule in seed.get("rules", []):
            signature = _normalize_rule_signature(
                rule.get("rule_scope"),
                rule.get("field_name"),
                rule.get("rule_type"),
                rule.get("expected_values"),
            )
            if signature in existing_signatures:
                continue
            payloads_to_add.append(
                {
                    "template_id": template_id,
                    "rule_scope": rule.get("rule_scope"),
                    "field_name": rule.get("field_name"),
                    "rule_type": rule.get("rule_type"),
                    "expected_values": rule.get("expected_values"),
                    "notes": rule.get("notes") or "",
                }
            )
            existing_signatures.add(signature)

        if payloads_to_add:
            success, response = append_template_rules(email_id, payloads_to_add)
            if not success:
                return False, response
            added_rules += len(payloads_to_add)

    return True, (
        f"Homepage template synced. "
        f"Created {created_templates}, updated {updated_templates}, added {added_rules} rule(s)."
    )


def reset_templates_to_homepage_only(email_id: str):
    service_account_info = get_service_account_info()
    if not service_account_info:
        return False, "Google Sheets logging is not configured yet."

    settings = get_template_sheet_settings()
    template_ws, rules_ws = get_template_worksheets(
        json.dumps(service_account_info),
        settings["spreadsheet_id"],
        settings["template_worksheet_name"],
        settings["template_rules_worksheet_name"],
    )

    homepage_seed = get_homepage_starter_template()
    homepage_template_id = "tpl_home_page"
    timestamp = datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S")

    template_ws.clear()
    rules_ws.clear()
    ensure_fixed_headers(template_ws, TEMPLATE_HEADERS)
    ensure_fixed_headers(rules_ws, TEMPLATE_RULE_HEADERS)

    template_row = {
        "template_id": homepage_template_id,
        "template_name": homepage_seed.get("template_name"),
        "domain_name": homepage_seed.get("domain_name"),
        "measurement_id": homepage_seed.get("measurement_id"),
        "container_id": homepage_seed.get("container_id"),
        "url_pattern": homepage_seed.get("url_pattern"),
        "active": "TRUE",
        "created_by": email_id,
        "created_at": timestamp,
    }
    template_ws.append_row(
        [template_row.get(header, "") for header in TEMPLATE_HEADERS],
        value_input_option="USER_ENTERED",
    )

    rule_rows = []
    for index, rule in enumerate(homepage_seed.get("rules", []), start=1):
        row_map = {
            "rule_id": f"rule_home_page_{index:02d}",
            "template_id": homepage_template_id,
            "rule_scope": str(rule.get("rule_scope") or "").strip(),
            "field_name": str(rule.get("field_name") or "").strip(),
            "rule_type": str(rule.get("rule_type") or "").strip(),
            "expected_values": str(rule.get("expected_values") or "").strip(),
            "notes": str(rule.get("notes") or "").strip(),
            "created_by": email_id,
            "created_at": timestamp,
        }
        rule_rows.append([row_map.get(header, "") for header in TEMPLATE_RULE_HEADERS])

    if rule_rows:
        rules_ws.append_rows(rule_rows, value_input_option="USER_ENTERED")

    return True, "Template Manager reset. Only the Home Page template remains."


def should_auto_cleanup_homepage_templates(template_records: List[dict]) -> bool:
    starter_template_names = {
        _normalize_template_name_key(seed.get("template_name"))
        for seed in JAGRAN_STARTER_TEMPLATES[1:]
    }
    homepage_names = {"home page", "jagran homepage"}
    names = [
        _normalize_template_name_key(template.get("template_name"))
        for template in (template_records or [])
        if str(template.get("template_name") or "").strip()
    ]
    has_old_starter_templates = any(name in starter_template_names for name in names)
    has_duplicate_homepage_templates = sum(1 for name in names if name in homepage_names) > 1
    return has_old_starter_templates or has_duplicate_homepage_templates


def reset_templates_to_homepage_only(email_id: str):
    if not supabase_is_configured():
        return False, "Supabase is not configured yet."

    homepage_seed = get_homepage_starter_template()
    homepage_template_id = "tpl_home_page"
    timestamp = datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S")

    try:
        supabase_request("DELETE", SUPABASE_TEMPLATE_RULE_TABLE, params={"rule_id": "not.is.null"}, prefer="return=minimal")
        supabase_request("DELETE", SUPABASE_TEMPLATE_TABLE, params={"template_id": "not.is.null"}, prefer="return=minimal")

        template_row = {
            "template_id": homepage_template_id,
            "template_name": homepage_seed.get("template_name"),
            "domain_name": homepage_seed.get("domain_name"),
            "measurement_id": homepage_seed.get("measurement_id"),
            "container_id": homepage_seed.get("container_id"),
            "url_pattern": homepage_seed.get("url_pattern"),
            "active": True,
            "created_by": email_id,
            "created_at": timestamp,
        }
        supabase_request("POST", SUPABASE_TEMPLATE_TABLE, payload=template_row, prefer="return=minimal")

        rule_rows = []
        for index, rule in enumerate(homepage_seed.get("rules", []), start=1):
            rule_rows.append(
                {
                    "rule_id": f"rule_home_page_{index:02d}",
                    "template_id": homepage_template_id,
                    "rule_scope": str(rule.get("rule_scope") or "").strip(),
                    "field_name": str(rule.get("field_name") or "").strip(),
                    "rule_type": str(rule.get("rule_type") or "").strip(),
                    "expected_values": str(rule.get("expected_values") or "").strip(),
                    "notes": str(rule.get("notes") or "").strip(),
                    "created_by": email_id,
                    "created_at": timestamp,
                }
            )
        if rule_rows:
            supabase_request("POST", SUPABASE_TEMPLATE_RULE_TABLE, payload=rule_rows, prefer="return=minimal")
        return True, "Template Manager reset. Only the Home Page template remains."
    except Exception as exc:
        return False, str(exc)


def render_sidebar_session(email_id: str):
    with st.sidebar:
        st.markdown("### Session")
        st.write(email_id)
        if st.button("Log out"):
            st.session_state.pop("logged_in_email", None)
            clear_login_cookie()
            st.rerun()

        st.markdown("### Storage")
        if supabase_is_configured():
            st.success("Supabase configured")
        else:
            st.warning("Supabase not configured")
            st.caption("Add `supabase.url` and `supabase.service_role_key` to Streamlit secrets.")


logged_in_email = require_login()
render_sidebar_session(logged_in_email)

template_records, template_rules, template_load_error = load_templates_and_rules()
active_templates = [
    template
    for template in template_records
    if template.get("active")
]
template_rules_by_template = {}
for template_rule in template_rules:
    template_rules_by_template.setdefault(
        str(template_rule.get("template_id") or "").strip(),
        [],
    ).append(template_rule)

tab_labels = ["Audit URLs", "Domain Audit", "Compare Prod vs Stage"]
if is_template_admin(logged_in_email):
    tab_labels.append("Template Manager")

tabs = st.tabs(tab_labels)
tab_main = tabs[0]
tab_domain_audit = tabs[1]
tab_compare = tabs[2]
tab_template_manager = tabs[3] if len(tabs) > 3 else None


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
        "chartbeat_hits_json",
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
            "chartbeat_present": result.get("chartbeat_present"),
            "chartbeat_values": audit_summary["chartbeat_preview"],
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


def canonical_event_name(value) -> str:
    text = normalize_event_name(value)
    if text.startswith("tvc"):
        stripped = text[3:]
        if stripped.startswith("videointeraction") or stripped.startswith("pageview") or stripped.startswith("pagescroll"):
            return stripped
    return text


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


def parse_regex_patterns(raw_value: str) -> List[str]:
    text = str(raw_value or "").strip()
    if not text:
        return []
    return [part.strip() for part in re.split(r"[\n\r]+", text) if part.strip()]


def normalize_expected_values_input(raw_value: str) -> str:
    return "|".join(parse_expected_values(raw_value))


def format_expected_values_display(raw_value: str) -> str:
    values = parse_expected_values(raw_value)
    if not values:
        return ""
    return ", ".join(values)


def normalize_multiline_entries(raw_value: str) -> str:
    entries = [line.strip() for line in str(raw_value or "").splitlines() if line.strip()]
    return "\n".join(entries)


def format_multiline_entries_display(raw_value: str) -> str:
    entries = [line.strip() for line in str(raw_value or "").splitlines() if line.strip()]
    if not entries:
        return ""
    return " | ".join(entries)


def normalize_rule_expected_values_input(rule_type: str, raw_value: str) -> str:
    normalized_rule_type = str(rule_type or "").strip().lower()
    if normalized_rule_type in {"required", "optional"}:
        return ""
    if normalized_rule_type == "regex":
        return normalize_multiline_entries(raw_value)
    return normalize_expected_values_input(raw_value)


def format_rule_expected_values_display(rule_type: str, raw_value: str) -> str:
    normalized_rule_type = str(rule_type or "").strip().lower()
    if normalized_rule_type == "regex":
        return format_multiline_entries_display(raw_value)
    return format_expected_values_display(raw_value)


def editable_rule_expected_values_text(rule_type: str, raw_value: str) -> str:
    normalized_rule_type = str(rule_type or "").strip().lower()
    if normalized_rule_type == "regex":
        return normalize_multiline_entries(raw_value)
    return "\n".join(parse_expected_values(raw_value))


def unique_preserve_order(values: List[str]) -> List[str]:
    seen = set()
    ordered = []
    for value in values or []:
        text = str(value or "").strip()
        if not text or text in seen:
            continue
        seen.add(text)
        ordered.append(text)
    return ordered


def merge_expected_value_inputs(saved_values: List[str], typed_values: str) -> str:
    merged = unique_preserve_order([*(saved_values or []), *parse_expected_values(typed_values)])
    return "|".join(merged)


def merge_rule_expected_value_inputs(rule_type: str, saved_values: List[str], typed_values: str) -> str:
    normalized_rule_type = str(rule_type or "").strip().lower()
    if normalized_rule_type in {"required", "optional"}:
        return ""
    if normalized_rule_type == "regex":
        return normalize_multiline_entries(typed_values)
    return merge_expected_value_inputs(saved_values, typed_values)


def build_execution_rule_catalog(template_rules: List[dict]):
    field_names = []
    value_catalog = {}

    for rule in template_rules or []:
        if str(rule.get("rule_scope") or "").strip().lower() != "execution":
            continue

        field_name = str(rule.get("field_name") or "").strip()
        if not field_name:
            continue
        if field_name not in field_names:
            field_names.append(field_name)

        rule_type = str(rule.get("rule_type") or "").strip().lower()
        if rule_type in {"required", "optional", "regex"}:
            continue

        entry = value_catalog.setdefault(field_name, [])
        for value in parse_expected_values(rule.get("expected_values")):
            if value not in entry:
                entry.append(value)

    return sorted(field_names, key=str.lower), value_catalog


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
        matched = False
        for pattern in parse_regex_patterns(expected_values_text):
            try:
                if re.search(pattern, actual_text):
                    matched = True
                    break
            except re.error:
                continue
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


def build_execution_validation_rows(
    snapshot: dict,
    template_rules: List[dict],
    *,
    include_unmatched_fields: bool = True,
):
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

    if include_unmatched_fields:
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
        canonical_event_name(row.get("event_name")): row
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
        configured_event_names = parse_expected_values(rule.get("field_name"))
        configured_values = parse_expected_values(rule.get("expected_values"))
        if not configured_event_names:
            configured_event_names = configured_values[:]
        if not configured_event_names:
            continue

        matched_names = []
        for configured in configured_event_names:
            configured_norm = canonical_event_name(configured)
            if configured_norm in observed_by_name:
                matched_names.append(configured_norm)

        matched = bool(matched_names)
        expected_text = str(rule.get("expected_values") or "").strip() or " | ".join(configured_event_names)

        if matched and configured_values:
            configured_event_norms = {canonical_event_name(value) for value in configured_event_names}
            expected_value_norms = {canonical_event_name(value) for value in configured_values}
            validate_payload_values = bool(expected_value_norms - configured_event_norms)

            if validate_payload_values:
                payload_text_parts = []
                for event_name in matched_names:
                    matched_row = observed_by_name.get(event_name) or {}
                    payload_text_parts.append(str(matched_row.get("key_values_seen") or ""))
                    for detail in (matched_row.get("details") or []):
                        payload_text_parts.append(str(detail.get("Field") or ""))
                        payload_text_parts.append(str(detail.get("Value") or ""))
                    for detail in (matched_row.get("technical_details") or []):
                        payload_text_parts.append(str(detail.get("Field") or ""))
                        payload_text_parts.append(str(detail.get("Value") or ""))
                payload_text = " | ".join(part for part in payload_text_parts if part).lower()
                matched = all(str(value).strip().lower() in payload_text for value in configured_values if str(value).strip())

        validation_label = VALIDATION_PASS_LABEL if matched else (
            VALIDATION_OPTIONAL_LABEL if str(rule.get("rule_type") or "").strip().lower() == "optional" else VALIDATION_FAIL_LABEL
        )

        if matched_names:
            for event_name in matched_names:
                handled_event_names.add(event_name)
                for row in display_rows:
                    if canonical_event_name(row.get("event_name")) != event_name:
                        continue
                    row["expected"] = expected_text
                    row["validation"] = validation_label
        else:
            display_rows.append(
                {
                    "event_name": " | ".join(configured_event_names),
                    "status": "Expected but not fired",
                    "times_fired": 0,
                    "capture_layer": "Not observed",
                    "key_values_seen": "",
                    "details": [],
                    "technical_details": [],
                    "expected": expected_text,
                    "validation": validation_label,
                }
            )

    return pd.DataFrame(display_rows)


DOMAIN_AUDIT_TEMPLATE_LIMIT = 3
DOMAIN_AUDIT_BATCH_DEFAULT = 1


def get_template_domain_label(template: dict) -> str:
    return str(template.get("domain_name") or "").strip() or "Unspecified domain"


def split_template_reference_patterns(raw_value: str) -> List[str]:
    pieces: List[str] = []
    for line in str(raw_value or "").splitlines():
        for part in line.split("|"):
            text = part.strip()
            if text:
                pieces.append(text)
    return pieces


def _pattern_to_candidate_url(pattern: str) -> str:
    text = str(pattern or "").strip()
    if not text:
        return ""
    text = re.sub(r"\s+", "", text)
    text = text.replace("*", "")
    text = text.replace("\\", "")
    text = re.sub(r"[\[\]\(\)\{\}\^\$]+", "", text)
    if not text:
        return ""
    if text.endswith("."):
        text = text[:-1]
    return text


def choose_template_sample_url(template: dict) -> Tuple[str, str]:
    patterns = split_template_reference_patterns(template.get("url_pattern") or "")
    exact_candidates = [pattern for pattern in patterns if "*" not in pattern and not re.search(r"[\[\]\(\)\{\}\^\$]", pattern)]
    fallback_candidates = [pattern for pattern in patterns if pattern not in exact_candidates]

    for pattern in [*exact_candidates, *fallback_candidates]:
        candidate = _pattern_to_candidate_url(pattern)
        if not candidate:
            continue
        _, normalized_url, input_error = normalize_single_url(candidate)
        if not input_error:
            return normalized_url, ""

    return "", "No usable reference URL/pattern found for this template."


def template_reference_matches_url(template: Optional[dict], normalized_url: str) -> bool:
    if not template:
        return False
    url_text = str(normalized_url or "").strip().lower()
    if not url_text:
        return False

    patterns = split_template_reference_patterns(template.get("url_pattern") or "")
    if not patterns:
        return True

    for pattern in patterns:
        raw_pattern = str(pattern or "").strip()
        if not raw_pattern:
            continue
        _, normalized_pattern, pattern_error = normalize_single_url(raw_pattern)
        candidate_pattern = normalized_pattern if not pattern_error else raw_pattern.strip()
        candidate_pattern = candidate_pattern.lower()
        if not candidate_pattern:
            continue

        has_wildcard = "*" in candidate_pattern
        has_regex = bool(re.search(r"[\[\]\(\)\{\}\^\$]", candidate_pattern))

        if has_wildcard:
            wildcard_regex = "^" + re.escape(candidate_pattern).replace("\\*", ".*") + "$"
            if re.match(wildcard_regex, url_text):
                return True
            continue

        if has_regex:
            try:
                if re.search(candidate_pattern, url_text):
                    return True
            except re.error:
                pass
            cleaned_pattern = _pattern_to_candidate_url(candidate_pattern).lower()
            if cleaned_pattern and cleaned_pattern in url_text:
                return True
            continue

        if candidate_pattern == url_text:
            return True

    return False


def template_search_blob(template: dict) -> str:
    return " ".join(
        [
            str(template.get("template_name") or ""),
            get_template_domain_label(template),
            str(template.get("measurement_id") or ""),
            str(template.get("container_id") or ""),
            str(template.get("url_pattern") or ""),
        ]
    ).lower()


def pick_first_matching_template(templates: List[dict], terms: List[str], used_ids: Set[str]) -> Optional[dict]:
    for template in templates:
        template_id = str(template.get("template_id") or "").strip()
        if template_id in used_ids:
            continue
        blob = template_search_blob(template)
        if any(term in blob for term in terms):
            return template
    return None


def select_domain_audit_templates(domain_templates: List[dict], limit: int = DOMAIN_AUDIT_TEMPLATE_LIMIT) -> List[dict]:
    sorted_templates = sorted(
        domain_templates or [],
        key=lambda template: str(template.get("template_name") or "").lower(),
    )
    selected: List[dict] = []
    used_ids: Set[str] = set()

    for terms in (
        ["home page", "homepage", "home"],
        ["article detail", "article"],
        ["listing", "landing"],
    ):
        match = pick_first_matching_template(sorted_templates, terms, used_ids)
        if match:
            selected.append(match)
            used_ids.add(str(match.get("template_id") or "").strip())
        if len(selected) >= limit:
            return selected[:limit]

    for template in sorted_templates:
        template_id = str(template.get("template_id") or "").strip()
        if template_id in used_ids:
            continue
        selected.append(template)
        used_ids.add(template_id)
        if len(selected) >= limit:
            break

    return selected[:limit]


def build_domain_audit_plan(domain_templates: List[dict], limit: int = DOMAIN_AUDIT_TEMPLATE_LIMIT) -> List[dict]:
    plan_rows = []
    for template in select_domain_audit_templates(domain_templates, limit=limit):
        sample_url, sample_error = choose_template_sample_url(template)
        plan_rows.append(
            {
                "template": template,
                "template_id": str(template.get("template_id") or "").strip(),
                "template_name": str(template.get("template_name") or "Unnamed template"),
                "sample_url": sample_url,
                "sample_error": sample_error,
            }
        )
    return plan_rows


def build_domain_audit_plan_from_templates(
    domain_templates: List[dict],
    override_urls: Optional[Dict[str, str]] = None,
    all_templates: Optional[List[dict]] = None,
    rules_by_template: Optional[Dict[str, List[dict]]] = None,
) -> List[dict]:
    plan_rows = []
    override_urls = override_urls or {}
    seen_template_ids = set()

    def append_plan_row(
        plan_template: dict,
        sample_url: str,
        sample_error: str,
        override_raw: str,
        parent_template_id: str = "",
    ):
        template_id = str(plan_template.get("template_id") or "").strip()
        if not template_id or template_id in seen_template_ids:
            return
        seen_template_ids.add(template_id)
        plan_rows.append(
            {
                "template": plan_template,
                "template_id": template_id,
                "template_name": str(plan_template.get("template_name") or "Unnamed template"),
                "sample_url": sample_url,
                "sample_error": sample_error,
                "override_url": override_raw,
                "parent_template_id": parent_template_id,
                "is_companion_template": bool(parent_template_id),
            }
        )

    for template in sorted(
        domain_templates or [],
        key=lambda item: str(item.get("template_name") or "").lower(),
    ):
        template_id = str(template.get("template_id") or "").strip()
        override_raw = str(override_urls.get(template_id) or "").strip()
        if override_raw:
            _, sample_url, sample_error = normalize_single_url(override_raw)
        else:
            sample_url, sample_error = choose_template_sample_url(template)
        append_plan_row(template, sample_url, sample_error, override_raw)

        for companion_template in build_companion_validation_templates(template, all_templates or [], rules_by_template):
            append_plan_row(
                companion_template,
                sample_url,
                sample_error,
                override_raw,
                parent_template_id=template_id,
            )
    return plan_rows


def compact_domain_audit_plan(plan_rows: List[dict]) -> List[dict]:
    compact_rows = []
    for row in plan_rows or []:
        compact_rows.append(
            {
                "template": row.get("template") or {},
                "template_id": row.get("template_id") or "",
                "template_name": row.get("template_name") or "Unnamed template",
                "sample_url": row.get("sample_url") or "",
                "sample_error": row.get("sample_error") or "",
            }
        )
    return compact_rows


def summarize_validation_failures(
    result: dict,
    template: dict,
    selected_template_rules: List[dict],
) -> Dict[str, Any]:
    audit_summary = build_audit_focus_summary(result)
    snapshot = build_datalayer_snapshot_export(result)
    _, execution_validation_rows = build_execution_validation_rows(snapshot, selected_template_rules)
    event_df = build_event_validation_rows(audit_summary["event_rows"], selected_template_rules)

    execution_failures = []
    for row in execution_validation_rows:
        if row.get("validation") != VALIDATION_FAIL_LABEL:
            continue
        execution_failures.append(
            f"{row.get('field_name')}: expected {row.get('expected') or 'configured rule'}, got {row.get('actual_value')}"
        )

    event_failures = []
    if isinstance(event_df, pd.DataFrame) and not event_df.empty and "validation" in event_df.columns:
        for _, event_row in event_df.iterrows():
            if event_row.get("validation") != VALIDATION_FAIL_LABEL:
                continue
            expected = event_row.get("expected") or event_row.get("event_name") or "configured event"
            status = event_row.get("status") or "not observed"
            event_failures.append(f"{expected}: {status}")

    issue_parts = []
    if str(result.get("issues") or "").strip():
        issue_parts.append(str(result.get("issues")).strip())
    if not audit_summary["pageview_triggered"]:
        issue_parts.append("page_view was not triggered")
    if execution_failures:
        issue_parts.append(f"{len(execution_failures)} execution validation mismatch(es)")
    if event_failures:
        issue_parts.append(f"{len(event_failures)} event validation mismatch(es)")

    return {
        "pageview_triggered": audit_summary["pageview_triggered"],
        "pageview_source": audit_summary["pageview_source"],
        "container_id": audit_summary["container_id"],
        "measurement_id": audit_summary["measurement_id"],
        "events_fired": audit_summary["events_fired"],
        "events_count": len(audit_summary["events_fired"]),
        "comscore_present": audit_summary["comscore_present"],
        "chartbeat_present": audit_summary["chartbeat_present"],
        "execution_failures": execution_failures,
        "event_failures": event_failures,
        "issues": " | ".join(issue_parts),
        "audit_outcome": "Issue" if issue_parts else "Pass",
        "implementation_status": result.get("status") or "",
        "audit_duration_seconds": result.get("audit_duration_seconds") or 0,
        "template_name": template.get("template_name") or "Unnamed template",
        "template_id": template.get("template_id") or "",
    }


def dataframe_report_records(dataframe: pd.DataFrame, columns: Optional[List[str]] = None, limit: int = 40) -> List[dict]:
    if not isinstance(dataframe, pd.DataFrame) or dataframe.empty:
        return []

    frame = dataframe.copy()
    if columns:
        existing_columns = [column for column in columns if column in frame.columns]
        frame = frame[existing_columns] if existing_columns else frame
    frame = frame.head(limit)
    records = []
    for record in frame.fillna("").to_dict("records"):
        records.append({str(key): format_exact_value(value) for key, value in record.items()})
    return records


def build_domain_audit_detail_payload(result: dict, selected_template_rules: List[dict]) -> Dict[str, Any]:
    audit_summary = build_audit_focus_summary(result)
    snapshot = build_datalayer_snapshot_export(result)

    if selected_template_rules:
        execution_display_df, _ = build_execution_validation_rows(snapshot, selected_template_rules)
    else:
        execution_display_df = snapshot["execution_df"]
        if execution_display_df.empty and not snapshot["network_df"].empty:
            execution_display_df = snapshot["network_df"]

    event_df = (
        build_event_validation_rows(audit_summary["event_rows"], selected_template_rules)
        if selected_template_rules
        else pd.DataFrame(audit_summary["event_rows"])
    )
    event_display_columns = ["event_name", "status", "times_fired", "capture_layer"]
    if isinstance(event_df, pd.DataFrame) and not event_df.empty:
        if "expected" in event_df.columns:
            event_display_columns.append("expected")
        if "validation" in event_df.columns:
            event_display_columns.append("validation")

    comscore_df = pd.DataFrame(audit_summary.get("comscore_rows") or [])
    if not comscore_df.empty:
        comscore_columns = [
            column
            for column in ["hit_type", "times_fired", "status_chain", "c1", "c2", "c7", "c8"]
            if column in comscore_df.columns
        ]
    else:
        comscore_columns = []

    chartbeat_rows = audit_summary.get("chartbeat_rows") or []
    total_chartbeat_fires = sum(
        int(row.get("times_fired") or 0)
        for row in chartbeat_rows
        if isinstance(row, dict)
    )
    if audit_summary["chartbeat_present"] and total_chartbeat_fires <= 0:
        total_chartbeat_fires = 1
    chartbeat_df = pd.DataFrame(
        [
            {
                "Check": "Chartbeat ping",
                "Fired": "Yes" if audit_summary["chartbeat_present"] else "No",
                "Times Fired": total_chartbeat_fires,
            }
        ]
    )

    return {
        "trigger_rows": dataframe_report_records(snapshot["trigger_df"], ["Field", "Value"]),
        "computed_rows": dataframe_report_records(snapshot["computed_df"], ["Field", "Value"]),
        "execution_rows": dataframe_report_records(
            execution_display_df,
            ["Field", "Value", "Expected", "Validation"],
        ),
        "event_rows": dataframe_report_records(event_df, event_display_columns),
        "comscore_rows": dataframe_report_records(comscore_df, comscore_columns),
        "chartbeat_rows": dataframe_report_records(chartbeat_df),
        "selected_datalayer_index": snapshot.get("selected_index"),
    }


def build_domain_audit_report_row(
    domain_name: str,
    template: dict,
    sample_url: str,
    result: Optional[dict] = None,
    error_message: str = "",
    include_detail: bool = True,
) -> Dict[str, Any]:
    if not result:
        return {
            "domain": domain_name,
            "template_name": template.get("template_name") or "Unnamed template",
            "sample_url": sample_url,
            "audit_outcome": "Issue",
            "implementation_status": "ERROR",
            "pageview_triggered": False,
            "pageview_source": "Not tested",
            "ga_present": False,
            "events_count": 0,
            "events_fired": "",
            "container_id": "Not found",
            "measurement_id": "Not found",
            "comscore_present": False,
            "chartbeat_present": False,
            "issues": error_message or "Audit did not complete.",
            "execution_failures": [],
            "event_failures": [],
            "audit_duration_seconds": 0,
            "detail_payload": {},
        }

    selected_template_rules = get_effective_template_rules(
        template,
        active_templates,
        template_rules_by_template,
    )
    validation_summary = summarize_validation_failures(result, template, selected_template_rules)
    detail_payload = (
        build_domain_audit_detail_payload(result, selected_template_rules)
        if include_detail
        else {}
    )
    ga_present = bool(
        result.get("ga4_collect_present")
        or result.get("ccm_pageview_present")
        or result.get("ga4_execution_present")
        or validation_summary["pageview_triggered"]
    )
    return {
        "domain": domain_name,
        "template_name": validation_summary["template_name"],
        "sample_url": sample_url,
        "audit_outcome": validation_summary["audit_outcome"],
        "implementation_status": validation_summary["implementation_status"],
        "pageview_triggered": validation_summary["pageview_triggered"],
        "pageview_source": validation_summary["pageview_source"],
        "ga_present": ga_present,
        "events_count": validation_summary["events_count"],
        "events_fired": ", ".join(validation_summary["events_fired"]) or "None",
        "container_id": validation_summary["container_id"],
        "measurement_id": validation_summary["measurement_id"],
        "comscore_present": validation_summary["comscore_present"],
        "chartbeat_present": validation_summary["chartbeat_present"],
        "issues": validation_summary["issues"],
        "execution_failures": validation_summary["execution_failures"],
        "event_failures": validation_summary["event_failures"],
        "audit_duration_seconds": validation_summary["audit_duration_seconds"],
        "detail_payload": detail_payload,
    }


def _short_report_text(value: Any, limit: int = 240) -> str:
    text = str(value or "").strip()
    if len(text) <= limit:
        return text
    return f"{text[:limit - 3]}..."


def build_domain_audit_pdf(domain_name: str, report_rows: List[dict]) -> bytes:
    import html
    from reportlab.lib import colors
    from reportlab.lib.pagesizes import A4, landscape
    from reportlab.lib.styles import ParagraphStyle, getSampleStyleSheet
    from reportlab.pdfbase import pdfmetrics
    from reportlab.pdfbase.ttfonts import TTFont
    from reportlab.platypus import PageBreak, SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle

    def resolve_pdf_fonts() -> Tuple[str, str]:
        regular_candidates = [
            "/usr/share/fonts/truetype/noto/NotoSansDevanagari-Regular.ttf",
            "/usr/share/fonts/opentype/noto/NotoSansDevanagari-Regular.ttf",
            "/usr/share/fonts/truetype/noto/NotoSansDevanagariUI-Regular.ttf",
            "/usr/share/fonts/truetype/lohit-devanagari/Lohit-Devanagari.ttf",
            "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
        ]
        bold_candidates = [
            "/usr/share/fonts/truetype/noto/NotoSansDevanagari-Bold.ttf",
            "/usr/share/fonts/opentype/noto/NotoSansDevanagari-Bold.ttf",
            "/usr/share/fonts/truetype/noto/NotoSansDevanagariUI-Bold.ttf",
            "/usr/share/fonts/truetype/dejavu/DejaVuSans-Bold.ttf",
        ]

        regular_font = "Helvetica"
        bold_font = "Helvetica-Bold"
        for font_path in regular_candidates:
            if not os.path.exists(font_path):
                continue
            try:
                pdfmetrics.registerFont(TTFont("GAAuditUnicode", font_path))
                regular_font = "GAAuditUnicode"
                bold_font = regular_font
                break
            except Exception:
                continue

        for font_path in bold_candidates:
            if not os.path.exists(font_path):
                continue
            try:
                pdfmetrics.registerFont(TTFont("GAAuditUnicodeBold", font_path))
                bold_font = "GAAuditUnicodeBold"
                break
            except Exception:
                continue

        return regular_font, bold_font

    buffer = io.BytesIO()
    doc = SimpleDocTemplate(
        buffer,
        pagesize=landscape(A4),
        rightMargin=24,
        leftMargin=24,
        topMargin=24,
        bottomMargin=24,
    )
    styles = getSampleStyleSheet()
    pdf_font_name, pdf_bold_font_name = resolve_pdf_fonts()
    title_style = ParagraphStyle(
        "DomainAuditTitle",
        parent=styles["Title"],
        fontName=pdf_bold_font_name,
        fontSize=18,
        leading=22,
        alignment=0,
        textColor=colors.HexColor("#111827"),
    )
    heading_style = ParagraphStyle(
        "DomainAuditHeading",
        parent=styles["Heading2"],
        fontName=pdf_bold_font_name,
        fontSize=12,
        leading=15,
        textColor=colors.HexColor("#111827"),
        spaceBefore=8,
        spaceAfter=6,
    )
    subheading_style = ParagraphStyle(
        "DomainAuditSubheading",
        parent=styles["Heading3"],
        fontName=pdf_bold_font_name,
        fontSize=10,
        leading=12,
        textColor=colors.HexColor("#111827"),
        spaceBefore=6,
        spaceAfter=4,
    )
    body_style = ParagraphStyle(
        "DomainAuditBody",
        parent=styles["BodyText"],
        fontName=pdf_font_name,
        fontSize=8,
        leading=10,
        wordWrap="CJK",
    )
    small_style = ParagraphStyle(
        "DomainAuditSmall",
        parent=styles["BodyText"],
        fontName=pdf_font_name,
        fontSize=7,
        leading=8,
        wordWrap="CJK",
    )

    def p(value: Any, limit: int = 320):
        return Paragraph(html.escape(_short_report_text(value, limit)), small_style)

    def build_table_flowable(headers: List[str], rows: List[List[Any]], widths: List[int], repeat_rows: int = 1):
        if not rows:
            rows = [["No values captured." if index == 0 else "" for index, _ in enumerate(headers)]]
        table_data = [[Paragraph(html.escape(header), body_style) for header in headers]]
        for row in rows:
            table_data.append([p(cell) for cell in row])
        table = Table(table_data, colWidths=widths, repeatRows=repeat_rows)
        table.setStyle(
            TableStyle(
                [
                    ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#e5e7eb")),
                    ("TEXTCOLOR", (0, 0), (-1, 0), colors.HexColor("#111827")),
                    ("GRID", (0, 0), (-1, -1), 0.35, colors.HexColor("#9ca3af")),
                    ("VALIGN", (0, 0), (-1, -1), "TOP"),
                    ("FONTNAME", (0, 0), (-1, 0), pdf_bold_font_name),
                    ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, colors.HexColor("#f9fafb")]),
                ]
            )
        )
        return table

    def add_table(elements: List[Any], headers: List[str], rows: List[List[Any]], widths: List[int]):
        elements.append(build_table_flowable(headers, rows, widths))

    def add_records_table(
        elements: List[Any],
        title: str,
        records: List[dict],
        column_labels: List[str],
        column_keys: List[str],
        widths: List[int],
    ):
        elements.append(Paragraph(title, subheading_style))
        rows = [
            [record.get(key, "") for key in column_keys]
            for record in records
        ]
        add_table(elements, column_labels, rows, widths)

    def add_snapshot_sections(elements: List[Any], detail_payload: Dict[str, Any]):
        trigger_records = detail_payload.get("trigger_rows") or []
        computed_records = detail_payload.get("computed_rows") or []
        execution_records = detail_payload.get("execution_rows") or []
        section_heading_style = ParagraphStyle(
            "DomainAuditSectionHeading",
            parent=styles["Heading3"],
            fontName=pdf_bold_font_name,
            fontSize=10,
            leading=12,
            textColor=colors.HexColor("#111827"),
            spaceAfter=4,
        )
        elements.append(Paragraph("Trigger Event", section_heading_style))
        elements.append(
            build_table_flowable(
                ["Field", "Value"],
                [[row.get("Field", ""), row.get("Value", "")] for row in trigger_records],
                [120, 575],
            )
        )
        elements.append(Spacer(1, 8))

        elements.append(Paragraph("Computed State", section_heading_style))
        elements.append(
            build_table_flowable(
                ["Field", "Value"],
                [[row.get("Field", ""), row.get("Value", "")] for row in computed_records],
                [120, 575],
            )
        )
        elements.append(Spacer(1, 8))

        elements.append(Paragraph("Execution Payload", section_heading_style))
        elements.append(
            build_table_flowable(
                ["Field", "Value", "Expected", "Validation"],
                [
                    [
                        row.get("Field", ""),
                        row.get("Value", ""),
                        row.get("Expected", ""),
                        row.get("Validation", ""),
                    ]
                    for row in execution_records
                ],
                [110, 310, 180, 95],
            )
        )

    generated_at = datetime.now(LOG_TIMEZONE).strftime("%Y-%m-%d %H:%M:%S %Z")
    issue_rows = [row for row in report_rows if row.get("audit_outcome") == "Issue"]
    passed_rows = [row for row in report_rows if row.get("audit_outcome") != "Issue"]

    elements: List[Any] = [
        Paragraph(f"GA4 Domain Audit Report: {html.escape(str(domain_name or 'Unknown domain'))}", title_style),
        Paragraph(
            html.escape(
                f"Generated {generated_at}. Tested {len(report_rows)} template URL(s): "
                f"{len(issue_rows)} with issue(s), {len(passed_rows)} passed."
            ),
            body_style,
        ),
        Spacer(1, 12),
        Paragraph("URLs Needing Attention", heading_style),
    ]

    if issue_rows:
        add_table(
            elements,
            ["Template", "URL", "GA Fired", "Comscore", "Chartbeat", "Issues"],
            [
                [
                    row.get("template_name"),
                    row.get("sample_url"),
                    "Yes" if row.get("ga_present") else "No",
                    "Yes" if row.get("comscore_present") else "No",
                    "Yes" if row.get("chartbeat_present") else "No",
                    row.get("issues") or "Issue observed",
                ]
                for row in issue_rows
            ],
            [120, 245, 55, 60, 60, 240],
        )
    else:
        elements.append(Paragraph("No issues were detected in this run.", body_style))

    elements.extend([Spacer(1, 14), Paragraph("Bulk Run Overview", heading_style)])
    add_table(
        elements,
        ["Template", "URL", "Outcome", "GA Fired", "Pageview", "Events", "GA IDs", "Comscore", "Chartbeat", "Issues"],
        [
            [
                row.get("template_name"),
                row.get("sample_url"),
                row.get("audit_outcome"),
                "Yes" if row.get("ga_present") else "No",
                f"{'Yes' if row.get('pageview_triggered') else 'No'} ({row.get('pageview_source')})",
                f"{row.get('events_count')} - {row.get('events_fired')}",
                f"{row.get('measurement_id')} / {row.get('container_id')}",
                "Yes" if row.get("comscore_present") else "No",
                "Yes" if row.get("chartbeat_present") else "No",
                row.get("issues") or "None",
            ]
            for row in report_rows
        ],
        [80, 155, 45, 45, 60, 85, 85, 45, 45, 140],
    )

    detailed_rows = []
    for row in report_rows:
        for failure in row.get("execution_failures") or []:
            detailed_rows.append([row.get("template_name"), row.get("sample_url"), "Execution", failure])
        for failure in row.get("event_failures") or []:
            detailed_rows.append([row.get("template_name"), row.get("sample_url"), "Event", failure])

    if detailed_rows:
        elements.extend([Spacer(1, 14), Paragraph("Validation Failure Details", heading_style)])
        add_table(
            elements,
            ["Template", "URL", "Layer", "Failure"],
            detailed_rows,
            [130, 260, 80, 310],
        )

    for index, row in enumerate(report_rows, start=1):
        elements.append(PageBreak())
        elements.append(Paragraph(f"URL Audit Detail {index}: {html.escape(str(row.get('template_name') or 'Template'))}", heading_style))
        elements.append(Paragraph(html.escape(str(row.get("sample_url") or "")), body_style))
        elements.append(Spacer(1, 6))
        if row.get("issues"):
            elements.append(Paragraph("Issues", subheading_style))
            elements.append(Paragraph(html.escape(str(row.get("issues") or "")), body_style))
            elements.append(Spacer(1, 6))
        add_table(
            elements,
            ["Outcome", "GA Fired", "Pageview", "Events", "Measurement ID", "Container ID", "Comscore", "Chartbeat"],
            [
                [
                    row.get("audit_outcome"),
                    "Yes" if row.get("ga_present") else "No",
                    f"{'Yes' if row.get('pageview_triggered') else 'No'} ({row.get('pageview_source')})",
                    f"{row.get('events_count')} - {row.get('events_fired')}",
                    row.get("measurement_id"),
                    row.get("container_id"),
                    "Yes" if row.get("comscore_present") else "No",
                    "Yes" if row.get("chartbeat_present") else "No",
                ]
            ],
            [70, 55, 90, 170, 105, 90, 65, 65],
        )

        detail_payload = row.get("detail_payload") or {}
        if not detail_payload:
            elements.append(Paragraph("Detailed dataLayer snapshot was skipped for this bulk run to keep Streamlit memory within limits.", body_style))
            continue

        selected_index = detail_payload.get("selected_datalayer_index")
        if selected_index not in (None, ""):
            elements.append(Paragraph(f"Selected dataLayer index: {html.escape(str(selected_index))}", body_style))

        elements.append(Spacer(1, 8))
        elements.append(Paragraph("DataLayer Snapshot", heading_style))
        elements.append(
            Paragraph(
                "Primary audit view. This mirrors the in-app audit sections for Trigger Event, Computed State, and Execution Payload.",
                body_style,
            )
        )
        add_snapshot_sections(elements, detail_payload)

        elements.append(Spacer(1, 8))
        elements.append(Paragraph("Events", heading_style))
        add_records_table(
            elements,
            "GA4 Events",
            detail_payload.get("event_rows") or [],
            ["Event", "Status", "Times Fired", "Seen In", "Expected", "Validation"],
            ["event_name", "status", "times_fired", "capture_layer", "expected", "validation"],
            [150, 120, 60, 90, 240, 80],
        )

        elements.append(Spacer(1, 8))
        elements.append(Paragraph("Third-party Tag Checks", heading_style))
        add_records_table(
            elements,
            "Comscore",
            detail_payload.get("comscore_rows") or [],
            ["Hit Type", "Times Fired", "Status", "c1", "c2", "c7", "c8"],
            ["hit_type", "times_fired", "status_chain", "c1", "c2", "c7", "c8"],
            [95, 55, 70, 40, 70, 220, 220],
        )
        add_records_table(
            elements,
            "Chartbeat",
            detail_payload.get("chartbeat_rows") or [],
            ["Check", "Fired", "Times Fired"],
            ["Check", "Fired", "Times Fired"],
            [180, 80, 80],
        )

    doc.build(elements)
    return buffer.getvalue()


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


def build_chartbeat_preview(rows: List[Dict[str, Any]]) -> str:
    if not rows:
        return "Not found"

    highlights = []
    for row in rows:
        parts = []
        for key in ("h", "p", "d", "g", "title"):
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
    chartbeat_rows = load_json_payload(result.get("chartbeat_hits_json", ""), [])
    if not isinstance(chartbeat_rows, list):
        chartbeat_rows = []

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
        "chartbeat_present": bool(result.get("chartbeat_present")),
        "chartbeat_rows": chartbeat_rows,
        "chartbeat_preview": build_chartbeat_preview(chartbeat_rows),
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
        "URL *",
        placeholder="https://www.example.com/article-1 or www.example.com/article-1",
    )

    selected_template = None
    if not active_templates:
        st.warning("No active templates are available.")
    else:
        template_options = [
            None,
            *sorted(
                active_templates,
                key=lambda template: build_template_option_label(template).lower(),
            ),
        ]
        selected_template = st.selectbox(
            "Template *",
            options=template_options,
            format_func=lambda template: "Select a template" if template is None else build_template_option_label(template),
        )
        st.caption("Open the dropdown and start typing to search within the template list.")

    wait_seconds = st.slider(
        "Wait time after page load (seconds)",
        min_value=4,
        max_value=20,
        value=8,
    )

    st.caption("`URL` and `Template` are required to run the audit.")

    if st.button(
        "Run audit",
        disabled=not str(url_text or "").strip() or selected_template is None,
    ):
        original_url, normalized_url, input_error = normalize_single_url(url_text)
        companion_audit_results: Dict[str, Dict[str, Any]] = {}

        if selected_template is None:
            st.error("Please select a template before running the audit.")
        elif input_error:
            st.error(input_error)
        elif not template_reference_matches_url(selected_template, normalized_url):
            st.error(
                "The selected template does not match this URL. "
                "Please choose a template whose reference URL/pattern fits the page you want to audit."
            )
        else:
            if normalized_url != original_url:
                st.info(f"Using normalized URL: `{normalized_url}`")

            results = []
            progress = st.progress(0)
            status_box = st.empty()
            selected_template_rules = get_effective_template_rules(
                selected_template,
                active_templates,
                template_rules_by_template,
            )
            runtime_companion_template = build_runtime_video_companion_template(
                selected_template,
                template_rules_by_template,
            )
            companion_validation_templates = [runtime_companion_template] if runtime_companion_template else []
            companion_rules_map = {
                str(template.get("template_id") or "").strip(): get_rules_for_validation_template(
                    template,
                    template_rules_by_template,
                )
                for template in companion_validation_templates
            }
            combined_interaction_rules: List[dict] = list(selected_template_rules)
            for companion_rules in companion_rules_map.values():
                if companion_rules:
                    combined_interaction_rules.extend(companion_rules)
            total_audit_passes = 1
            completed_audit_passes = 0

            status_box.write(f"Auditing {normalized_url} (1/{total_audit_passes})")
            try:
                # Streamlit Cloud is much more stable on the lighter Selenium path.
                driver = create_driver(headless=True, capture_network=False)
                try:
                    primary_result = audit_single_url(
                        driver,
                        normalized_url,
                        wait_seconds,
                        template_rules=selected_template_rules,
                        force_video_playback=single_audit_requires_video_playback(combined_interaction_rules),
                        force_scroll_capture=single_audit_requires_scroll_capture(combined_interaction_rules),
                    )
                    results.append(primary_result)
                finally:
                    driver.quit()
                completed_audit_passes += 1
                progress.progress(completed_audit_passes / total_audit_passes)
                for companion_template in companion_validation_templates:
                    companion_template_id = str(companion_template.get("template_id") or "").strip()
                    if companion_template_id:
                        companion_audit_results[companion_template_id] = primary_result
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
                            "chartbeat_present": audit_summary["chartbeat_present"],
                            "comscore_values": audit_summary["comscore_preview"],
                            "chartbeat_values": audit_summary["chartbeat_preview"],
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
                    "chartbeat_present",
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

                    stat_col1, stat_col2, stat_col3, stat_col4, stat_col5, stat_col6, stat_col7 = st.columns(7)
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
                    stat_col7.metric(
                        "Chartbeat",
                        "Yes" if audit_summary["chartbeat_present"] else "No",
                    )

                    snapshot = build_datalayer_snapshot_export(result)
                    if selected_template:
                        st.caption(
                            f"Template validation active: **{selected_template.get('template_name') or 'Unnamed template'}**"
                        )
                        if not selected_template_rules:
                            st.info("This template has no rules yet. Add execution-field or event rules in Template Manager.")
                        elif companion_validation_templates:
                            companion_names = ", ".join(
                                str(template.get("template_name") or "Unnamed template")
                                for template in companion_validation_templates
                            )
                            st.caption(
                                f"Companion validation auto-included for this audit: **{companion_names}**"
                            )

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

                    if companion_validation_templates:
                        st.markdown("### Additional Template Validations")
                        st.caption(
                            "Base article detail checks stay separate from companion validations like video interaction."
                        )
                        for companion_template in companion_validation_templates:
                            companion_template_name = str(companion_template.get("template_name") or "Unnamed template")
                            companion_rules = get_rules_for_validation_template(
                                companion_template,
                                template_rules_by_template,
                            )
                            companion_template_id = str(companion_template.get("template_id") or "").strip()
                            companion_result = companion_audit_results.get(companion_template_id)
                            companion_snapshot = build_datalayer_snapshot_export(companion_result) if companion_result else snapshot
                            companion_audit_summary = build_audit_focus_summary(companion_result) if companion_result else audit_summary
                            with st.container(border=True):
                                st.markdown(f"#### {companion_template_name}")
                                if not companion_rules:
                                    st.info("This companion template has no rules yet.")
                                    continue

                                companion_event_df = build_event_validation_rows(
                                    companion_audit_summary["event_rows"],
                                    companion_rules,
                                )
                                companion_has_matched_event = False
                                if isinstance(companion_event_df, pd.DataFrame) and not companion_event_df.empty:
                                    companion_has_matched_event = bool(
                                        (
                                            companion_event_df.get("validation") == VALIDATION_PASS_LABEL
                                        ).any()
                                    ) if "validation" in companion_event_df.columns else False

                                companion_execution_df, _ = build_execution_validation_rows(
                                    companion_snapshot,
                                    companion_rules,
                                    include_unmatched_fields=companion_has_matched_event,
                                )

                                companion_col1, companion_col2 = st.columns(2)
                                with companion_col1:
                                    st.markdown("**Execution checks**")
                                    if not companion_has_matched_event:
                                        st.info(
                                            "No matching video interaction event was captured in this run, so video-field execution values are unavailable."
                                        )
                                    elif companion_execution_df.empty:
                                        st.info("No execution checks are configured for this companion template.")
                                    elif "Validation" in companion_execution_df.columns:
                                        st.dataframe(
                                            style_validation_table(companion_execution_df, "Validation"),
                                            use_container_width=True,
                                            hide_index=True,
                                        )
                                    else:
                                        st.dataframe(
                                            companion_execution_df,
                                            use_container_width=True,
                                            hide_index=True,
                                        )
                                with companion_col2:
                                    st.markdown("**Event checks**")
                                    if companion_event_df.empty:
                                        st.info("No event checks are configured for this companion template.")
                                    else:
                                        companion_event_columns = ["event_name", "status", "times_fired", "capture_layer"]
                                        if "expected" in companion_event_df.columns:
                                            companion_event_columns.append("expected")
                                        if "validation" in companion_event_df.columns:
                                            companion_event_columns.append("validation")
                                        companion_event_display_df = companion_event_df[companion_event_columns].rename(
                                            columns={
                                                "event_name": "Event",
                                                "status": "Status",
                                                "times_fired": "Times Fired",
                                                "capture_layer": "Seen In",
                                                "expected": "Expected",
                                                "validation": "Validation",
                                            }
                                        )
                                        if "Validation" in companion_event_display_df.columns:
                                            st.dataframe(
                                                style_validation_table(companion_event_display_df, "Validation"),
                                                use_container_width=True,
                                                hide_index=True,
                                            )
                                        else:
                                            st.dataframe(
                                                companion_event_display_df,
                                                use_container_width=True,
                                                hide_index=True,
                                            )

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

                    st.markdown("### Chartbeat")
                    if not audit_summary["chartbeat_present"]:
                        chartbeat_validation_df = pd.DataFrame(
                            [
                                {
                                    "Check": "Chartbeat ping",
                                    "Validation": VALIDATION_FAIL_LABEL,
                                    "Times Fired": 0,
                                }
                            ]
                        )
                        st.dataframe(
                            style_validation_table(chartbeat_validation_df, "Validation"),
                            use_container_width=True,
                            hide_index=True,
                        )
                    else:
                        total_chartbeat_fires = sum(
                            int(row.get("times_fired") or 0)
                            for row in (audit_summary.get("chartbeat_rows") or [])
                            if isinstance(row, dict)
                        )
                        if total_chartbeat_fires <= 0:
                            total_chartbeat_fires = 1
                        chartbeat_validation_df = pd.DataFrame(
                            [
                                {
                                    "Check": "Chartbeat ping",
                                    "Validation": VALIDATION_PASS_LABEL,
                                    "Times Fired": total_chartbeat_fires,
                                }
                            ]
                        )
                        st.dataframe(
                            style_validation_table(chartbeat_validation_df, "Validation"),
                            use_container_width=True,
                            hide_index=True,
                        )
                        st.caption("Detailed Chartbeat request values remain available under Advanced debug.")

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
                                "Chartbeat captures",
                                result.get("chartbeat_hits_json", ""),
                                "No Chartbeat values captured.",
                            )

                        render_json_block(
                            "Consent actions",
                            result.get("consent_clicks_json", ""),
                            "No consent click was performed.",
                        )


with tab_domain_audit:
    st.markdown(
        """
Run a domain-level audit from saved templates.

Choose a domain, select templates, and click Run audit. The browser work runs in GitHub Actions and writes results back to Supabase, so Streamlit stays lightweight.
"""
    )

    if template_load_error:
        st.info(template_load_error)
    else:
        domain_wait_seconds = st.slider(
            "Wait time per URL after page load (seconds)",
            min_value=4,
            max_value=20,
            value=8,
            key="domain_audit_wait_seconds",
        )
        active_domain_templates = [template for template in active_templates if template.get("active")]
        domain_names = sorted(
            {get_template_domain_label(template) for template in active_domain_templates},
            key=str.lower,
        )

        if not domain_names:
            st.info("No active templates are available. Add templates in Template Manager first.")
        else:
            selected_domain = st.selectbox(
                "Choose domain",
                domain_names,
                key="domain_audit_selected_domain",
            )
            selected_domain_templates = sorted(
                [
                    template
                    for template in active_domain_templates
                    if get_template_domain_label(template) == selected_domain
                ],
                key=lambda template: str(template.get("template_name") or "").lower(),
            )
            domain_state_key = re.sub(r"[^a-zA-Z0-9_]+", "_", selected_domain).strip("_") or "domain"
            checkbox_keys = []
            for index, template in enumerate(selected_domain_templates):
                template_identity = str(template.get("template_id") or template.get("template_name") or index)
                checkbox_key = f"domain_audit_template_selected_{domain_state_key}_{index}_{_slugify_identifier(template_identity)}"
                checkbox_keys.append(checkbox_key)
                if checkbox_key not in st.session_state:
                    st.session_state[checkbox_key] = True

            select_col1, select_col2, select_col3 = st.columns([1, 1, 5])
            if select_col1.button("Select all", key=f"domain_audit_select_all_{domain_state_key}"):
                for checkbox_key in checkbox_keys:
                    st.session_state[checkbox_key] = True
                st.rerun()
            if select_col2.button("Clear all", key=f"domain_audit_clear_all_{domain_state_key}"):
                for checkbox_key in checkbox_keys:
                    st.session_state[checkbox_key] = False
                st.rerun()
            select_col3.caption(
                "All templates are selected by default. Uncheck any template you do not want in this domain run."
            )

            st.markdown("### Templates to audit")
            selected_templates = []
            if not selected_domain_templates:
                st.info("No active templates are available for this domain.")
            else:
                header_cols = st.columns([0.45, 1.8, 2.4, 2.4, 0.6])
                for col, label in zip(header_cols, ["Run", "Template", "Reference URL / Pattern", "Override URL", "Rules"]):
                    col.markdown(f"**{label}**")

                override_urls: Dict[str, str] = {}
                for index, template in enumerate(selected_domain_templates):
                    checkbox_key = checkbox_keys[index]
                    row_cols = st.columns([0.45, 1.8, 2.4, 2.4, 0.6])
                    is_selected = row_cols[0].checkbox(
                        "Select template",
                        key=checkbox_key,
                        label_visibility="collapsed",
                    )
                    row_cols[1].write(str(template.get("template_name") or "Unnamed template"))
                    row_cols[2].write(str(template.get("url_pattern") or "No reference URL/pattern"))
                    template_id = str(template.get("template_id") or "").strip()
                    override_key = f"domain_audit_override_url_{domain_state_key}_{index}_{_slugify_identifier(template_id or str(index))}"
                    override_value = row_cols[3].text_input(
                        "Override URL",
                        value=st.session_state.get(override_key, ""),
                        key=override_key,
                        label_visibility="collapsed",
                        placeholder="Optional URL override for this run",
                    )
                    if override_value.strip():
                        override_urls[template_id] = override_value.strip()
                    row_cols[4].write(str(len(template_rules_by_template.get(template_id, []))))
                    if is_selected:
                        selected_templates.append(template)

            auto_included_templates = [
                companion_template
                for selected_template in selected_templates
                for companion_template in build_companion_validation_templates(
                    selected_template,
                    active_templates,
                    template_rules_by_template,
                )
            ]
            auto_included_templates = sorted(
                {
                    str(template.get("template_id") or "").strip(): template
                    for template in auto_included_templates
                }.values(),
                key=lambda template: str(template.get("template_name") or "").lower(),
            )

            st.caption("If an override URL is filled for a template, that URL will be audited for this run. Otherwise the saved reference URL/pattern is used.")
            if auto_included_templates:
                auto_included_names = ", ".join(
                    str(template.get("template_name") or "Unnamed template")
                    for template in auto_included_templates
                )
                st.caption(
                    f"Companion templates auto-included for this run: **{auto_included_names}**"
                )

            audit_plan = build_domain_audit_plan_from_templates(
                selected_templates,
                override_urls=override_urls,
                all_templates=active_templates,
                rules_by_template=template_rules_by_template,
            )
            st.caption(
                f"{len(audit_plan)} template URL(s) selected for {selected_domain}. "
                "GitHub Actions will process them sequentially."
            )

            if audit_plan:
                plan_preview_df = pd.DataFrame(
                    [
                        {
                            "Validation Path": "Companion"
                            if row.get("is_companion_template")
                            else "Primary",
                            "Template": row["template_name"],
                            "Sample URL": row["sample_url"] or "Not available",
                            "Override URL": row.get("override_url") or "",
                            "Issue": row["sample_error"],
                        }
                        for row in audit_plan
                    ]
                )
                with st.expander("Selected URL plan", expanded=False):
                    st.dataframe(plan_preview_df, use_container_width=True, hide_index=True)

            st.markdown("### Run Bulk Audit")
            st.caption(
                "This now runs in GitHub Actions. Streamlit only creates the job and reads Supabase results, "
                "so the app should not hit Selenium memory limits."
            )
            if not github_is_configured():
                st.warning(
                    "GitHub trigger is not configured in Streamlit secrets. Add [github] owner, repo, workflow, and token."
                )

            run_cols = st.columns([1, 3])
            run_clicked = run_cols[0].button(
                "Run audit",
                key=f"start_github_domain_audit_{domain_state_key}",
                disabled=not audit_plan or not supabase_is_configured() or not github_is_configured(),
                type="primary",
            )
            run_cols[1].caption(
                "The selected templates will be processed one by one by GitHub Actions."
            )
            if run_clicked:
                success, response = create_bulk_audit_job(
                    logged_in_email,
                    selected_domain,
                    audit_plan,
                    domain_wait_seconds,
                )
                if not success:
                    st.error(response)
                else:
                    job_id = response
                    trigger_success, trigger_message = trigger_bulk_audit_workflow(job_id)
                    if trigger_success:
                        st.session_state["latest_bulk_audit_job_id"] = job_id
                        st.session_state["bulk_audit_force_latest_job_id"] = job_id
                        st.success(f"Bulk audit started in GitHub Actions. Job ID: {job_id}")
                    else:
                        st.error(trigger_message)

            jobs, jobs_error = load_bulk_audit_jobs(selected_domain, limit=12)
            if jobs_error:
                st.warning(jobs_error)
            elif jobs:
                st.markdown("### Bulk Audit Jobs")
                job_options = {
                    f"{job.get('created_at', '')} | {job.get('status', '')} | {job.get('completed_count', 0)}/{job.get('total_count', 0)} | {job.get('job_id')}": job
                    for job in jobs
                }
                latest_job_id = st.session_state.get("latest_bulk_audit_job_id")
                force_latest_job_id = st.session_state.get("bulk_audit_force_latest_job_id")
                labels = list(job_options.keys())
                default_index = 0
                if latest_job_id:
                    for index, label in enumerate(labels):
                        if latest_job_id in label:
                            default_index = index
                            break
                selected_job_key = f"domain_audit_job_select_{domain_state_key}"
                if force_latest_job_id:
                    for label in labels:
                        if force_latest_job_id in label:
                            st.session_state[selected_job_key] = label
                            st.session_state["bulk_audit_force_latest_job_id"] = ""
                            break
                selected_job_label = st.selectbox(
                    "View job",
                    labels,
                    index=default_index,
                    key=selected_job_key,
                )
                selected_job = job_options[selected_job_label]
                selected_job_id = str(selected_job.get("job_id") or "").strip()
                job_total = int(selected_job.get("total_count") or 0)
                job_completed = int(selected_job.get("completed_count") or 0)
                job_status = str(selected_job.get("status") or "").strip().lower()
                progress_percent = int((job_completed / job_total) * 100) if job_total else 0
                progress_milestone = min(100, (progress_percent // 25) * 25) if progress_percent else 0
                milestone_key = f"bulk_audit_progress_milestone_{selected_job_id}"
                previous_milestone = int(st.session_state.get(milestone_key, 0) or 0)
                if progress_milestone > previous_milestone:
                    st.session_state[milestone_key] = progress_milestone
                elif milestone_key not in st.session_state:
                    st.session_state[milestone_key] = progress_milestone

                if job_status in {"queued", "running"} and st_autorefresh:
                    st.caption("Auto-refreshing job status while this audit is in progress.")
                    st_autorefresh(interval=10000, key=f"bulk_audit_autorefresh_{selected_job_id}")

                st.progress((job_completed / job_total) if job_total else 0)
                metric_cols = st.columns(4)
                metric_cols[0].metric("Status", str(selected_job.get("status") or ""))
                metric_cols[1].metric("Completed", f"{job_completed}/{job_total}")
                metric_cols[2].metric("Failed", int(selected_job.get("failed_count") or 0))
                metric_cols[3].metric("Job ID", selected_job_id[-12:] if selected_job_id else "-")
                if progress_milestone and progress_milestone > previous_milestone:
                    st.info(f"Job progress reached {progress_milestone}%.")
                if selected_job.get("error_message"):
                    st.error(str(selected_job.get("error_message")))
                action_cols = st.columns([1, 1, 5])
                if action_cols[0].button("Refresh job status", key=f"refresh_bulk_job_{domain_state_key}"):
                    st.rerun()
                stop_clicked = action_cols[1].button(
                    "Stop audit",
                    key=f"stop_bulk_job_{selected_job_id}",
                    disabled=job_status not in {"queued", "running"},
                )
                if stop_clicked:
                    cancel_success, cancel_message = cancel_bulk_audit_job(selected_job_id)
                    if cancel_success:
                        st.session_state["latest_bulk_audit_job_id"] = selected_job_id
                        st.warning("Audit stop requested. The worker will stop after the current URL finishes.")
                        st.rerun()
                    else:
                        st.error(cancel_message)
                if job_status == "cancelled":
                    st.warning("This bulk audit was stopped before completion.")

                result_records, results_error = load_bulk_audit_results(selected_job_id)
                if results_error:
                    st.warning(results_error)
                report_rows = bulk_result_records_to_report_rows(result_records)
                report_domain = str(selected_job.get("domain_name") or selected_domain)
                if report_rows:
                    st.markdown("### Latest Domain Audit Report")
                    st.caption(f"Domain: {report_domain}")

                issue_rows = [row for row in report_rows if row.get("audit_outcome") == "Issue"]
                metric_col1, metric_col2, metric_col3 = st.columns(3)
                metric_col1.metric("URLs tested", len(report_rows))
                metric_col2.metric("URLs with issues", len(issue_rows))
                metric_col3.metric("Passed", len(report_rows) - len(issue_rows))

                issues_df = pd.DataFrame(
                    [
                        {
                            "Template": row.get("template_name"),
                            "URL": row.get("sample_url"),
                            "GA Fired": "Yes" if row.get("ga_present") else "No",
                            "Comscore Fired": "Yes" if row.get("comscore_present") else "No",
                            "Chartbeat Fired": "Yes" if row.get("chartbeat_present") else "No",
                            "Issues": row.get("issues"),
                        }
                        for row in issue_rows
                    ]
                )
                if issues_df.empty:
                    st.success("No issues were detected in the latest domain audit.")
                else:
                    st.markdown("#### URLs Needing Attention")
                    st.dataframe(issues_df, use_container_width=True, hide_index=True)

                full_report_df = pd.DataFrame(
                    [
                        {
                            "Template": row.get("template_name"),
                            "URL": row.get("sample_url"),
                            "Outcome": row.get("audit_outcome"),
                            "Implementation Status": row.get("implementation_status"),
                            "GA Fired": "Yes" if row.get("ga_present") else "No",
                            "Pageview Triggered": "Yes" if row.get("pageview_triggered") else "No",
                            "Pageview Source": row.get("pageview_source"),
                            "Events Fired": row.get("events_count"),
                            "Measurement ID": row.get("measurement_id"),
                            "Container ID": row.get("container_id"),
                            "Comscore Fired": "Yes" if row.get("comscore_present") else "No",
                            "Chartbeat Fired": "Yes" if row.get("chartbeat_present") else "No",
                            "Issues": row.get("issues") or "None",
                        }
                        for row in report_rows
                    ]
                )
                st.markdown("#### Full Audit Results")
                st.dataframe(full_report_df, use_container_width=True, hide_index=True)

                download_col1, download_col2 = st.columns([1, 1])
                download_col1.download_button(
                    "Download domain audit CSV",
                    full_report_df.to_csv(index=False).encode("utf-8"),
                    export_filename("domain_audit_report", "csv"),
                    "text/csv",
                )
                try:
                    pdf_bytes = build_domain_audit_pdf(report_domain, report_rows)
                    download_col2.download_button(
                        "Download domain audit PDF",
                        pdf_bytes,
                        export_filename("domain_audit_report", "pdf"),
                        "application/pdf",
                    )
                except Exception as exc:
                    st.warning(f"PDF report could not be generated. {exc}")


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
            driver = create_driver(headless=True, capture_network=False)
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
                            "chartbeat_present": prod.get("chartbeat_present"),
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
                            "chartbeat_present": stage.get("chartbeat_present"),
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
                "Choose a domain first, then a template. Editing, reviewing rules, and adding new rules all happen in one workspace."
            )

            template_rules_by_template = {}
            for rule in template_rules:
                template_rules_by_template.setdefault(str(rule.get("template_id") or "").strip(), []).append(rule)
            rule_scope_labels = {value: label for label, value in RULE_SCOPE_OPTIONS.items()}

            domain_options = sorted(
                {get_template_domain_label(template) for template in template_records},
                key=str.lower,
            )
            domain_filter_col, search_filter_col = st.columns([1.1, 1.9])
            with domain_filter_col:
                selected_domain_filter = st.selectbox(
                    "Domain filter",
                    options=["All domains", *domain_options],
                    key="template_manager_domain_filter",
                )
            with search_filter_col:
                template_manager_search = st.text_input(
                    "Search templates",
                    placeholder="Search by template name, domain, measurement ID, container ID, or URL pattern",
                    key="template_manager_search",
                )

            filtered_templates = []
            search_text = str(template_manager_search or "").strip().lower()
            for template in template_records:
                domain_label = get_template_domain_label(template)
                if selected_domain_filter != "All domains" and domain_label != selected_domain_filter:
                    continue
                search_blob = " ".join(
                    [
                        str(template.get("template_name") or ""),
                        domain_label,
                        str(template.get("measurement_id") or ""),
                        str(template.get("container_id") or ""),
                        str(template.get("url_pattern") or ""),
                    ]
                ).lower()
                if search_text and search_text not in search_blob:
                    continue
                filtered_templates.append(template)

            filtered_templates = sorted(
                filtered_templates,
                key=lambda template: (
                    get_template_domain_label(template).lower(),
                    str(template.get("template_name") or "").lower(),
                    str(template.get("measurement_id") or "").lower(),
                ),
            )

            summary_col1, summary_col2, summary_col3 = st.columns(3)
            summary_col1.metric("Domains", len(domain_options))
            summary_col2.metric("Templates in view", len(filtered_templates))
            summary_col3.metric(
                "Active in view",
                sum(1 for template in filtered_templates if template.get("active")),
            )

            st.markdown("### Template Workspace")
            st.caption("Pick a template below. Everything for that template stays in this workspace.")

            if not filtered_templates:
                st.info("No templates match the selected domain and search filters.")
            else:
                filtered_template_map = {
                    str(template.get("template_id") or "").strip(): template
                    for template in filtered_templates
                }
                filtered_template_ids = list(filtered_template_map.keys())
                workspace_template_id = str(st.session_state.get("template_workspace_template_id") or "").strip()
                if workspace_template_id not in filtered_template_ids:
                    workspace_template_id = filtered_template_ids[0]
                    st.session_state["template_workspace_template_id"] = workspace_template_id

                selected_template_id = st.selectbox(
                    "Template",
                    options=filtered_template_ids,
                    index=filtered_template_ids.index(workspace_template_id),
                    format_func=lambda template_id: build_template_option_label(filtered_template_map[template_id]),
                )
                st.session_state["template_workspace_template_id"] = selected_template_id
                st.session_state["template_rule_target_id"] = selected_template_id

                selected_template = filtered_template_map[selected_template_id]
                selected_template_rules = template_rules_by_template.get(selected_template_id, [])
                selected_execution_rules = sorted(
                    [
                        rule
                        for rule in selected_template_rules
                        if str(rule.get("rule_scope") or "").strip().lower() == "execution"
                    ],
                    key=lambda rule: str(rule.get("field_name") or "").lower(),
                )
                selected_event_rules = sorted(
                    [
                        rule
                        for rule in selected_template_rules
                        if str(rule.get("rule_scope") or "").strip().lower() == "event"
                    ],
                    key=lambda rule: str(rule.get("field_name") or "").lower(),
                )

                active_rule_edit_id = str(st.session_state.get("template_rule_edit_id") or "").strip()
                if active_rule_edit_id and not any(
                    str(rule.get("rule_id") or "").strip() == active_rule_edit_id
                    for rule in selected_template_rules
                ):
                    st.session_state.pop("template_rule_edit_id", None)
                    active_rule_edit_id = ""

                metric_col1, metric_col2, metric_col3, metric_col4 = st.columns(4)
                metric_col1.metric("Domain", get_template_domain_label(selected_template))
                metric_col2.metric("Measurement ID", str(selected_template.get("measurement_id") or "Not set"))
                metric_col3.metric("Container ID", str(selected_template.get("container_id") or "Not set"))
                metric_col4.metric("Rules", len(selected_template_rules))

                reference_entries = [
                    line.strip()
                    for line in str(selected_template.get("url_pattern") or "").splitlines()
                    if line.strip()
                ]
                if reference_entries:
                    st.markdown("**Reference URLs / patterns**")
                    for reference_entry in reference_entries:
                        st.write(reference_entry)

                workspace_mode = st.radio(
                    "Workspace view",
                    options=["Template details", "Rules", "Add rule"],
                    horizontal=True,
                    key="template_workspace_mode",
                )

                if workspace_mode == "Template details":
                    st.markdown("#### Edit Template")
                    with st.form(
                        f"template_manager_edit_template_{selected_template_id}",
                        clear_on_submit=False,
                    ):
                        edit_template_name = st.text_input(
                            "Template name",
                            value=str(selected_template.get("template_name") or ""),
                        )
                        edit_meta_col1, edit_meta_col2 = st.columns(2)
                        with edit_meta_col1:
                            edit_domain_name = st.text_input(
                                "Domain / site name",
                                value=str(selected_template.get("domain_name") or ""),
                            )
                            edit_measurement_id = st.text_input(
                                "GA4 measurement ID",
                                value=str(selected_template.get("measurement_id") or ""),
                            )
                        with edit_meta_col2:
                            edit_container_id = st.text_input(
                                "GTM container ID",
                                value=str(selected_template.get("container_id") or ""),
                            )
                        edit_reference_urls = st.text_area(
                            "Reference URLs / patterns (one per line)",
                            value=str(selected_template.get("url_pattern") or ""),
                            help="Add one URL or pattern per line so the template has multiple examples.",
                            height=150,
                        )
                        edit_template_active = st.checkbox(
                            "Active",
                            value=bool(selected_template.get("active")),
                            key=f"edit_template_active_{selected_template_id}",
                        )
                        save_template_changes = st.form_submit_button("Save template changes")

                    if save_template_changes:
                        normalized_reference_urls = normalize_multiline_entries(edit_reference_urls)
                        if not str(edit_template_name or "").strip():
                            st.error("Template name is required.")
                        elif not any(
                            str(value or "").strip()
                            for value in (
                                edit_domain_name,
                                edit_measurement_id,
                                edit_container_id,
                                normalized_reference_urls,
                            )
                        ):
                            st.error("Add at least one identifier: domain, measurement ID, container ID, or URL pattern.")
                        else:
                            success, response = update_template_record(
                                logged_in_email,
                                selected_template_id,
                                {
                                    "template_name": edit_template_name,
                                    "domain_name": edit_domain_name,
                                    "measurement_id": edit_measurement_id,
                                    "container_id": edit_container_id,
                                    "url_pattern": normalized_reference_urls,
                                    "active": edit_template_active,
                                },
                            )
                            if success:
                                st.session_state["template_workspace_template_id"] = selected_template_id
                                st.success(f"Template updated: {edit_template_name}")
                                st.rerun()
                            else:
                                st.error(response)

                elif workspace_mode == "Rules":
                    st.markdown("#### Template Rules")
                    st.caption("Review and edit rules for the selected template. Edits stay in this workspace.")

                    if active_rule_edit_id:
                        rule_to_edit = next(
                            (
                                rule
                                for rule in selected_template_rules
                                if str(rule.get("rule_id") or "").strip() == active_rule_edit_id
                            ),
                            None,
                        )
                        if rule_to_edit:
                            rule_scope_value = str(rule_to_edit.get("rule_scope") or "").strip().lower()
                            rule_scope_label = rule_scope_labels.get(rule_scope_value, rule_scope_value or "Rule")
                            existing_rule_type = str(rule_to_edit.get("rule_type") or "").strip()
                            if existing_rule_type not in RULE_TYPE_OPTIONS:
                                existing_rule_type = "exact"
                            st.info(
                                f"Editing {rule_scope_label.lower()} rule: {str(rule_to_edit.get('field_name') or '').strip() or 'Unnamed rule'}"
                            )
                            with st.form(
                                f"template_manager_edit_rule_{active_rule_edit_id}",
                                clear_on_submit=False,
                            ):
                                edit_rule_field_name = st.text_input(
                                    "Field / event name",
                                    value=str(rule_to_edit.get("field_name") or ""),
                                )
                                edit_rule_col1, edit_rule_col2 = st.columns([1.1, 1.9])
                                with edit_rule_col1:
                                    edit_rule_type = st.selectbox(
                                        "Rule type",
                                        options=RULE_TYPE_OPTIONS,
                                        index=RULE_TYPE_OPTIONS.index(existing_rule_type),
                                    )
                                with edit_rule_col2:
                                    edit_rule_expected_values = ""
                                    if edit_rule_type in {"required", "optional"}:
                                        st.caption("This rule type does not need explicit expected values.")
                                    else:
                                        edit_rule_expected_values = st.text_area(
                                            "Expected values",
                                            value=editable_rule_expected_values_text(
                                                edit_rule_type,
                                                rule_to_edit.get("expected_values"),
                                            ),
                                            help="Use one value per line. For regex rules, use one pattern per line.",
                                            height=120,
                                        )
                                edit_rule_notes = st.text_input(
                                    "Notes (optional)",
                                    value=str(rule_to_edit.get("notes") or ""),
                                )
                                save_rule_col, cancel_rule_col = st.columns([1, 1])
                                save_rule_changes = save_rule_col.form_submit_button("Save rule changes")
                                cancel_rule_changes = cancel_rule_col.form_submit_button("Cancel")

                            if cancel_rule_changes:
                                st.session_state.pop("template_rule_edit_id", None)
                                st.rerun()

                            if save_rule_changes:
                                normalized_expected_values = normalize_rule_expected_values_input(
                                    edit_rule_type,
                                    edit_rule_expected_values,
                                )
                                if not str(edit_rule_field_name or "").strip():
                                    st.error("Field / event name is required.")
                                elif edit_rule_type not in {"required", "optional"} and not normalized_expected_values:
                                    st.error("Expected values are required for this rule type.")
                                else:
                                    success, response = update_template_rule(
                                        logged_in_email,
                                        active_rule_edit_id,
                                        {
                                            "template_id": selected_template_id,
                                            "rule_scope": rule_scope_value,
                                            "field_name": edit_rule_field_name,
                                            "rule_type": edit_rule_type,
                                            "expected_values": normalized_expected_values,
                                            "notes": edit_rule_notes,
                                        },
                                    )
                                    if success:
                                        st.session_state.pop("template_rule_edit_id", None)
                                        st.success("Rule updated.")
                                        st.rerun()
                                    else:
                                        st.error(response)

                    rule_scope_tabs = st.tabs(
                        [
                            f"Execution rules ({len(selected_execution_rules)})",
                            f"Event rules ({len(selected_event_rules)})",
                        ]
                    )

                    with rule_scope_tabs[0]:
                        if not selected_execution_rules:
                            st.info("No execution rules for this template yet.")
                        else:
                            execution_header_cols = st.columns([2.0, 1.2, 2.1, 1.5, 0.8, 0.8])
                            for col, label in zip(
                                execution_header_cols,
                                ["Execution field", "Rule", "Expected values", "Notes", "Edit", "Delete"],
                            ):
                                col.markdown(f"**{label}**")

                            for rule in selected_execution_rules:
                                rule_id = str(rule.get("rule_id") or "").strip()
                                row_cols = st.columns([2.0, 1.2, 2.1, 1.5, 0.8, 0.8])
                                row_values = [
                                    str(rule.get("field_name") or ""),
                                    str(rule.get("rule_type") or ""),
                                    format_rule_expected_values_display(
                                        str(rule.get("rule_type") or ""),
                                        rule.get("expected_values"),
                                    ) or "—",
                                    str(rule.get("notes") or "") or "—",
                                ]
                                for col, value in zip(row_cols[:-2], row_values):
                                    col.write(value)
                                if row_cols[-2].button("✏️", key=f"edit_execution_rule_{rule_id}"):
                                    st.session_state["template_rule_edit_id"] = rule_id
                                    st.rerun()
                                if row_cols[-1].button("🗑", key=f"delete_execution_rule_{rule_id}"):
                                    success, response = delete_template_rule(rule_id)
                                    if success:
                                        if st.session_state.get("template_rule_edit_id") == rule_id:
                                            st.session_state.pop("template_rule_edit_id", None)
                                        st.success("Rule deleted.")
                                        st.rerun()
                                    else:
                                        st.error(response)

                    with rule_scope_tabs[1]:
                        if not selected_event_rules:
                            st.info("No event rules for this template yet.")
                        else:
                            event_header_cols = st.columns([2.0, 1.2, 2.1, 1.5, 0.8, 0.8])
                            for col, label in zip(
                                event_header_cols,
                                ["Event", "Rule", "Expected values", "Notes", "Edit", "Delete"],
                            ):
                                col.markdown(f"**{label}**")

                            for rule in selected_event_rules:
                                rule_id = str(rule.get("rule_id") or "").strip()
                                row_cols = st.columns([2.0, 1.2, 2.1, 1.5, 0.8, 0.8])
                                row_values = [
                                    str(rule.get("field_name") or ""),
                                    str(rule.get("rule_type") or ""),
                                    format_rule_expected_values_display(
                                        str(rule.get("rule_type") or ""),
                                        rule.get("expected_values"),
                                    ) or "—",
                                    str(rule.get("notes") or "") or "—",
                                ]
                                for col, value in zip(row_cols[:-2], row_values):
                                    col.write(value)
                                if row_cols[-2].button("✏️", key=f"edit_event_rule_{rule_id}"):
                                    st.session_state["template_rule_edit_id"] = rule_id
                                    st.rerun()
                                if row_cols[-1].button("🗑", key=f"delete_event_rule_{rule_id}"):
                                    success, response = delete_template_rule(rule_id)
                                    if success:
                                        if st.session_state.get("template_rule_edit_id") == rule_id:
                                            st.session_state.pop("template_rule_edit_id", None)
                                        st.success("Rule deleted.")
                                        st.rerun()
                                    else:
                                        st.error(response)

                else:
                    st.markdown("#### Add Rule")
                    st.caption(
                        "Use execution rules for fields like page_type or author. Use event rules for event names. Regex rules accept one pattern per line."
                    )

                    global_execution_field_options, global_execution_value_catalog = build_execution_rule_catalog(template_rules)
                    global_event_field_options = sorted(
                        {
                            str(rule.get("field_name") or "").strip()
                            for rule in template_rules
                            if str(rule.get("rule_scope") or "").strip().lower() == "event"
                            and str(rule.get("field_name") or "").strip()
                        },
                        key=str.lower,
                    )

                    pending_execution_key = f"pending_execution_rules_{selected_template_id}"
                    if pending_execution_key not in st.session_state:
                        st.session_state[pending_execution_key] = []

                    add_rule_tabs = st.tabs(["Execution rule", "Event rule"])

                    with add_rule_tabs[0]:
                        with st.form(
                            f"template_manager_add_execution_rule_{selected_template_id}",
                            clear_on_submit=True,
                        ):
                            field_col, rule_col, value_col = st.columns([1.4, 1.0, 1.8])
                            with field_col:
                                execution_field_choice = st.selectbox(
                                    "Execution field",
                                    options=["Add new field...", *global_execution_field_options]
                                    if global_execution_field_options
                                    else ["Add new field..."],
                                    key=f"execution_field_choice_{selected_template_id}",
                                )
                                new_execution_field = ""
                                if execution_field_choice == "Add new field...":
                                    new_execution_field = st.text_input(
                                        "New execution field",
                                        placeholder="page_type",
                                        key=f"new_execution_field_{selected_template_id}",
                                    )

                            with rule_col:
                                execution_rule_type = st.selectbox(
                                    "Rule",
                                    options=RULE_TYPE_OPTIONS,
                                    key=f"execution_rule_type_{selected_template_id}",
                                )

                            selected_execution_field = (
                                str(new_execution_field or "").strip()
                                if execution_field_choice == "Add new field..."
                                else execution_field_choice
                            )
                            known_value_options = global_execution_value_catalog.get(selected_execution_field, [])

                            with value_col:
                                execution_saved_value_selection = []
                                execution_expected_values_input = ""
                                if execution_rule_type in {"required", "optional"}:
                                    st.caption("This rule type does not need explicit expected values.")
                                else:
                                    if execution_rule_type != "regex" and known_value_options:
                                        execution_saved_value_selection = st.multiselect(
                                            "Saved values",
                                            options=known_value_options,
                                            key=f"execution_saved_values_{selected_template_id}_{selected_execution_field}",
                                        )
                                    execution_expected_values_input = st.text_area(
                                        "Expected values",
                                        help="Use one value per line. For regex rules, use one pattern per line.",
                                        placeholder="article detail\ngallery",
                                        height=120,
                                        key=f"execution_expected_values_{selected_template_id}",
                                    )
                                    merged_preview = merge_rule_expected_value_inputs(
                                        execution_rule_type,
                                        execution_saved_value_selection,
                                        execution_expected_values_input,
                                    )
                                    if merged_preview:
                                        st.caption(
                                            f"Will be stored as: {format_rule_expected_values_display(execution_rule_type, merged_preview)}"
                                        )

                            execution_notes = st.text_input(
                                "Notes (optional)",
                                key=f"execution_rule_notes_{selected_template_id}",
                            )
                            add_execution_rule_submitted = st.form_submit_button("Add execution rule")

                        if add_execution_rule_submitted:
                            normalized_expected_values = merge_rule_expected_value_inputs(
                                execution_rule_type,
                                execution_saved_value_selection,
                                execution_expected_values_input,
                            )
                            if not selected_execution_field:
                                st.error("Choose an execution field or add a new one.")
                            elif execution_rule_type not in {"required", "optional"} and not normalized_expected_values:
                                st.error("Expected values are required for this rule type.")
                            else:
                                pending_rules = list(st.session_state.get(pending_execution_key, []))
                                pending_rules.append(
                                    {
                                        "field_name": selected_execution_field,
                                        "rule_type": execution_rule_type,
                                        "expected_values": normalized_expected_values,
                                        "notes": execution_notes,
                                    }
                                )
                                st.session_state[pending_execution_key] = pending_rules
                                st.success(f"Added `{selected_execution_field}` to the pending execution batch.")

                        pending_rules = st.session_state.get(pending_execution_key, [])
                        if pending_rules:
                            st.markdown("##### Pending execution rules")
                            pending_display_df = pd.DataFrame(pending_rules).rename(
                                columns={
                                    "field_name": "Execution field",
                                    "rule_type": "Rule",
                                    "expected_values": "Expected values",
                                    "notes": "Notes",
                                }
                            )
                            if not pending_display_df.empty and "Expected values" in pending_display_df.columns:
                                pending_display_df["Expected values"] = pending_display_df.apply(
                                    lambda row: format_rule_expected_values_display(
                                        row.get("Rule"),
                                        row.get("Expected values"),
                                    ),
                                    axis=1,
                                )
                            st.dataframe(pending_display_df, use_container_width=True, hide_index=True)
                            pending_action_col1, pending_action_col2 = st.columns([1, 1])
                            if pending_action_col1.button(
                                "Save execution rule batch",
                                key=f"save_execution_batch_{selected_template_id}",
                            ):
                                success, response = append_template_rules(
                                    logged_in_email,
                                    [
                                        {
                                            "template_id": selected_template_id,
                                            "rule_scope": "execution",
                                            "field_name": entry["field_name"],
                                            "rule_type": entry["rule_type"],
                                            "expected_values": entry["expected_values"],
                                            "notes": entry["notes"],
                                        }
                                        for entry in pending_rules
                                    ],
                                )
                                if success:
                                    st.session_state[pending_execution_key] = []
                                    st.success(f"{response} execution rule(s) added.")
                                    st.rerun()
                                else:
                                    st.error(response)
                            if pending_action_col2.button(
                                "Clear execution batch",
                                key=f"clear_execution_batch_{selected_template_id}",
                            ):
                                st.session_state[pending_execution_key] = []
                                st.rerun()

                    with add_rule_tabs[1]:
                        with st.form(
                            f"template_manager_add_event_rule_{selected_template_id}",
                            clear_on_submit=True,
                        ):
                            field_col, rule_col, value_col = st.columns([1.4, 1.0, 1.8])
                            with field_col:
                                event_field_choice = st.selectbox(
                                    "Event label / field",
                                    options=["Add new event...", *global_event_field_options]
                                    if global_event_field_options
                                    else ["Add new event..."],
                                    key=f"event_field_choice_{selected_template_id}",
                                )
                                new_event_field = ""
                                if event_field_choice == "Add new event...":
                                    new_event_field = st.text_input(
                                        "New event label / field",
                                        placeholder="page_view",
                                        key=f"new_event_field_{selected_template_id}",
                                    )
                            with rule_col:
                                event_rule_type = st.selectbox(
                                    "Rule",
                                    options=RULE_TYPE_OPTIONS,
                                    key=f"event_rule_type_{selected_template_id}",
                                )
                            with value_col:
                                event_expected_values_input = ""
                                if event_rule_type in {"required", "optional"}:
                                    st.caption("This rule type does not need explicit expected values.")
                                else:
                                    event_expected_values_input = st.text_area(
                                        "Expected values",
                                        help="Use one value per line. For regex rules, use one pattern per line.",
                                        placeholder="page_view\npage_scroll",
                                        height=120,
                                        key=f"event_expected_values_{selected_template_id}",
                                    )
                                    event_preview = normalize_rule_expected_values_input(
                                        event_rule_type,
                                        event_expected_values_input,
                                    )
                                    if event_preview:
                                        st.caption(
                                            f"Will be stored as: {format_rule_expected_values_display(event_rule_type, event_preview)}"
                                        )
                            event_notes = st.text_input(
                                "Notes (optional)",
                                key=f"event_rule_notes_{selected_template_id}",
                            )
                            add_event_rule_submitted = st.form_submit_button("Add event rule")

                        if add_event_rule_submitted:
                            selected_event_field = (
                                str(new_event_field or "").strip()
                                if event_field_choice == "Add new event..."
                                else event_field_choice
                            )
                            normalized_expected_values = normalize_rule_expected_values_input(
                                event_rule_type,
                                event_expected_values_input,
                            )
                            if not selected_event_field:
                                st.error("Event label / field is required.")
                            elif event_rule_type not in {"required", "optional"} and not normalized_expected_values:
                                st.error("Expected values are required for this rule type.")
                            else:
                                success, response = append_template_rule(
                                    logged_in_email,
                                    {
                                        "template_id": selected_template_id,
                                        "rule_scope": "event",
                                        "field_name": selected_event_field,
                                        "rule_type": event_rule_type,
                                        "expected_values": normalized_expected_values,
                                        "notes": event_notes,
                                    },
                                )
                                if success:
                                    st.success("Rule added.")
                                    st.rerun()
                                else:
                                    st.error(response)

            with st.expander("Create New Template", expanded=False):
                with st.form("template_manager_add_template", clear_on_submit=True):
                    template_name = st.text_input("Template name", placeholder="Daily Jagran Article")
                    meta_col1, meta_col2 = st.columns(2)
                    with meta_col1:
                        domain_name = st.text_input("Domain / site name", placeholder="www.example.com")
                        measurement_id = st.text_input("GA4 measurement ID", placeholder="G-XXXXXXXXXX")
                    with meta_col2:
                        container_id = st.text_input("GTM container ID", placeholder="GTM-XXXXXXX")
                    reference_urls = st.text_area(
                        "Reference URLs / patterns (one per line)",
                        placeholder=(
                            "https://www.example.com/world/*\n"
                            "https://www.example.com/world/article-1\n"
                            "https://www.example.com/world/article-2"
                        ),
                        help="Add one URL or pattern per line so the template has multiple examples.",
                        height=150,
                    )
                    template_active = st.checkbox("Active", value=True)
                    add_template_submitted = st.form_submit_button("Add template")

                if add_template_submitted:
                    normalized_reference_urls = normalize_multiline_entries(reference_urls)
                    if not str(template_name or "").strip():
                        st.error("Template name is required.")
                    elif not any(
                        str(value or "").strip()
                        for value in (domain_name, measurement_id, container_id, normalized_reference_urls)
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
                                "url_pattern": normalized_reference_urls,
                                "active": template_active,
                            },
                        )
                        if success:
                            new_domain = str(domain_name or "").strip() or "Unspecified domain"
                            st.session_state["template_workspace_template_id"] = response
                            st.session_state["template_manager_domain_filter"] = new_domain
                            st.success(f"Template added: {template_name}")
                            st.rerun()
                        else:
                            st.error(response)

            with st.expander("Import Templates", expanded=False):
                st.caption(
                    "Upload the GA mapping workbook. The importer uses the Finalized sheet, groups templates by page_type, "
                    "and converts static/dynamic formats into validation rules."
                )
                mapping_file = st.file_uploader(
                    "GA mapping Excel",
                    type=["xlsx"],
                    key="ga_mapping_excel_import_file",
                )
                import_meta_col1, import_meta_col2, import_meta_col3 = st.columns(3)
                with import_meta_col1:
                    mapping_domain = st.text_input(
                        "Default domain",
                        value="www.jagran.com",
                        key="ga_mapping_import_domain",
                    )
                with import_meta_col2:
                    mapping_measurement_id = st.text_input(
                        "Default measurement ID",
                        value="G-3RLQSM7QQQ",
                        key="ga_mapping_import_measurement_id",
                    )
                with import_meta_col3:
                    mapping_container_id = st.text_input(
                        "Default container ID",
                        value="GTM-5CTQK3",
                        key="ga_mapping_import_container_id",
                    )

                imported_mapping_templates = []
                mapping_parse_notes = []
                if mapping_file is not None:
                    try:
                        imported_mapping_templates, mapping_parse_notes = parse_ga_mapping_excel_templates(
                            mapping_file.getvalue(),
                            mapping_domain,
                            mapping_measurement_id,
                            mapping_container_id,
                        )
                        total_imported_rules = sum(
                            len(template.get("rules") or [])
                            for template in imported_mapping_templates
                        )
                        st.success(
                            f"Detected {len(imported_mapping_templates)} page_type template(s) "
                            f"and {total_imported_rules} rule(s)."
                        )
                        if mapping_parse_notes:
                            with st.expander("Import parser notes"):
                                for note in mapping_parse_notes[:20]:
                                    st.write(note)
                        preview_rows = [
                            {
                                "Template": template.get("template_name"),
                                "Rules": len(template.get("rules") or []),
                                "Reference URLs / Patterns": format_multiline_entries_display(template.get("url_pattern") or ""),
                            }
                            for template in imported_mapping_templates[:8]
                        ]
                        if preview_rows:
                            st.dataframe(
                                pd.DataFrame(preview_rows),
                                use_container_width=True,
                                hide_index=True,
                            )
                    except Exception as exc:
                        st.error(f"Could not read GA mapping Excel: {exc}")

                keep_homepage_template = st.checkbox(
                    "Also add/update the Home Page starter template",
                    value=True,
                    key="ga_mapping_import_keep_homepage",
                )
                add_mapping_confirmed = st.checkbox(
                    "I understand this will add templates from the workbook and update matching template names.",
                    key="ga_mapping_import_add_confirmed",
                )
                if st.button(
                    "Add GA mapping templates",
                    key="add_templates_from_ga_mapping",
                    disabled=mapping_file is None or not imported_mapping_templates or not add_mapping_confirmed,
                ):
                    seeds_to_import = list(imported_mapping_templates)
                    if keep_homepage_template:
                        seeds_to_import = [get_homepage_starter_template(), *seeds_to_import]
                    success, response = add_templates_from_seed_templates(
                        logged_in_email,
                        seeds_to_import,
                        template_records,
                        template_rules,
                        "GA mapping templates",
                    )
                    if success:
                        st.success(response)
                        st.rerun()
                    else:
                        st.error(response)

            with st.expander("Maintenance", expanded=False):
                st.caption("Use this only if you want to remove every template except Home Page.")
                cleanup_confirmed = st.checkbox(
                    "I understand this will remove all saved templates except Home Page.",
                    key="reset_templates_to_homepage_confirmed",
                )
                if st.button(
                    "Remove all templates except Home Page",
                    key="reset_templates_to_homepage_only",
                    disabled=not cleanup_confirmed,
                ):
                    success, response = reset_templates_to_homepage_only(logged_in_email)
                    if success:
                        st.success(response)
                        st.rerun()
                    else:
                        st.error(response)
