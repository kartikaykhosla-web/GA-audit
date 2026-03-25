import os
import re
import json
import time
import glob
import shutil
import subprocess
from datetime import datetime, timezone
from typing import List, Dict, Any, Tuple, Optional, Set
from urllib.parse import urlparse, parse_qs

import pandas as pd
import requests
import streamlit as st
from bs4 import BeautifulSoup
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


def _flatten_qs(values):
    flat = {}
    for key, raw in values.items():
        if isinstance(raw, list):
            flat[key] = raw[0] if raw else ""
        else:
            flat[key] = raw
    return flat


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
        "ul": "language",
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


def _collect_params(event_list):
    params = {}
    for event in merge_ga4_events(event_list):
        raw = event.get("params")
        if isinstance(raw, dict):
            params.update(raw)
    return params


def map_dl_to_ga4(
    pageview_event_json,
    ga4_exec_events_json,
    ga4_network_events_json,
):
    dl_event = _safe_json_load(pageview_event_json, {})
    exec_events = _safe_json_load(ga4_exec_events_json, [])
    network_events = _safe_json_load(ga4_network_events_json, [])

    exec_params = _collect_params(exec_events)
    network_params = _collect_params(network_events)

    rows = []
    matched_exec = set()
    matched_network = set()

    for dl_key, dl_value in dl_event.items():
        if dl_key == "event" or str(dl_key).startswith("gtm"):
            continue

        dl_norm = _normalize_key(dl_key)

        exec_key = None
        exec_value = None
        for current_key, current_value in exec_params.items():
            if _normalize_key(current_key) == dl_norm:
                exec_key = current_key
                exec_value = current_value
                matched_exec.add(current_key)
                break

        ga4_key = None
        ga4_value = None
        for current_key, current_value in network_params.items():
            if _normalize_key(current_key) == dl_norm:
                ga4_key = current_key
                ga4_value = current_value
                matched_network.add(current_key)
                break

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

    for ga4_key, ga4_value in network_params.items():
        if ga4_key in matched_network:
            continue
        rows.append(
            {
                "dl_key": None,
                "dl_value": None,
                "exec_key": None,
                "exec_value": None,
                "ga4_key": ga4_key,
                "ga4_value": ga4_value,
            }
        )

    for exec_key, exec_value in exec_params.items():
        if exec_key in matched_exec:
            continue
        rows.append(
            {
                "dl_key": None,
                "dl_value": None,
                "exec_key": exec_key,
                "exec_value": exec_value,
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
    "ul": "language",
    "tid": "measurement_id",
    "cid": "client_id",
    "sid": "session_id",
}

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


def extract_collect_hits_from_performance_logs(driver, page_domain: str) -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]]]:
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
            if not (_is_ga4_collect_hit(url) or _is_ccm_pageview_hit(url, page_domain)):
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
            if not (_is_ga4_collect_hit(url) or _is_ccm_pageview_hit(url, page_domain)):
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

    for request_id, item in requests_by_id.items():
        url = str(item.get("url") or "")
        if not url:
            continue
        if not (_is_ga4_collect_hit(url) or _is_ccm_pageview_hit(url, page_domain)):
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

        if _is_ccm_pageview_hit(url, page_domain):
            ccm_pageviews.append(hit)
        else:
            ga4_collects.append(hit)

    return ga4_collects, ccm_pageviews


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

    perf_ga4_collects, perf_ccm_pageviews = extract_collect_hits_from_performance_logs(driver, page_domain)
    ga4_collects = merge_network_hits(ga4_collects, perf_ga4_collects)
    ccm_pageviews = merge_network_hits(ccm_pageviews, perf_ccm_pageviews)

    return {
        "gtm_present": bool(gtm_scripts),
        "gtag_present": bool(gtag_scripts),
        "ga4_collect_present": bool(ga4_collects),
        "ccm_pageview_present": bool(ccm_pageviews),
        "gtm_scripts": gtm_scripts,
        "gtag_scripts": gtag_scripts,
        "ga4_collects": ga4_collects,
        "ccm_pageviews": ccm_pageviews,
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
        "gtm_scripts_sample": "",
        "gtag_scripts_sample": "",
        "ga4_collects_sample": "",
        "ccm_pageviews_sample": "",
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

    result["gtm_scripts_sample"] = _format_hits_sample(net_info["gtm_scripts"])
    result["gtag_scripts_sample"] = _format_hits_sample(net_info["gtag_scripts"])
    result["ga4_collects_sample"] = _format_hits_sample(net_info["ga4_collects"])
    result["ccm_pageviews_sample"] = _format_hits_sample(net_info["ccm_pageviews"])

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

import json
from datetime import datetime, timezone

import pandas as pd
import streamlit as st



st.set_page_config(page_title="GA4 / dataLayer Auditor", layout="wide")
st.title("GA4 / dataLayer Auditor")

tab_main, tab_compare = st.tabs(["Audit URLs", "Compare Prod vs Stage"])


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


def best_matching_event(selected_event: dict, events):
    if not isinstance(events, list) or not events:
        return None

    target = normalize_event_name(selected_event.get("event"))
    if target:
        for event in events:
            if not isinstance(event, dict):
                continue
            if normalize_event_name(event.get("event_name")) == target:
                return event

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


def find_event_by_name(events, target_name: str):
    target = normalize_event_name(target_name)
    for event in events or []:
        if not isinstance(event, dict):
            continue
        if normalize_event_name(event.get("event_name")) == target:
            return event
    return None


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
            "dl_key": row.get("dl_key") or "",
            "dl_value": dl_value if dl_value is not None else "",
            "exec_key": row.get("exec_key") or "",
            "exec_value": exec_value if exec_value is not None else "",
            "ga4_key": row.get("ga4_key") or "",
            "ga4_value": ga4_value if ga4_value is not None else "",
            "status": status,
        }
        cleaned_rows.append(cleaned)

    return cleaned_rows


def summarize_mapping_values(mapping_rows):
    captured_network = []
    captured_execution = []
    trigger_only = []

    for row in mapping_rows:
        dimension = row.get("dimension")
        if row.get("status") == "Captured in network":
            captured_network.append(f"{dimension}={stringify_value(row.get('ga4_value'))}")
        elif row.get("status") == "Captured in execution":
            captured_execution.append(f"{dimension}={stringify_value(row.get('exec_value'))}")
        elif row.get("status") == "Only in trigger":
            trigger_only.append(f"{dimension}={stringify_value(row.get('dl_value'))}")

    return captured_network, captured_execution, trigger_only


def preview_list(values, limit: int = 5):
    if not values:
        return "None"
    if len(values) <= limit:
        return ", ".join(values)
    return ", ".join(values[:limit]) + f" (+{len(values) - limit} more)"


def build_audit_focus_summary(result: dict):
    execution_events = load_json_payload(result.get("ga4_execution_events_json", ""), [])
    network_events = load_json_payload(result.get("ga4_network_events_json", ""), [])

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
        "events_fired": extract_event_names(result),
        "mapping_rows": mapping_rows,
        "captured_network": captured_network,
        "captured_execution": captured_execution,
        "trigger_only": trigger_only,
    }


with tab_main:
    st.markdown(
        """
Paste one or more URLs and run the audit.

This capture is split into three layers:
- `dataLayer` trigger state
- execution-stage GA4 values intercepted before transport
- final network request / response hits
"""
    )

    urls_text = st.text_area(
        "URLs",
        height=160,
        placeholder="https://www.example.com/\nhttps://www.example.com/article-1",
    )

    wait_seconds = st.slider(
        "Wait time after page load (seconds)",
        min_value=4,
        max_value=20,
        value=8,
    )

    headful = st.checkbox(
        "Run Chrome in visible mode",
        value=False,
        help="Use this if tracking is blocked in headless mode.",
    )

    if st.button("Run audit"):
        urls = [
            url.strip()
            for line in urls_text.splitlines()
            for url in line.split(",")
            if url.strip()
        ]

        if not urls:
            st.error("Please enter at least one URL.")
        else:
            results = []
            progress = st.progress(0)
            status_box = st.empty()

            for index, url in enumerate(urls, start=1):
                status_box.write(f"Auditing {url} ({index}/{len(urls)})")
                try:
                    driver = create_driver(headless=not headful)
                    try:
                        results.append(audit_single_url(driver, url, wait_seconds))
                    finally:
                        driver.quit()
                except Exception as exc:
                    st.error(f"Error auditing {url}")
                    st.exception(exc)
                progress.progress(index / len(urls))

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

                    if result.get("preload_hook_error"):
                        st.warning(
                            "Early instrumentation was not installed cleanly. "
                            f"Details: {result['preload_hook_error']}"
                        )

                    stat_col1, stat_col2, stat_col3 = st.columns(3)
                    stat_col1.metric(
                        "Pageview Triggered",
                        "Yes" if audit_summary["pageview_triggered"] else "No",
                    )
                    stat_col2.metric("Pageview Source", audit_summary["pageview_source"])
                    stat_col3.metric("Events Fired", str(len(audit_summary["events_fired"])))

                    st.markdown("### Events Fired")
                    if audit_summary["events_fired"]:
                        st.write(", ".join(audit_summary["events_fired"]))
                    else:
                        st.info("No GA4 events were detected during the audit window.")

                    st.markdown("### Trigger → Execution → Network Mapping")
                    mapping_df = pd.DataFrame(audit_summary["mapping_rows"])
                    if mapping_df.empty:
                        st.info("No mapping table available.")
                    else:
                        if not audit_summary["captured_network"]:
                            st.warning(
                                "No decodable final GA4 network payload was captured in this run. "
                                "`ga4_key` and `ga4_value` stay blank when the request is seen only at "
                                "trigger/execution stage or the final network hit cannot be decoded."
                            )
                        st.dataframe(mapping_df, use_container_width=True, hide_index=True)
                        mapping_csv = mapping_df.to_csv(index=False).encode("utf-8")
                        st.download_button(
                            "Download mapping CSV",
                            mapping_csv,
                            export_filename("ga4_mapping", "csv"),
                            "text/csv",
                        )

                    with st.expander("Observed values by layer", expanded=False):
                        st.markdown("### Captured in Network")
                        if audit_summary["captured_network"]:
                            st.write(", ".join(audit_summary["captured_network"]))
                        else:
                            st.info("No mapped values reached the final GA4 network payload.")

                        st.markdown("### Captured in Execution Only")
                        if audit_summary["captured_execution"]:
                            st.write(", ".join(audit_summary["captured_execution"]))
                        else:
                            st.info("No additional mapped values were found only at execution stage.")

                        st.markdown("### Trigger Only (not fired downstream)")
                        if audit_summary["trigger_only"]:
                            st.write(", ".join(audit_summary["trigger_only"]))
                        else:
                            st.info("No mapped values were left behind in the trigger layer.")

                    with st.expander("Final collect request / response", expanded=False):
                        render_network_hits(result.get("ga4_network_hits_json", ""), title=None)

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
                            "Consent actions",
                            result.get("consent_clicks_json", ""),
                            "No consent click was performed.",
                        )

                with st.expander("Advanced downloads", expanded=False):
                    share_payload = build_share_payload(results)
                    share_json = json.dumps(share_payload, ensure_ascii=False, indent=2).encode("utf-8")
                    st.download_button(
                        "Download full debug JSON",
                        share_json,
                        export_filename("ga4_debug_export", "json"),
                        "application/json",
                    )


with tab_compare:
    st.markdown("Compare tagging between two URLs, typically Prod vs Stage.")

    prod_col, stage_col = st.columns(2)
    prod_url = prod_col.text_input("Prod URL")
    stage_url = stage_col.text_input("Stage URL")

    wait_cmp = st.slider("Wait seconds", 4, 20, 8, key="wait_compare")
    headful_cmp = st.checkbox("Visible browser", value=False, key="cmp_headful")

    if st.button("Run comparison"):
        if not prod_url or not stage_url:
            st.error("Enter both URLs.")
        else:
            driver = create_driver(headless=not headful_cmp)
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
                            "pv_page_location": stage.get("pv_page_location"),
                            "pv_page_title": stage.get("pv_page_title"),
                            "issues": stage.get("issues"),
                        },
                    ]
                ),
                use_container_width=True,
            )
