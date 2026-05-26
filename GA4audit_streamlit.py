import functools
import json
import os
import re
import shutil
import time
import uuid
from collections import Counter
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple
from urllib.parse import parse_qs, urlparse

import pandas as pd
import streamlit as st

try:
    import psycopg
    from psycopg.rows import dict_row
except Exception:
    psycopg = None
    dict_row = None

from selenium import webdriver
from selenium.common.exceptions import TimeoutException, WebDriverException
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service
from selenium.webdriver.common.action_chains import ActionChains
from selenium.webdriver.common.by import By


st.set_page_config(page_title="GA4 / dataLayer Auditor", layout="wide")

APP_TITLE = "GA4 / dataLayer Auditor"
DEFAULT_WAIT_SECONDS = 8
DEFAULT_VIDEO_WAIT_SECONDS = 20
RULE_TYPE_OPTIONS = ["exact", "one_of", "contains", "regex", "required", "optional"]
DEFAULT_CREATED_BY = os.environ.get("USER", "local")

TEMPLATE_SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS ga_audit_templates (
    template_id text PRIMARY KEY,
    template_name text NOT NULL,
    domain_name text DEFAULT '',
    measurement_id text DEFAULT '',
    container_id text DEFAULT '',
    url_pattern text DEFAULT '',
    active boolean DEFAULT true,
    created_by text DEFAULT '',
    created_at text DEFAULT ''
);

CREATE TABLE IF NOT EXISTS ga_audit_template_rules (
    rule_id text PRIMARY KEY,
    template_id text NOT NULL REFERENCES ga_audit_templates(template_id) ON DELETE CASCADE,
    rule_scope text NOT NULL CHECK (rule_scope IN ('execution', 'event')),
    field_name text NOT NULL,
    rule_type text NOT NULL CHECK (rule_type IN ('exact', 'one_of', 'contains', 'regex', 'required', 'optional')),
    expected_values text DEFAULT '',
    notes text DEFAULT '',
    created_by text DEFAULT '',
    created_at text DEFAULT ''
);

CREATE INDEX IF NOT EXISTS idx_ga_audit_templates_domain_name
    ON ga_audit_templates(domain_name);

CREATE INDEX IF NOT EXISTS idx_ga_audit_template_rules_template_id
    ON ga_audit_template_rules(template_id);
"""

PRELOAD_SCRIPT = r"""
(function () {
  try {
    if (window.__videoMvpInstalled) return;
    window.__videoMvpInstalled = true;

    var state = window.__videoMvpState = window.__videoMvpState || {
      dataLayerPushes: [],
      gtagCalls: [],
      transportHits: []
    };

    function trim(list) {
      if (list.length > 80) {
        list.splice(0, list.length - 80);
      }
    }

    function safeClone(value, depth) {
      depth = depth || 0;
      if (depth > 2) return "[MaxDepth]";
      if (value === null || value === undefined) return value;
      var type = typeof value;
      if (type === "string" || type === "number" || type === "boolean") return value;
      if (type === "function") return "[Function]";
      if (Array.isArray(value)) {
        return value.slice(0, 20).map(function (entry) {
          return safeClone(entry, depth + 1);
        });
      }
      if (typeof FormData !== "undefined" && value instanceof FormData) {
        var pairs = [];
        value.forEach(function (entryValue, entryKey) {
          pairs.push(encodeURIComponent(entryKey) + "=" + encodeURIComponent(String(entryValue)));
        });
        return pairs.join("&");
      }
      if (typeof URLSearchParams !== "undefined" && value instanceof URLSearchParams) {
        return value.toString();
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
        Object.keys(value).slice(0, 60).forEach(function (key) {
          try {
            output[key] = safeClone(value[key], depth + 1);
          } catch (e) {}
        });
        return output;
      }
      return String(value);
    }

    function push(target, payload) {
      try {
        state[target].push(Object.assign({ timestamp: Date.now() }, payload));
        trim(state[target]);
      } catch (e) {}
    }

    function isInterestingUrl(url) {
      if (typeof url !== "string") return false;
      return (
        url.indexOf("google-analytics.com") !== -1 ||
        url.indexOf("/g/collect") !== -1 ||
        url.indexOf("/mp/collect") !== -1 ||
        url.indexOf("/collect") !== -1
      );
    }

    function asText(data) {
      try {
        if (data === null || data === undefined) return "";
        if (typeof data === "string") return data;
        if (typeof URLSearchParams !== "undefined" && data instanceof URLSearchParams) return data.toString();
        if (typeof FormData !== "undefined" && data instanceof FormData) {
          var pairs = [];
          data.forEach(function (entryValue, entryKey) {
            pairs.push(encodeURIComponent(entryKey) + "=" + encodeURIComponent(String(entryValue)));
          });
          return pairs.join("&");
        }
        return String(data);
      } catch (e) {
        return "[unserializable]";
      }
    }

    function recordTransport(api, url, method, body) {
      try {
        if (!isInterestingUrl(url)) return;
        push("transportHits", {
          api: api,
          url: String(url || ""),
          method: String(method || "GET").toUpperCase(),
          bodyText: asText(body)
        });
      } catch (e) {}
    }

    function wrapDataLayer(list) {
      if (!list) list = [];
      if (list.__videoMvpWrappedPush) return list;
      var originalPush = typeof list.push === "function" ? list.push : Array.prototype.push;
      Object.defineProperty(list, "__videoMvpWrappedPush", {
        value: true,
        configurable: true
      });
      list.push = function () {
        var args = Array.prototype.slice.call(arguments);
        push("dataLayerPushes", {
          entry: safeClone(args[0], 0),
          event: args[0] && args[0].event ? args[0].event : ""
        });
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
      if (original && original.__videoMvpWrapped) return original;
      var wrapped = function () {
        var args = Array.prototype.slice.call(arguments);
        push("gtagCalls", {
          command: args[0],
          event_name: args[0] === "event" ? args[1] : "",
          params: args[0] === "event" && args[2] && typeof args[2] === "object"
            ? safeClone(args[2], 0)
            : null
        });
        if (typeof original === "function") {
          return original.apply(this, arguments);
        }
      };
      Object.defineProperty(wrapped, "__videoMvpWrapped", {
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

    if (navigator && typeof navigator.sendBeacon === "function" && !navigator.sendBeacon.__videoMvpWrapped) {
      var originalSendBeacon = navigator.sendBeacon.bind(navigator);
      var wrappedSendBeacon = function (url, data) {
        recordTransport("sendBeacon", url, "POST", data);
        return originalSendBeacon(url, data);
      };
      wrappedSendBeacon.__videoMvpWrapped = true;
      navigator.sendBeacon = wrappedSendBeacon;
    }

    if (typeof window.fetch === "function" && !window.fetch.__videoMvpWrapped) {
      var originalFetch = window.fetch.bind(window);
      var wrappedFetch = function (input, init) {
        var url = typeof input === "string" ? input : (input && input.url) || "";
        var method = (init && init.method) || (input && input.method) || "GET";
        var body = (init && init.body) || null;
        recordTransport("fetch", url, method, body);
        return originalFetch(input, init);
      };
      wrappedFetch.__videoMvpWrapped = true;
      window.fetch = wrappedFetch;
    }

    if (typeof XMLHttpRequest !== "undefined" && XMLHttpRequest.prototype && !XMLHttpRequest.prototype.__videoMvpWrapped) {
      var originalOpen = XMLHttpRequest.prototype.open;
      var originalSend = XMLHttpRequest.prototype.send;
      XMLHttpRequest.prototype.open = function (method, url) {
        try {
          this.__videoMvpUrl = url || "";
          this.__videoMvpMethod = method || "GET";
        } catch (e) {}
        return originalOpen.apply(this, arguments);
      };
      XMLHttpRequest.prototype.send = function (body) {
        try {
          recordTransport("xhr", this.__videoMvpUrl || "", this.__videoMvpMethod || "GET", body);
        } catch (e) {}
        return originalSend.apply(this, arguments);
      };
      Object.defineProperty(XMLHttpRequest.prototype, "__videoMvpWrapped", {
        value: true,
        configurable: true
      });
    }
  } catch (e) {}
})();
"""

LIGHTWEIGHT_CONSENT_SELECTORS = [
    "#onetrust-accept-btn-handler",
    ".onetrust-accept-btn-handler",
    "#CybotCookiebotDialogBodyLevelButtonLevelOptinAllowAll",
    "#didomi-notice-agree-button",
    "[id*='didomi-notice-agree-button']",
    "[data-testid*='accept']",
    "[aria-label*='Accept']",
]

ARTICLE_OPEN_SELECTORS = [
    ".Short_wrapper_fixed img[alt='video thumbnail']",
    ".Short_wrapper_fixed img[src*='thumbnail' i]",
    ".Short_wrapper_fixed i.videoImage",
    ".Short_wrapper_fixed [class*='play' i]",
    ".Short_wrapper_fixed [role='button']",
    ".ArticleDetail_relatedvideo__wvgRP img",
    ".ArticleDetail_relatedvideo__wvgRP .article",
    ".ArticleDetail_relatedvideo__wvgRP i.videoImage",
    ".ArticleDetail_relatedvideo__wvgRP [class*='play' i]",
    ".ArticleDetail_relatedvideo__wvgRP [role='button']",
    ".relatedvideo img",
    ".relatedvideo .article",
    ".relatedvideo a",
    "img[alt='video thumbnail']",
]

PLAY_CONTROL_SELECTORS = [
    ".video-player-container [aria-label*='play' i]",
    ".VideoSwiper_videoContainer [aria-label*='play' i]",
    ".video-player-container [class*='play' i]",
    ".VideoSwiper_videoContainer [class*='play' i]",
    ".video-player-container [role='button']",
    ".VideoSwiper_videoContainer [role='button']",
    ".video-player-container button",
    ".VideoSwiper_videoContainer button",
]


def safe_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, indent=2)


def now_text() -> str:
    return datetime.now(timezone.utc).isoformat()


def text_value(value: Any) -> str:
    if value is None:
        return ""
    return str(value).strip()


def normalize_event_name(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "", str(value or "").strip().lower())


def normalize_url(raw_value: str) -> Tuple[str, str]:
    value = text_value(raw_value)
    if not value:
        return "", "Please enter a URL."
    if not re.match(r"^https?://", value, re.I):
        value = f"https://{value}"
    parsed = urlparse(value)
    if not parsed.netloc:
        return "", "Please enter a valid URL."
    return value, ""


def parse_expected_values(raw_value: Any) -> List[str]:
    text = text_value(raw_value)
    if not text:
        return []
    parts = re.split(r"[|\n\r]+", text)
    return [part.strip() for part in parts if part.strip()]


def get_case_insensitive(payload: Dict[str, Any], field_name: str) -> Any:
    target = text_value(field_name).lower()
    for key, value in (payload or {}).items():
        if text_value(key).lower() == target:
            return value
    return None


def evaluate_rule(actual_value: Any, rule_type: str, expected_values: Any) -> Tuple[str, str]:
    normalized_rule_type = text_value(rule_type).lower()
    actual_text = text_value(actual_value)
    expected_list = parse_expected_values(expected_values)

    if normalized_rule_type == "optional":
        return "Matched", actual_text or "Optional"
    if normalized_rule_type == "required":
        return ("Matched", actual_text) if actual_text else ("Mismatch", "Not observed")
    if not actual_text:
        return "Mismatch", "Not observed"
    if normalized_rule_type == "exact":
        return ("Matched", actual_text) if actual_text in expected_list else ("Mismatch", actual_text)
    if normalized_rule_type == "one_of":
        return ("Matched", actual_text) if actual_text in expected_list else ("Mismatch", actual_text)
    if normalized_rule_type == "contains":
        actual_lower = actual_text.lower()
        matched = any(item.lower() in actual_lower for item in expected_list)
        return ("Matched", actual_text) if matched else ("Mismatch", actual_text)
    if normalized_rule_type == "regex":
        matched = any(re.search(pattern, actual_text) for pattern in expected_list if pattern)
        return ("Matched", actual_text) if matched else ("Mismatch", actual_text)
    return "Mismatch", actual_text


def template_option_label(template: Dict[str, Any]) -> str:
    pieces = [text_value(template.get("template_name")) or "Unnamed template"]
    meta = [text_value(template.get("domain_name")), text_value(template.get("measurement_id")), text_value(template.get("container_id"))]
    meta = [item for item in meta if item]
    if meta:
        pieces.append(f"({' | '.join(meta)})")
    return " ".join(pieces)


def rule_table_rows(rules: List[Dict[str, Any]]) -> List[Dict[str, Any]]:
    rows = []
    for rule in rules:
        rows.append(
            {
                "Rule ID": text_value(rule.get("rule_id")),
                "Scope": text_value(rule.get("rule_scope")),
                "Field": text_value(rule.get("field_name")),
                "Rule": text_value(rule.get("rule_type")),
                "Expected": text_value(rule.get("expected_values")),
                "Notes": text_value(rule.get("notes")),
            }
        )
    return rows


@functools.lru_cache(maxsize=1)
def resolve_chrome_paths() -> Tuple[str, str]:
    binary_candidates = [
        os.environ.get("CHROME_BINARY"),
        "/usr/bin/chromium",
        "/usr/bin/chromium-browser",
        "/usr/bin/google-chrome",
        "/Applications/Google Chrome.app/Contents/MacOS/Google Chrome",
    ]
    driver_candidates = [
        os.environ.get("CHROMEDRIVER_PATH"),
        shutil.which("chromedriver"),
        "/usr/bin/chromedriver",
    ]
    chrome_binary = next((item for item in binary_candidates if item and os.path.exists(item)), "")
    chromedriver = next((item for item in driver_candidates if item and os.path.exists(item)), "")
    return chrome_binary, chromedriver


def create_driver(headless: bool = True) -> webdriver.Chrome:
    chrome_binary, chromedriver = resolve_chrome_paths()
    options = Options()
    if headless:
        options.add_argument("--headless=new")
    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--window-size=1440,2200")
    options.add_argument("--autoplay-policy=no-user-gesture-required")
    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_argument("--disable-background-timer-throttling")
    options.add_argument("--disable-backgrounding-occluded-windows")
    options.add_argument("--disable-renderer-backgrounding")
    options.add_argument("--mute-audio")
    if chrome_binary:
        options.binary_location = chrome_binary

    service = Service(executable_path=chromedriver) if chromedriver else None
    try:
        driver = webdriver.Chrome(options=options, service=service) if service else webdriver.Chrome(options=options)
    except WebDriverException as exc:
        message = str(exc)
        if service and ("only supports Chrome version" in message or "session not created" in message.lower()):
            driver = webdriver.Chrome(options=options)
        else:
            raise
    driver.set_page_load_timeout(20)
    driver.set_script_timeout(5)
    try:
        driver.execute_cdp_cmd("Page.addScriptToEvaluateOnNewDocument", {"source": PRELOAD_SCRIPT})
        driver.execute_cdp_cmd("Network.enable", {})
    except Exception:
        pass
    return driver


def safe_quit(driver: Optional[webdriver.Chrome]) -> None:
    if not driver:
        return
    try:
        driver.quit()
    except Exception:
        pass


def native_click(driver: webdriver.Chrome, element) -> bool:
    if not element:
        return False
    try:
        driver.execute_script("arguments[0].scrollIntoView({block:'center', inline:'center'});", element)
    except Exception:
        pass
    try:
        ActionChains(driver).move_to_element(element).pause(0.08).click().perform()
        return True
    except Exception:
        pass
    try:
        element.click()
        return True
    except Exception:
        return False


def click_first_visible(driver: webdriver.Chrome, selectors: List[str]) -> bool:
    for selector in selectors:
        try:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
        except Exception:
            continue
        for element in elements[:5]:
            try:
                if not element.is_displayed():
                    continue
                if native_click(driver, element):
                    return True
            except Exception:
                continue
    return False


def accept_common_consent(driver: webdriver.Chrome) -> List[str]:
    clicked: List[str] = []
    for selector in LIGHTWEIGHT_CONSENT_SELECTORS:
        try:
            elements = driver.find_elements(By.CSS_SELECTOR, selector)
        except Exception:
            continue
        for element in elements[:2]:
            try:
                if not element.is_displayed():
                    continue
                driver.execute_script("arguments[0].click();", element)
                clicked.append(selector)
                time.sleep(0.15)
                return clicked
            except Exception:
                continue
    return clicked


def reset_visible_videos(driver: webdriver.Chrome) -> None:
    try:
        driver.execute_script(
            """
            document.querySelectorAll("video").forEach((video) => {
              const rect = video.getBoundingClientRect();
              if (!rect.width || !rect.height) return;
              try {
                video.pause();
                video.currentTime = 0;
              } catch (e) {}
            });
            """
        )
    except Exception:
        pass


def capture_primary_video_state(driver: webdriver.Chrome) -> Dict[str, Any]:
    try:
        return driver.execute_script(
            """
            const videos = Array.from(document.querySelectorAll("video"));
            for (const video of videos) {
              const rect = video.getBoundingClientRect();
              if (!rect.width || !rect.height) continue;
              return {
                paused: !!video.paused,
                muted: !!video.muted,
                currentTime: Number(video.currentTime || 0),
                duration: Number(video.duration || 0),
                readyState: Number(video.readyState || 0),
                width: Number(rect.width || 0),
                height: Number(rect.height || 0),
                top: Number(rect.top || 0),
                src: String(video.currentSrc || video.src || "")
              };
            }
            return {};
            """
        ) or {}
    except Exception as exc:
        return {"error": str(exc)}


def extract_state(driver: webdriver.Chrome) -> Dict[str, Any]:
    try:
        return driver.execute_script(
            "return window.__videoMvpState ? JSON.parse(JSON.stringify(window.__videoMvpState)) : {};"
        ) or {}
    except Exception:
        return {}


def decode_collect(url: str, body_text: str = "") -> List[Dict[str, Any]]:
    parsed = urlparse(url)
    payloads: List[Dict[str, Any]] = []
    query_payload = {key: values[-1] if values else "" for key, values in parse_qs(parsed.query, keep_blank_values=True).items()}
    body_text = text_value(body_text)
    if not body_text:
        payloads = [query_payload]
    elif "=" in body_text:
        body_payload = {key: values[-1] if values else "" for key, values in parse_qs(body_text, keep_blank_values=True).items()}
        payloads = [{**query_payload, **body_payload}]
    else:
        payloads = [{**query_payload, "_body_text": body_text}]

    events: List[Dict[str, Any]] = []
    for payload in payloads:
        params: Dict[str, Any] = {}
        for key, value in payload.items():
            if key.startswith(("ep.", "epn.", "epf.")):
                params[key.split(".", 1)[1]] = value
        for raw_key, clean_key in {
            "dl": "page_location",
            "dt": "page_title",
            "dr": "page_referrer",
            "en": "event_name",
        }.items():
            if raw_key in payload and clean_key not in params:
                params[clean_key] = payload[raw_key]
        event_name = text_value(payload.get("en") or payload.get("event_name"))
        if event_name:
            events.append({"event_name": event_name, "params": params, "raw_fields": payload, "source": "transport"})
    return events


def synthetic_event_from_datalayer_entry(entry: Any) -> Optional[Dict[str, Any]]:
    if isinstance(entry, dict):
        event_name = text_value(entry.get("event"))
        if not event_name:
            return None
        params = {
            str(key): value
            for key, value in entry.items()
            if str(key) != "event" and not str(key).startswith("gtm")
        }
        return {"event_name": event_name, "params": params, "raw_fields": dict(entry), "source": "dataLayer"}
    if isinstance(entry, list) and len(entry) >= 2:
        command_name = text_value(entry[0]).lower()
        event_name = text_value(entry[1])
        params = entry[2] if len(entry) > 2 and isinstance(entry[2], dict) else {}
        if command_name == "event" and event_name:
            return {
                "event_name": event_name,
                "params": dict(params),
                "raw_fields": {"event": event_name, **dict(params)},
                "source": "dataLayer",
            }
    return None


def normalize_state_events(state: Dict[str, Any]) -> Dict[str, Any]:
    gtag_events: List[Dict[str, Any]] = []
    for call in state.get("gtagCalls", []) or []:
        if not isinstance(call, dict):
            continue
        if text_value(call.get("command")).lower() != "event":
            continue
        gtag_events.append(
            {
                "event_name": text_value(call.get("event_name")),
                "params": dict(call.get("params") or {}),
                "raw_fields": dict(call.get("params") or {}),
                "source": "gtag",
            }
        )

    data_layer_events: List[Dict[str, Any]] = []
    for push_entry in state.get("dataLayerPushes", []) or []:
        if not isinstance(push_entry, dict):
            continue
        event = synthetic_event_from_datalayer_entry(push_entry.get("entry"))
        if event:
            data_layer_events.append(event)

    transport_events: List[Dict[str, Any]] = []
    for hit in state.get("transportHits", []) or []:
        if not isinstance(hit, dict):
            continue
        transport_events.extend(
            decode_collect(text_value(hit.get("url")), text_value(hit.get("bodyText")))
        )

    all_events = [*data_layer_events, *gtag_events, *transport_events]
    return {
        "gtag_events": gtag_events,
        "data_layer_events": data_layer_events,
        "transport_events": transport_events,
        "all_events": all_events,
        "raw_state": state,
    }


def payload_from_event(event: Optional[Dict[str, Any]]) -> Dict[str, Any]:
    if not isinstance(event, dict):
        return {}
    payload = dict(event.get("params") or {})
    payload.setdefault("event_name", text_value(event.get("event_name")))
    return payload


def find_event_by_name(events: List[Dict[str, Any]], event_name: str) -> Optional[Dict[str, Any]]:
    target = normalize_event_name(event_name)
    for event in events or []:
        if normalize_event_name(event.get("event_name")) == target:
            return event
    return None


def merge_event_payloads(events: List[Dict[str, Any]], event_name: str) -> Dict[str, Any]:
    merged: Dict[str, Any] = {}
    for event in events or []:
        if normalize_event_name(event.get("event_name")) != normalize_event_name(event_name):
            continue
        merged.update(payload_from_event(event))
    return merged


def capture_page_audit(url: str, wait_seconds: int, headless: bool = True) -> Dict[str, Any]:
    driver = None
    debug_steps: List[Dict[str, Any]] = []
    try:
        driver = create_driver(headless=headless)
        driver.get(url)
        debug_steps.append({"step": "driver.get", "success": True})
        consent_actions = accept_common_consent(driver)
        debug_steps.append({"step": "accept_common_consent", "actions": consent_actions})
        try:
            driver.execute_script(
                """
                try {
                    if (typeof gtag === "function") {
                        gtag('consent', 'update', {
                            analytics_storage: 'granted',
                            ad_storage: 'granted',
                            ad_user_data: 'granted',
                            ad_personalization: 'granted'
                        });
                    }
                } catch (e) {}
                """
            )
        except Exception:
            pass
        time.sleep(max(1, int(wait_seconds or DEFAULT_WAIT_SECONDS)))
        state = extract_state(driver)
        normalized = normalize_state_events(state)
        primary_event = (
            find_event_by_name(normalized["all_events"], "page_view")
            or find_event_by_name(normalized["all_events"], "pageview")
            or (normalized["all_events"][-1] if normalized["all_events"] else None)
        )
        return {
            "url": url,
            "debug_steps": debug_steps,
            "state": state,
            "normalized": normalized,
            "primary_event": primary_event,
            "video_state": capture_primary_video_state(driver),
            "counts": {
                "gtag_calls": len((state.get("gtagCalls") or [])),
                "data_layer_pushes": len((state.get("dataLayerPushes") or [])),
                "transport_hits": len((state.get("transportHits") or [])),
                "matched_events": len(normalized["all_events"]),
            },
        }
    except TimeoutException as exc:
        return {"error": f"Timeout: {exc}", "url": url, "debug_steps": debug_steps}
    except Exception as exc:
        return {"error": str(exc), "url": url, "debug_steps": debug_steps}
    finally:
        safe_quit(driver)


def capture_video_event(url: str, headless: bool = True) -> Dict[str, Any]:
    driver = None
    debug_steps: List[Dict[str, Any]] = []
    try:
        driver = create_driver(headless=headless)
        driver.get(url)
        debug_steps.append({"step": "driver.get", "success": True})

        consent_actions = accept_common_consent(driver)
        debug_steps.append({"step": "accept_common_consent", "actions": consent_actions})

        try:
            driver.execute_script(
                """
                try {
                    if (typeof gtag === "function") {
                        gtag('consent', 'update', {
                            analytics_storage: 'granted',
                            ad_storage: 'granted',
                            ad_user_data: 'granted',
                            ad_personalization: 'granted'
                        });
                    }
                } catch (e) {}
                """
            )
        except Exception:
            pass

        time.sleep(1.0)
        clicked_initial = click_first_visible(driver, ARTICLE_OPEN_SELECTORS)
        time.sleep(0.8)
        clicked_control = click_first_visible(driver, PLAY_CONTROL_SELECTORS)
        time.sleep(0.8)

        reset_visible_videos(driver)
        time.sleep(0.3)

        clicked_control_after_reset = click_first_visible(driver, PLAY_CONTROL_SELECTORS)
        if not clicked_control_after_reset:
            try:
                driver.execute_script(
                    """
                    const video = document.querySelector("video");
                    if (video) {
                        video.muted = false;
                        video.defaultMuted = false;
                        const p = video.play();
                        if (p && typeof p.catch === "function") p.catch(() => {});
                    }
                    """
                )
            except Exception:
                pass

        debug_steps.append(
            {
                "step": "video_probe",
                "clicked_initial": clicked_initial,
                "clicked_control": clicked_control,
                "clicked_control_after_reset": clicked_control_after_reset,
            }
        )

        start = time.time()
        latest_state: Dict[str, Any] = {}
        latest_video_state: Dict[str, Any] = {}
        matched: Optional[Dict[str, Any]] = None
        while time.time() - start < DEFAULT_VIDEO_WAIT_SECONDS:
            latest_state = extract_state(driver)
            normalized = normalize_state_events(latest_state)
            latest_video_state = capture_primary_video_state(driver)
            data_layer_match = find_event_by_name(normalized["data_layer_events"], "video_interaction")
            gtag_match = find_event_by_name(normalized["gtag_events"], "video_interaction")
            transport_match = find_event_by_name(normalized["transport_events"], "video_interaction")
            if data_layer_match or gtag_match or transport_match:
                matched = {
                    "data_layer_video_event": data_layer_match,
                    "gtag_video_event": gtag_match,
                    "transport_video_event": transport_match,
                    "normalized": normalized,
                }
                break
            time.sleep(1.0)

        normalized = normalize_state_events(latest_state)
        if matched is None:
            matched = {
                "data_layer_video_event": find_event_by_name(normalized["data_layer_events"], "video_interaction"),
                "gtag_video_event": find_event_by_name(normalized["gtag_events"], "video_interaction"),
                "transport_video_event": find_event_by_name(normalized["transport_events"], "video_interaction"),
                "normalized": normalized,
            }

        primary_event = (
            matched["data_layer_video_event"]
            or matched["gtag_video_event"]
            or matched["transport_video_event"]
        )

        return {
            "url": url,
            "debug_steps": debug_steps,
            "state": latest_state,
            "normalized": normalized,
            "matched": matched,
            "primary_event": primary_event,
            "video_state": latest_video_state,
            "counts": {
                "gtag_calls": len((latest_state.get("gtagCalls") or [])),
                "data_layer_pushes": len((latest_state.get("dataLayerPushes") or [])),
                "transport_hits": len((latest_state.get("transportHits") or [])),
                "matched_events": int(bool(primary_event)),
            },
        }
    except TimeoutException as exc:
        return {"error": f"Timeout: {exc}", "url": url, "debug_steps": debug_steps}
    except Exception as exc:
        return {"error": str(exc), "url": url, "debug_steps": debug_steps}
    finally:
        safe_quit(driver)


def get_neon_database_url() -> str:
    candidates = [
        os.environ.get("NEON_DATABASE_URL"),
        os.environ.get("DATABASE_URL"),
        os.environ.get("POSTGRES_URL"),
    ]
    try:
        candidates.extend(
            [
                st.secrets.get("NEON_DATABASE_URL"),
                st.secrets.get("DATABASE_URL"),
                st.secrets.get("POSTGRES_URL"),
            ]
        )
        neon_secret = st.secrets.get("neon")
        if isinstance(neon_secret, dict):
            candidates.extend(
                [
                    neon_secret.get("database_url"),
                    neon_secret.get("url"),
                ]
            )
    except Exception:
        pass
    for candidate in candidates:
        if text_value(candidate):
            return text_value(candidate)
    return ""


def neon_is_configured() -> bool:
    return bool(psycopg and dict_row and get_neon_database_url())


def neon_connect():
    database_url = get_neon_database_url()
    if not database_url:
        raise RuntimeError("NEON_DATABASE_URL or DATABASE_URL is not configured.")
    if not psycopg or not dict_row:
        raise RuntimeError("psycopg is not installed.")
    return psycopg.connect(database_url, row_factory=dict_row)


@st.cache_resource(show_spinner=False)
def ensure_neon_schema() -> bool:
    with neon_connect() as conn:
        with conn.cursor() as cur:
            cur.execute(TEMPLATE_SCHEMA_SQL)
        conn.commit()
    return True


def normalize_template_row(row: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "template_id": text_value(row.get("template_id")),
        "template_name": text_value(row.get("template_name")),
        "domain_name": text_value(row.get("domain_name")),
        "measurement_id": text_value(row.get("measurement_id")),
        "container_id": text_value(row.get("container_id")),
        "url_pattern": text_value(row.get("url_pattern")),
        "active": bool(row.get("active")),
        "created_by": text_value(row.get("created_by")),
        "created_at": text_value(row.get("created_at")),
    }


def normalize_rule_row(row: Dict[str, Any]) -> Dict[str, Any]:
    return {
        "rule_id": text_value(row.get("rule_id")),
        "template_id": text_value(row.get("template_id")),
        "rule_scope": text_value(row.get("rule_scope")),
        "field_name": text_value(row.get("field_name")),
        "rule_type": text_value(row.get("rule_type")),
        "expected_values": text_value(row.get("expected_values")),
        "notes": text_value(row.get("notes")),
        "created_by": text_value(row.get("created_by")),
        "created_at": text_value(row.get("created_at")),
    }


@st.cache_data(ttl=60, show_spinner=False)
def load_templates_and_rules() -> Tuple[List[Dict[str, Any]], List[Dict[str, Any]], str]:
    if not neon_is_configured():
        return [], [], "Neon is not configured. Add NEON_DATABASE_URL or DATABASE_URL to secrets."
    try:
        ensure_neon_schema()
        with neon_connect() as conn:
            with conn.cursor() as cur:
                cur.execute("SELECT * FROM ga_audit_templates ORDER BY template_name ASC")
                templates = [normalize_template_row(row) for row in cur.fetchall()]
                cur.execute("SELECT * FROM ga_audit_template_rules ORDER BY field_name ASC")
                rules = [normalize_rule_row(row) for row in cur.fetchall()]
        return templates, rules, ""
    except Exception as exc:
        return [], [], str(exc)


def clear_template_cache() -> None:
    try:
        load_templates_and_rules.clear()
    except Exception:
        pass


def append_template_record(template_payload: Dict[str, Any], created_by: str = DEFAULT_CREATED_BY) -> Tuple[bool, str]:
    ensure_neon_schema()
    template_id = f"tpl_{uuid.uuid4().hex[:10]}"
    created_at = now_text()
    with neon_connect() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """
                INSERT INTO ga_audit_templates (
                    template_id, template_name, domain_name, measurement_id,
                    container_id, url_pattern, active, created_by, created_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                """,
                (
                    template_id,
                    text_value(template_payload.get("template_name")),
                    text_value(template_payload.get("domain_name")),
                    text_value(template_payload.get("measurement_id")),
                    text_value(template_payload.get("container_id")),
                    text_value(template_payload.get("url_pattern")),
                    bool(template_payload.get("active", True)),
                    created_by,
                    created_at,
                ),
            )
        conn.commit()
    clear_template_cache()
    return True, template_id


def append_template_rule(rule_payload: Dict[str, Any], created_by: str = DEFAULT_CREATED_BY) -> Tuple[bool, str]:
    ensure_neon_schema()
    rule_id = f"rule_{uuid.uuid4().hex[:10]}"
    created_at = now_text()
    with neon_connect() as conn:
        with conn.cursor() as cur:
            cur.execute(
                """
                INSERT INTO ga_audit_template_rules (
                    rule_id, template_id, rule_scope, field_name, rule_type,
                    expected_values, notes, created_by, created_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                """,
                (
                    rule_id,
                    text_value(rule_payload.get("template_id")),
                    text_value(rule_payload.get("rule_scope")),
                    text_value(rule_payload.get("field_name")),
                    text_value(rule_payload.get("rule_type")),
                    text_value(rule_payload.get("expected_values")),
                    text_value(rule_payload.get("notes")),
                    created_by,
                    created_at,
                ),
            )
        conn.commit()
    clear_template_cache()
    return True, rule_id


def build_event_counter(events: List[Dict[str, Any]]) -> Counter:
    counter: Counter = Counter()
    for event in events or []:
        event_name = text_value(event.get("event_name"))
        if event_name:
            counter[normalize_event_name(event_name)] += 1
    return counter


def validate_event_rules(all_events: List[Dict[str, Any]], rules: List[Dict[str, Any]]) -> pd.DataFrame:
    rows: List[Dict[str, Any]] = []
    event_rules = [rule for rule in rules if text_value(rule.get("rule_scope")).lower() == "event"]
    event_counter = build_event_counter(all_events)
    for rule in event_rules:
        rule_event_name = text_value(rule.get("field_name"))
        count = event_counter.get(normalize_event_name(rule_event_name), 0)
        rows.append(
            {
                "Event": rule_event_name,
                "Expected": text_value(rule.get("expected_values")) or rule_event_name,
                "Times Fired": count,
                "Validation": "Matched" if count > 0 else "Mismatch",
            }
        )
    return pd.DataFrame(rows)


def validate_execution_rules(payload: Dict[str, Any], rules: List[Dict[str, Any]]) -> pd.DataFrame:
    rows: List[Dict[str, Any]] = []
    execution_rules = [rule for rule in rules if text_value(rule.get("rule_scope")).lower() == "execution"]
    for rule in execution_rules:
        field_name = text_value(rule.get("field_name"))
        actual_value = get_case_insensitive(payload, field_name)
        status, display_value = evaluate_rule(actual_value, text_value(rule.get("rule_type")), rule.get("expected_values"))
        rows.append(
            {
                "Field": field_name,
                "Value": display_value,
                "Expected": text_value(rule.get("expected_values")),
                "Validation": status,
            }
        )
    return pd.DataFrame(rows)


def payload_value_rows(payload: Dict[str, Any]) -> pd.DataFrame:
    rows = [{"Field": key, "Value": value} for key, value in (payload or {}).items()]
    return pd.DataFrame(rows)


def render_result_block(title: str, result: Dict[str, Any], rules: List[Dict[str, Any]]) -> None:
    if result.get("error"):
        st.error(result["error"])
        if result.get("debug_steps"):
            with st.expander("Debug steps", expanded=True):
                st.json(result["debug_steps"])
        return

    primary_payload = payload_from_event(result.get("primary_event"))
    all_events = (result.get("normalized") or {}).get("all_events", [])

    st.markdown(f"### {title}")
    metric_cols = st.columns(4)
    counts = result.get("counts", {})
    metric_cols[0].metric("Gtag Calls", counts.get("gtag_calls", 0))
    metric_cols[1].metric("dataLayer Pushes", counts.get("data_layer_pushes", 0))
    metric_cols[2].metric("Transport Hits", counts.get("transport_hits", 0))
    metric_cols[3].metric("Observed Events", counts.get("matched_events", 0))

    if primary_payload:
        st.markdown("#### Captured Event Values")
        st.dataframe(payload_value_rows(primary_payload), use_container_width=True, hide_index=True)
    else:
        st.warning("No matching primary event payload was captured.")

    event_df = validate_event_rules(all_events, rules)
    execution_df = validate_execution_rules(primary_payload, rules)
    col1, col2 = st.columns(2)
    with col1:
        st.markdown("#### Event Validation")
        if event_df.empty:
            st.info("No event rules for this template.")
        else:
            st.dataframe(event_df, use_container_width=True, hide_index=True)
    with col2:
        st.markdown("#### Execution Validation")
        if execution_df.empty:
            st.info("No execution rules for this template.")
        else:
            st.dataframe(execution_df, use_container_width=True, hide_index=True)

    video_state = result.get("video_state") or {}
    if video_state:
        st.markdown("#### Video State")
        st.dataframe(payload_value_rows(video_state), use_container_width=True, hide_index=True)

    with st.expander("Debug JSON", expanded=False):
        st.json(result)


def render_template_manager(templates: List[Dict[str, Any]], rules: List[Dict[str, Any]]) -> None:
    st.subheader("Template Manager")
    template_map = {text_value(template.get("template_id")): template for template in templates}

    overview_df = pd.DataFrame(
        [
            {
                "Template": text_value(template.get("template_name")),
                "Domain": text_value(template.get("domain_name")),
                "Measurement ID": text_value(template.get("measurement_id")),
                "Container ID": text_value(template.get("container_id")),
                "Active": bool(template.get("active")),
            }
            for template in templates
        ]
    )
    if overview_df.empty:
        st.info("No templates found in Neon yet.")
    else:
        st.dataframe(overview_df, use_container_width=True, hide_index=True)

    selected_template = st.selectbox(
        "Inspect template rules",
        options=[None, *templates],
        format_func=lambda item: "Select a template" if item is None else template_option_label(item),
        key="template_manager_selected_template",
    )
    if selected_template is not None:
        selected_rules = [
            rule for rule in rules
            if text_value(rule.get("template_id")) == text_value(selected_template.get("template_id"))
        ]
        st.markdown("#### Rules")
        rules_df = pd.DataFrame(rule_table_rows(selected_rules))
        if rules_df.empty:
            st.info("No rules found for this template yet.")
        else:
            st.dataframe(rules_df, use_container_width=True, hide_index=True)

    st.markdown("#### Add Template")
    with st.form("add_template_form", clear_on_submit=True):
        template_name = st.text_input("Template name")
        domain_name = st.text_input("Domain name", value="www.jagran.com")
        measurement_id = st.text_input("Measurement ID")
        container_id = st.text_input("Container ID")
        url_pattern = st.text_area("Reference URL / Pattern")
        active = st.checkbox("Active", value=True)
        submitted = st.form_submit_button("Add template")
    if submitted:
        if not text_value(template_name):
            st.error("Template name is required.")
        else:
            success, response = append_template_record(
                {
                    "template_name": template_name,
                    "domain_name": domain_name,
                    "measurement_id": measurement_id,
                    "container_id": container_id,
                    "url_pattern": url_pattern,
                    "active": active,
                }
            )
            if success:
                st.success(f"Template added: {response}")
                st.rerun()
            else:
                st.error(response)

    st.markdown("#### Add Rule")
    if not templates:
        st.info("Add a template first.")
        return

    with st.form("add_rule_form", clear_on_submit=True):
        rule_template = st.selectbox(
            "Template",
            options=templates,
            format_func=template_option_label,
            key="add_rule_template_select",
        )
        rule_scope = st.selectbox("Rule scope", options=["execution", "event"])
        field_name = st.text_input("Field name")
        rule_type = st.selectbox("Rule type", options=RULE_TYPE_OPTIONS)
        expected_values = st.text_area("Expected values (`|` or newline separated)")
        notes = st.text_area("Notes")
        submitted_rule = st.form_submit_button("Add rule")
    if submitted_rule:
        if not text_value(field_name):
            st.error("Field name is required.")
        else:
            success, response = append_template_rule(
                {
                    "template_id": text_value(rule_template.get("template_id")),
                    "rule_scope": rule_scope,
                    "field_name": field_name,
                    "rule_type": rule_type,
                    "expected_values": expected_values,
                    "notes": notes,
                }
            )
            if success:
                st.success(f"Rule added: {response}")
                st.rerun()
            else:
                st.error(response)


def main() -> None:
    st.title(APP_TITLE)
    st.caption("Minimal rebuild: Neon-backed templates, single URL audit, and MVP-based video capture.")

    templates, rules, template_error = load_templates_and_rules()
    if template_error:
        st.error(template_error)
        return

    active_templates = [template for template in templates if template.get("active")]
    section = st.radio(
        "Section",
        options=["Audit URL", "Template Manager"],
        horizontal=True,
    )

    if section == "Template Manager":
        render_template_manager(templates, rules)
        return

    st.subheader("Single URL Audit")
    url_text = st.text_input("URL *", placeholder="https://www.jagran.com/example-article.html")
    selected_template = st.selectbox(
        "Template *",
        options=[None, *active_templates],
        format_func=lambda item: "Select a template" if item is None else template_option_label(item),
    )
    wait_seconds = st.slider("Wait after page load (seconds)", min_value=4, max_value=20, value=DEFAULT_WAIT_SECONDS)

    col1, col2 = st.columns(2)
    run_audit_clicked = col1.button("Run audit", use_container_width=True)
    capture_video_clicked = col2.button("Capture video interaction", use_container_width=True)

    normalized_url, url_error = normalize_url(url_text) if url_text else ("", "")
    if url_error and (run_audit_clicked or capture_video_clicked):
        st.error(url_error)
        return
    if selected_template is None and (run_audit_clicked or capture_video_clicked):
        st.error("Please select a template.")
        return

    selected_rules = [
        rule for rule in rules
        if text_value(rule.get("template_id")) == text_value((selected_template or {}).get("template_id"))
    ]

    if run_audit_clicked:
        with st.spinner("Running audit..."):
            result = capture_page_audit(normalized_url, wait_seconds=wait_seconds, headless=True)
        render_result_block("Audit Result", result, selected_rules)

    if capture_video_clicked:
        with st.spinner("Capturing video interaction..."):
            result = capture_video_event(normalized_url, headless=True)
        render_result_block("Video Interaction Result", result, selected_rules)


if __name__ == "__main__":
    main()
