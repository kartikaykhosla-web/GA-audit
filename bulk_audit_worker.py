import argparse
import json
import os
import re
import time
import uuid
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional
from urllib.parse import parse_qs, urlparse

import requests
from seleniumwire import webdriver
from selenium.webdriver.common.by import By
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service


SUPABASE_JOB_TABLE = "bulk_audit_jobs"
SUPABASE_RESULT_TABLE = "bulk_audit_results"
GA4_EVENT_PARAM_KEYS = ("en", "event_name")
FIELD_NAME_ALIASES = {
    "scroll_percent": ["scroll_percent", "scroll_percentage", "percent_scrolled"],
    "publish_date": ["publish_date", "tvc_publish_date"],
    "update_date": ["update_date", "tvc_update_date"],
}
VIDEO_EXECUTION_FIELDS = {
    "dynamic_video_embed_type",
    "player_type",
    "position_fold",
    "section_name",
    "video_orientation",
    "video_percent",
    "video_duration",
    "video_title",
}
VIDEO_PLAY_SELECTORS = [
    "video",
    "button[aria-label*='play' i]",
    "[role='button'][aria-label*='play' i]",
    ".vjs-big-play-button",
    ".jw-display-icon-container",
    ".jw-icon-playback",
    ".jw-button-container .jw-icon-playback",
    ".ytp-large-play-button",
    ".ytp-play-button",
    "[class*='play'][role='button']",
    "button[class*='play']",
    "[data-testid*='play']",
]


def utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def get_supabase_settings() -> Dict[str, str]:
    return {
        "url": os.environ.get("SUPABASE_URL", "").strip().rstrip("/"),
        "key": os.environ.get("SUPABASE_SERVICE_ROLE_KEY", "").strip(),
    }


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
        raise RuntimeError("SUPABASE_URL and SUPABASE_SERVICE_ROLE_KEY are required.")
    response = requests.request(
        method,
        f"{settings['url']}/rest/v1/{table}",
        headers=supabase_headers(prefer=prefer),
        params=params or {},
        json=payload,
        timeout=60,
    )
    if response.status_code >= 400:
        raise RuntimeError(f"Supabase {method} {table} failed: {response.status_code} {response.text}")
    if not response.text:
        return []
    try:
        return response.json()
    except Exception:
        return []


def update_job(job_id: str, values: dict):
    supabase_request(
        "PATCH",
        SUPABASE_JOB_TABLE,
        params={"job_id": f"eq.{job_id}"},
        payload=values,
        prefer="return=minimal",
    )


def load_job(job_id: str) -> dict:
    rows = supabase_request(
        "GET",
        SUPABASE_JOB_TABLE,
        params={"select": "*", "job_id": f"eq.{job_id}", "limit": "1"},
    )
    if not rows:
        raise RuntimeError(f"Bulk audit job not found: {job_id}")
    return rows[0]


def create_driver():
    options = Options()
    options.add_argument("--headless=new")
    options.add_argument("--disable-gpu")
    options.add_argument("--no-sandbox")
    options.add_argument("--disable-dev-shm-usage")
    options.add_argument("--disable-quic")
    options.add_argument("--disable-background-networking")
    options.add_argument("--disable-blink-features=AutomationControlled")
    options.add_argument("--disable-features=IsolateOrigins,site-per-process,BlockInsecurePrivateNetworkRequests")
    options.add_argument("--window-size=1365,1600")
    options.add_argument("--ignore-certificate-errors")
    options.add_argument(
        "--user-agent=Mozilla/5.0 (Windows NT 10.0; Win64; x64) "
        "AppleWebKit/537.36 (KHTML, like Gecko) Chrome/119.0.0.0 Safari/537.36"
    )
    options.set_capability("goog:loggingPrefs", {"performance": "ALL"})
    chrome_binary = os.environ.get("CHROME_BINARY") or os.environ.get("CHROME_PATH")
    if chrome_binary:
        options.binary_location = chrome_binary

    service = Service()
    driver = webdriver.Chrome(
        service=service,
        options=options,
        seleniumwire_options={
            "verify_ssl": False,
            "disable_encoding": True,
            "request_storage": "memory",
            "request_storage_max_size": 200,
        },
    )
    driver.scopes = [
        r".*google-analytics\.com/.*collect.*",
        r".*analytics\.google\.com/.*collect.*",
        r".*google\.com/ccm/collect.*",
        r".*googletagmanager\.com/.*",
        r".*scorecardresearch\.com/.*",
        r".*chartbeat\.net/.*ping.*",
    ]
    return driver


def install_datalayer_probe(driver):
    script = r"""
(() => {
  if (window.__gaAuditProbeInstalled) return;
  window.__gaAuditProbeInstalled = true;
  window.__gaAudit = window.__gaAudit || { pushes: [], state: {}, gtag: [], transportHits: [] };
  const clone = (value) => {
    try { return JSON.parse(JSON.stringify(value)); } catch (e) { return String(value); }
  };
  const asText = (data) => {
    try {
      if (data === null || data === undefined) return "";
      if (typeof data === "string") return data;
      if (typeof URLSearchParams !== "undefined" && data instanceof URLSearchParams) return data.toString();
      if (typeof FormData !== "undefined" && data instanceof FormData) {
        const pairs = [];
        data.forEach((entryValue, entryKey) => pairs.push(encodeURIComponent(entryKey) + "=" + encodeURIComponent(String(entryValue))));
        return pairs.join("&");
      }
      if (typeof Blob !== "undefined" && data instanceof Blob) return "[Blob size=" + data.size + "]";
      return String(data);
    } catch (e) {
      return "[unserializable]";
    }
  };
  const isGaUrl = (url) => {
    return typeof url === "string" && /(google-analytics\.com\/(g|j|r)\/collect|analytics\.google\.com\/g\/collect|google\.com\/ccm\/collect)/i.test(url);
  };
  const recordTransport = (api, url, method, body) => {
    try {
      if (!isGaUrl(String(url || ""))) return;
      window.__gaAudit.transportHits.push({
        timestamp: Date.now(),
        api,
        url: String(url || ""),
        method: String(method || "GET").toUpperCase(),
        bodyText: asText(body)
      });
    } catch (e) {}
  };
  const mergeState = (item) => {
    if (item && typeof item === 'object' && !Array.isArray(item)) {
      Object.assign(window.__gaAudit.state, clone(item));
    }
  };
  const hookDataLayer = () => {
    window.dataLayer = window.dataLayer || [];
    if (window.dataLayer.__gaAuditHooked) return;
    const originalPush = window.dataLayer.push;
    window.dataLayer.forEach((item) => {
      window.__gaAudit.pushes.push(clone(item));
      mergeState(item);
    });
    window.dataLayer.push = function() {
      Array.from(arguments).forEach((item) => {
        window.__gaAudit.pushes.push(clone(item));
        mergeState(item);
      });
      return originalPush.apply(window.dataLayer, arguments);
    };
    window.dataLayer.__gaAuditHooked = true;
  };
  const hookGtag = () => {
    const original = window.gtag;
    if (typeof original !== 'function' || original.__gaAuditHooked) return;
    window.gtag = function() {
      window.__gaAudit.gtag.push(clone(Array.from(arguments)));
      return original.apply(this, arguments);
    };
    window.gtag.__gaAuditHooked = true;
  };
  if (navigator && typeof navigator.sendBeacon === "function" && !navigator.sendBeacon.__gaAuditHooked) {
    const originalSendBeacon = navigator.sendBeacon.bind(navigator);
    navigator.sendBeacon = function(url, data) {
      recordTransport("sendBeacon", url, "POST", data);
      return originalSendBeacon(url, data);
    };
    navigator.sendBeacon.__gaAuditHooked = true;
  }
  if (typeof window.fetch === "function" && !window.fetch.__gaAuditHooked) {
    const originalFetch = window.fetch.bind(window);
    window.fetch = function(input, init) {
      const url = typeof input === "string" ? input : (input && input.url) || "";
      const method = (init && init.method) || (input && input.method) || "GET";
      const body = (init && init.body) || null;
      recordTransport("fetch", url, method, body);
      return originalFetch(input, init);
    };
    window.fetch.__gaAuditHooked = true;
  }
  if (window.XMLHttpRequest && window.XMLHttpRequest.prototype && !window.XMLHttpRequest.prototype.__gaAuditHooked) {
    const proto = window.XMLHttpRequest.prototype;
    const originalOpen = proto.open;
    const originalSend = proto.send;
    proto.open = function(method, url) {
      this.__gaAuditMeta = { method, url };
      return originalOpen.apply(this, arguments);
    };
    proto.send = function(body) {
      const meta = this.__gaAuditMeta || {};
      recordTransport("xhr", meta.url || "", meta.method || "GET", body);
      return originalSend.apply(this, arguments);
    };
    proto.__gaAuditHooked = true;
  }
  try {
    const proto = window.HTMLImageElement && window.HTMLImageElement.prototype;
    const descriptor = proto && Object.getOwnPropertyDescriptor(proto, "src");
    if (descriptor && descriptor.configurable && descriptor.set && !descriptor.set.__gaAuditHooked) {
      Object.defineProperty(proto, "src", {
        configurable: true,
        enumerable: descriptor.enumerable,
        get: descriptor.get,
        set: function(value) {
          recordTransport("image", value, "GET", "");
          return descriptor.set.call(this, value);
        }
      });
      descriptor.set.__gaAuditHooked = true;
    }
  } catch (e) {}
  hookDataLayer();
  hookGtag();
  window.setInterval(() => { hookDataLayer(); hookGtag(); }, 100);
})();
"""
    try:
        driver.execute_cdp_cmd("Page.addScriptToEvaluateOnNewDocument", {"source": script})
    except Exception:
        pass


def parse_query(url: str) -> Dict[str, str]:
    parsed = urlparse(url)
    values = {}
    for key, raw_values in parse_qs(parsed.query, keep_blank_values=True).items():
        if not raw_values:
            continue
        values[key] = str(raw_values[-1])
    return values


def parse_body(body_text: str) -> Dict[str, str]:
    text = str(body_text or "").strip()
    if not text or text.startswith("[Blob") or "byteLength" in text:
        return {}
    values = {}
    for key, raw_values in parse_qs(text, keep_blank_values=True).items():
        if not raw_values:
            continue
        values[key] = str(raw_values[-1])
    return values


def parse_ga_payloads(url: str, body_text: str = "") -> List[Dict[str, str]]:
    query_payload = parse_query(url)
    body_text = str(body_text or "").strip()
    if not body_text or body_text.startswith("[Blob") or "byteLength" in body_text:
        return [query_payload]

    lines = [line.strip() for line in body_text.splitlines() if line.strip()]
    if len(lines) > 1 and all("=" in line for line in lines):
        return [{**query_payload, **parse_body(line)} for line in lines]
    if "=" in body_text:
        return [{**query_payload, **parse_body(body_text)}]
    return [{**query_payload, "_body_text": body_text}]


def clean_ga_params(params: Dict[str, str]) -> Dict[str, str]:
    cleaned = {}
    for key, value in (params or {}).items():
        clean_key = key
        if key.startswith(("ep.", "up.", "epn.", "epf.", "upn.")):
            clean_key = key.split(".", 1)[1]
        cleaned[clean_key] = value
    return cleaned


def collect_ids_from_params(params: Dict[str, str], measurement_ids: List[str], container_ids: List[str]) -> None:
    tid = params.get("tid") or params.get("measurement_id") or params.get("measurementId") or ""
    if tid and tid not in measurement_ids:
        measurement_ids.append(tid)
    gtm = (
        params.get("ep.gtm_container_id")
        or params.get("gtm_container_id")
        or params.get("gtm")
        or params.get("container_id")
        or ""
    )
    if gtm and gtm not in container_ids:
        container_ids.append(gtm)


def build_ga_event_from_payload(params: Dict[str, str], status: str = "", url: str = "", source: str = "") -> dict:
    event_name = ""
    for key in GA4_EVENT_PARAM_KEYS:
        if params.get(key):
            event_name = normalize_event_name(params.get(key))
            break
    if not event_name and params.get("t") == "pageview":
        event_name = "page_view"
    return {
        "event_name": event_name or "collect",
        "params": clean_ga_params(params),
        "status": status,
        "url": url,
        "source": source,
    }


def build_ga_events_from_request(url: str, body_text: str = "", status: str = "", source: str = "") -> List[dict]:
    return [
        build_ga_event_from_payload(payload, status=status, url=url, source=source)
        for payload in parse_ga_payloads(url, body_text)
    ]


def is_ga_request(url: str) -> bool:
    host = urlparse(url).netloc.lower()
    path = urlparse(url).path.lower()
    if "google-analytics.com" in host and "collect" in path:
        return True
    if "analytics.google.com" in host and "collect" in path:
        return True
    if host.endswith("google.com") and path.endswith("/ccm/collect"):
        return True
    return False


def is_comscore_request(url: str) -> bool:
    host = urlparse(url).netloc.lower()
    return "scorecardresearch.com" in host or "sb.scorecardresearch.com" in host


def is_chartbeat_request(url: str) -> bool:
    parsed = urlparse(url)
    return "chartbeat.net" in parsed.netloc.lower() and "ping" in parsed.path.lower()


def normalize_event_name(name: str) -> str:
    text = str(name or "").strip()
    return "page_view" if text in {"pageview", "page_view"} else text


def template_requires_video_playback(rules: List[dict]) -> bool:
    for rule in rules or []:
        field_name = str(rule.get("field_name") or "").strip()
        if not field_name:
            continue
        if str(rule.get("rule_scope") or "").strip().lower() == "event":
            normalized_event = normalize_event_name(field_name).replace("_", "")
            if normalized_event.endswith("videointeraction"):
                return True
        elif str(rule.get("rule_scope") or "").strip().lower() == "execution":
            if normalize_dimension_name(field_name) in {
                normalize_dimension_name(value) for value in VIDEO_EXECUTION_FIELDS
            }:
                return True
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
                driver.execute_script("arguments[0].scrollIntoView({block:'center'});", element)
                time.sleep(0.2)
                driver.execute_script("arguments[0].click();", element)
                return True
            except Exception:
                continue
    return False


def trigger_video_playback(driver) -> bool:
    started = False
    try:
        driver.switch_to.default_content()
    except Exception:
        return False

    for percent in (20, 40, 60, 80):
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
            time.sleep(0.6)
        except Exception:
            pass
        started = _play_visible_videos_in_current_context(driver) or _click_video_controls_in_current_context(driver) or started
        if started:
            break

    try:
        frames = driver.find_elements(By.TAG_NAME, "iframe")
    except Exception:
        frames = []

    for frame in frames[:12]:
        try:
            driver.switch_to.default_content()
            driver.switch_to.frame(frame)
            frame_started = _play_visible_videos_in_current_context(driver) or _click_video_controls_in_current_context(driver)
            started = started or frame_started
        except Exception:
            continue
        finally:
            try:
                driver.switch_to.default_content()
            except Exception:
                pass

    return started


def extract_network(driver) -> dict:
    ga_events: List[dict] = []
    comscore_hits: List[dict] = []
    chartbeat_hits: List[dict] = []
    measurement_ids = []
    container_ids = []

    for request in getattr(driver, "requests", []) or []:
        url = getattr(request, "url", "") or ""
        params = parse_query(url)
        status_code = ""
        try:
            status_code = str(request.response.status_code) if request.response else ""
        except Exception:
            status_code = ""

        if is_ga_request(url):
            body_text = ""
            try:
                body = getattr(request, "body", b"") or b""
                body_text = body.decode("utf-8", errors="ignore") if isinstance(body, bytes) else str(body)
            except Exception:
                body_text = ""
            for payload in parse_ga_payloads(url, body_text):
                collect_ids_from_params(payload, measurement_ids, container_ids)
                ga_events.append(build_ga_event_from_payload(payload, status_code, url, "seleniumwire"))
        elif is_comscore_request(url):
            comscore_hits.append({"status": status_code, "params": params, "url": url})
        elif is_chartbeat_request(url):
            chartbeat_hits.append({"status": status_code, "params": params, "url": url})

    return {
        "ga_events": ga_events,
        "comscore_hits": comscore_hits,
        "chartbeat_hits": chartbeat_hits,
        "measurement_id": ", ".join(measurement_ids) or "Not found",
        "container_id": ", ".join(container_ids) or "Not found",
    }


def extract_performance_log_network(driver) -> dict:
    ga_events: List[dict] = []
    measurement_ids = []
    container_ids = []
    try:
        entries = driver.get_log("performance")
    except Exception:
        return {"ga_events": [], "measurement_id": "", "container_id": ""}

    for entry in entries or []:
        try:
            message = json.loads(entry.get("message", "{}")).get("message", {})
        except Exception:
            continue
        if message.get("method") != "Network.requestWillBeSent":
            continue
        request = message.get("params", {}).get("request", {})
        url = str(request.get("url") or "")
        if not is_ga_request(url):
            continue
        params = parse_query(url)
        body_text = str(request.get("postData") or "")
        for payload in parse_ga_payloads(url, body_text):
            collect_ids_from_params(payload, measurement_ids, container_ids)
            ga_events.append(build_ga_event_from_payload(payload, "", url, "performance_log"))

    return {
        "ga_events": ga_events,
        "measurement_id": ", ".join(measurement_ids),
        "container_id": ", ".join(container_ids),
    }


def extract_probe_transport(probe: dict) -> dict:
    ga_events: List[dict] = []
    measurement_ids = []
    container_ids = []
    for hit in probe.get("transportHits", []) or []:
        if not isinstance(hit, dict):
            continue
        url = str(hit.get("url") or "")
        if not is_ga_request(url):
            continue
        body_text = str(hit.get("bodyText") or "")
        for payload in parse_ga_payloads(url, body_text):
            collect_ids_from_params(payload, measurement_ids, container_ids)
            ga_events.append(build_ga_event_from_payload(payload, "Observed", url, f"probe_{hit.get('api') or 'transport'}"))
    return {
        "ga_events": ga_events,
        "measurement_id": ", ".join(measurement_ids),
        "container_id": ", ".join(container_ids),
    }


def extract_probe_gtag_events(probe: dict) -> List[dict]:
    events = []
    for call in probe.get("gtag", []) or []:
        if not isinstance(call, list) or len(call) < 2:
            continue
        if call[0] != "event":
            continue
        params = call[2] if len(call) > 2 and isinstance(call[2], dict) else {}
        events.append(
            {
                "event_name": normalize_event_name(call[1]),
                "params": params,
                "status": "Observed",
                "url": "",
                "source": "gtag",
            }
        )
    return events


def merge_ga_events(*groups: List[dict]) -> List[dict]:
    seen = set()
    merged = []
    for group in groups:
        for event in group or []:
            key = (
                event.get("event_name"),
                json.dumps(event.get("params") or {}, sort_keys=True, ensure_ascii=False),
                event.get("source"),
            )
            if key in seen:
                continue
            seen.add(key)
            merged.append(event)
    return merged


def join_nonempty_unique(*values: str) -> str:
    output = []
    for value in values:
        for item in str(value or "").split(","):
            text = item.strip()
            if text and text != "Not found" and text not in output:
                output.append(text)
    return ", ".join(output) or "Not found"


def normalize_compare_text(value: Any) -> str:
    return re.sub(r"\s+", " ", str(value or "").strip()).strip().lower()


def normalize_dimension_name(value: Any) -> str:
    name = str(value or "").strip()
    for prefix in ("tvc_", "user.", "ep.", "epn.", "epf.", "up.", "upn."):
        if name.startswith(prefix):
            name = name[len(prefix):]
            break
    return name.replace("_", "").lower()


def normalized_field_candidates(field_name: str) -> List[str]:
    raw = str(field_name or "").strip()
    candidates = [raw]
    for alias in FIELD_NAME_ALIASES.get(raw, []):
        if alias not in candidates:
            candidates.append(alias)
    normalized = []
    seen = set()
    for candidate in candidates:
        key = normalize_dimension_name(candidate)
        if key and key not in seen:
            seen.add(key)
            normalized.append(key)
    return normalized


def split_actual_tokens(value: Any) -> List[str]:
    text = str(value or "").strip()
    if not text:
        return []
    tokens: List[str] = []
    for piece in re.split(r"[|,\n\r;]+", text):
        cleaned = normalize_compare_text(piece)
        if cleaned:
            tokens.append(cleaned)
    return tokens


def find_payload_value(payload: Dict[str, Any], field_name: str) -> Any:
    if not isinstance(payload, dict):
        return None
    target = str(field_name or "").strip()
    if target in payload:
        return payload.get(target)
    target_candidates = set(normalized_field_candidates(target))
    for key, value in payload.items():
        if normalize_dimension_name(key) in target_candidates:
            return value
    return None


def collect_event_field_values(events: List[dict], field_name: str) -> List[str]:
    target_candidates = set(normalized_field_candidates(field_name))
    values: List[str] = []
    for event in events or []:
        if not isinstance(event, dict):
            continue
        payload = event.get("params") or {}
        if not isinstance(payload, dict):
            continue
        for key, value in payload.items():
            if normalize_dimension_name(key) not in target_candidates:
                continue
            text = str(value or "").strip()
            if text and text not in values:
                values.append(text)
    return values


def resolve_field_value(field_name: str, execution_values: Dict[str, Any], ga_events: List[dict]) -> Any:
    direct_value = find_payload_value(execution_values, field_name)
    if direct_value not in (None, ""):
        return direct_value
    event_values = collect_event_field_values(ga_events, field_name)
    if not event_values:
        return None
    if len(event_values) == 1:
        return event_values[0]
    return ", ".join(event_values)


def parse_percent_value(value: Any) -> Optional[float]:
    text = str(value or "").strip()
    if not text:
        return None
    match = re.search(r"\d+(?:\.\d+)?", text)
    if not match:
        return None
    try:
        return float(match.group(0))
    except ValueError:
        return None


def has_video_progress_event(events: List[dict], minimum_percent: float = 25.0) -> bool:
    for event in events or []:
        if normalize_event_name(event.get("event_name") or "") != "video_interaction":
            continue
        params = event.get("params") or {}
        if not isinstance(params, dict):
            continue
        video_percent = find_payload_value(params, "video_percent")
        percent_value = parse_percent_value(video_percent)
        if percent_value is not None and percent_value >= minimum_percent:
            return True
    return False


def wait_for_video_progress(driver, timeout_seconds: int = 60, minimum_percent: float = 25.0) -> bool:
    deadline = time.time() + max(1, int(timeout_seconds or 0))
    while time.time() < deadline:
        probe = get_probe_payload(driver)
        network = extract_network(driver)
        transport_network = extract_probe_transport(probe)
        gtag_events = extract_probe_gtag_events(probe)
        ga_events = merge_ga_events(
            network["ga_events"],
            transport_network["ga_events"],
            gtag_events,
        )
        if has_video_progress_event(ga_events, minimum_percent=minimum_percent):
            return True
        time.sleep(2)
    return False


def select_primary_execution_event(ga_events: List[dict]) -> Optional[dict]:
    if not ga_events:
        return None
    preferred_names = ("page_view", "pageview")
    preferred_sources = ("seleniumwire", "performance_log", "probe_sendBeacon", "probe_fetch", "probe_xhr", "probe_image", "gtag")
    for event_name in preferred_names:
        for source in preferred_sources:
            for event in ga_events:
                if normalize_event_name(event.get("event_name") or "") == event_name and str(event.get("source") or "") == source:
                    return event
        for event in ga_events:
            if normalize_event_name(event.get("event_name") or "") == event_name:
                return event
    return ga_events[0]


def build_computed_state(data_layer: List[dict], selected_index: int) -> Dict[str, Any]:
    state: Dict[str, Any] = {}
    for item in (data_layer or [])[: selected_index + 1]:
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if value is None:
                state.pop(key, None)
            else:
                state[key] = value
    return state


def matching_score_for_snapshot(candidate_payload: Dict[str, Any], reference_payload: Dict[str, Any]) -> tuple:
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


def find_matching_datalayer_index(data_layer: List[dict], selected_event: Dict[str, Any]) -> Optional[int]:
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
        overlap_count, key_count = matching_score_for_snapshot(item, selected_event)
        score = (overlap_count, key_count, index)
        if score >= best_score:
            best_index = index
            best_score = score
    return best_index


def merged_event_payload(event: Dict[str, Any]) -> Dict[str, Any]:
    payload: Dict[str, Any] = {}
    params = event.get("params") or {}
    if isinstance(params, dict):
        payload.update(params)
    return payload


def best_matching_event(selected_event: Dict[str, Any], events: List[dict]) -> Optional[dict]:
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
        overlap_count, key_count = matching_score_for_snapshot(payload, selected_event)
        score = (overlap_count, key_count, index)
        if score >= best_score:
            best_event = event
            best_score = score
    return best_event or events[-1]


def get_probe_payload(driver) -> dict:
    try:
        payload = driver.execute_script("return window.__gaAudit || {pushes: [], state: {}, gtag: []};")
        return payload if isinstance(payload, dict) else {"pushes": [], "state": {}, "gtag": []}
    except Exception:
        return {"pushes": [], "state": {}, "gtag": []}


def build_event_summary(ga_events: List[dict]) -> List[dict]:
    grouped: Dict[str, dict] = {}
    for event in ga_events:
        name = normalize_event_name(event.get("event_name") or "collect")
        group = grouped.setdefault(name, {"event_name": name, "times_fired": 0, "values": {}})
        group["times_fired"] += 1
        for key, value in (event.get("params") or {}).items():
            if key not in group["values"]:
                group["values"][key] = []
            if value not in group["values"][key]:
                group["values"][key].append(value)
    return list(grouped.values())


def parse_expected_values(value: str) -> List[str]:
    return [token.strip() for token in str(value or "").split("|") if token.strip()]


def parse_regex_patterns(value: str) -> List[str]:
    text = str(value or "").strip()
    if not text:
        return []
    return [token.strip() for token in re.split(r"[\n\r]+", text) if token.strip()]


def normalize_datetime_candidate(value: str) -> str:
    text = str(value or "").strip()
    text = text.strip("\"'()[]{}")
    text = re.sub(r"\s+", " ", text)
    return text


def is_valid_iso_datetime(value: str) -> bool:
    text = normalize_datetime_candidate(value)
    if not text:
        return False
    try:
        datetime.fromisoformat(text.replace("Z", "+00:00"))
        return True
    except ValueError:
        return False


def validate_rule(rule: dict, actual: Any) -> Optional[str]:
    rule_type = str(rule.get("rule_type") or "").strip()
    field_name = str(rule.get("field_name") or "").strip()
    normalized_field_name = normalize_dimension_name(field_name)
    expected = parse_expected_values(rule.get("expected_values"))
    actual_text = "" if actual is None else str(actual).strip()
    actual_normalized = normalize_compare_text(actual_text)
    actual_tokens = split_actual_tokens(actual_text)
    if rule_type == "optional":
        return None
    if rule_type == "required":
        return None if actual_text else f"{field_name} missing"
    if not actual_text:
        return f"{field_name} missing"
    if rule_type == "exact":
        expected_normalized = [normalize_compare_text(item) for item in expected]
        matched = actual_normalized in expected_normalized or any(token in expected_normalized for token in actual_tokens)
        if not matched and normalized_field_name == "scrollpercent":
            expected_scrolls = {token.replace(" ", "") for token in expected_normalized}
            actual_scrolls = {token.replace(" ", "") for token in actual_tokens + [actual_normalized]}
            matched = bool(expected_scrolls & actual_scrolls)
        return None if matched else f"{field_name} expected {expected}, got {actual_text}"
    if rule_type == "one_of":
        expected_normalized = [normalize_compare_text(item) for item in expected]
        matched = actual_normalized in expected_normalized or any(token in expected_normalized for token in actual_tokens)
        if not matched and normalized_field_name == "scrollpercent":
            expected_scrolls = {token.replace(" ", "") for token in expected_normalized}
            actual_scrolls = {token.replace(" ", "") for token in actual_tokens + [actual_normalized]}
            matched = bool(expected_scrolls & actual_scrolls)
        return None if matched else f"{field_name} expected one of {expected}, got {actual_text}"
    if rule_type == "contains":
        return None if any(normalize_compare_text(item) in actual_normalized for item in expected) else f"{field_name} expected to contain {expected}, got {actual_text}"
    if rule_type == "regex":
        invalid_patterns = []
        actual_candidates = [actual_text]
        actual_candidates.extend([token.strip() for token in re.split(r"[,\n\r;|]+", actual_text) if token.strip()])
        normalized_candidates = [normalize_datetime_candidate(candidate) for candidate in actual_candidates if str(candidate).strip()]
        for pattern in parse_regex_patterns(rule.get("expected_values")):
            if not pattern:
                continue
            try:
                if any(re.search(pattern, candidate) for candidate in actual_candidates + normalized_candidates):
                    return None
            except re.error:
                invalid_patterns.append(pattern)
        if invalid_patterns:
            return f"{field_name} has invalid regex in template: {invalid_patterns[0]}"
        if normalized_field_name in {"publishdate", "updatedate"} and any(is_valid_iso_datetime(candidate) for candidate in actual_candidates + normalized_candidates):
            return None
        return f"{field_name} did not match regex"
    return None


def audit_url(plan_row: dict, wait_seconds: int) -> dict:
    template = plan_row.get("template") or {}
    rules = plan_row.get("rules") or []
    sample_url = plan_row.get("sample_url") or ""
    if plan_row.get("sample_error") or not sample_url:
        raise RuntimeError(plan_row.get("sample_error") or "No sample URL available.")

    start = time.time()
    driver = create_driver()
    requires_video_playback = template_requires_video_playback(rules)
    try:
        try:
            del driver.requests
        except Exception:
            pass
        try:
            driver.get_log("performance")
        except Exception:
            pass
        install_datalayer_probe(driver)
        driver.get(sample_url)
        try:
            driver.execute_script(
                """
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
                """
            )
        except Exception:
            pass
        try:
            for percent in (0, 25, 50, 75, 100):
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
                time.sleep(0.8)
        except Exception:
            pass
        base_wait_seconds = max(1, int(wait_seconds or 8))
        time.sleep(min(3, base_wait_seconds))
        if requires_video_playback:
            try:
                trigger_video_playback(driver)
            except Exception:
                pass
            wait_for_video_progress(driver, timeout_seconds=max(base_wait_seconds, 60), minimum_percent=25.0)
        else:
            remaining_wait = max(0, base_wait_seconds - min(3, base_wait_seconds))
            if remaining_wait:
                time.sleep(remaining_wait)
        probe = get_probe_payload(driver)
        network = extract_network(driver)
        performance_network = extract_performance_log_network(driver)
        transport_network = extract_probe_transport(probe)
        gtag_events = extract_probe_gtag_events(probe)
    finally:
        try:
            driver.quit()
        except Exception:
            pass

    data_layer = probe.get("pushes") if isinstance(probe.get("pushes"), list) else []
    state = probe.get("state") if isinstance(probe.get("state"), dict) else {}
    ga_events = merge_ga_events(
        network["ga_events"],
        performance_network["ga_events"],
        transport_network["ga_events"],
        gtag_events,
    )
    selected_event = {}
    if isinstance(data_layer, list):
        for item in reversed(data_layer):
            if not isinstance(item, dict):
                continue
            if normalize_event_name(item.get("event")) in {"pageview", "page_view"}:
                selected_event = item
                break
    selected_index = None
    if selected_event:
        selected_index = find_matching_datalayer_index(data_layer, selected_event)
        if selected_index is None and data_layer:
            selected_index = len(data_layer) - 1
    computed_state = (
        build_computed_state(data_layer, selected_index)
        if selected_index is not None
        else dict(state)
    )
    event_names = [event.get("event_name") for event in ga_events if event.get("event_name")]
    event_set = sorted({name for name in event_names if name})
    pageview_triggered = "page_view" in event_set
    pageview_source = "Not fired"
    if pageview_triggered:
        pageview_sources = {
            str(event.get("source") or "")
            for event in ga_events
            if normalize_event_name(event.get("event_name") or "") == "page_view"
        }
        if any(source in {"seleniumwire", "performance_log"} or source.startswith("probe_") for source in pageview_sources):
            pageview_source = "Network"
        elif "gtag" in pageview_sources:
            pageview_source = "Execution"
        else:
            pageview_source = "Observed"
    primary_event = (
        best_matching_event(selected_event, ga_events)
        if selected_event
        else select_primary_execution_event(ga_events)
    )
    primary_params = dict((primary_event or {}).get("params") or {})
    execution_values = {**computed_state, **primary_params}
    measurement_id = join_nonempty_unique(network["measurement_id"], performance_network["measurement_id"], transport_network["measurement_id"])
    container_id = join_nonempty_unique(network["container_id"], performance_network["container_id"], transport_network["container_id"])

    execution_failures = []
    event_failures = []
    for rule in rules:
        scope = str(rule.get("rule_scope") or "").strip()
        field_name = str(rule.get("field_name") or "").strip()
        if scope == "event":
            if field_name not in event_set:
                event_failures.append(f"Event {field_name} not fired")
        elif scope == "execution":
            failure = validate_rule(rule, resolve_field_value(field_name, execution_values, ga_events))
            if failure:
                execution_failures.append(failure)

    ga_present = bool(ga_events)
    issues = []
    if not ga_present:
        issues.append("GA4 collect hit not observed")
    if not pageview_triggered:
        issues.append("page_view not observed in GA4 capture")
    issues.extend(execution_failures[:5])
    issues.extend(event_failures[:5])

    audit_outcome = "Issue" if issues else "Pass"
    return {
        "domain": plan_row.get("domain_name") or "",
        "template_name": template.get("template_name") or plan_row.get("template_name") or "Unnamed template",
        "sample_url": sample_url,
        "audit_outcome": audit_outcome,
        "implementation_status": "PASS" if audit_outcome == "Pass" else "ISSUE",
        "pageview_triggered": pageview_triggered,
        "pageview_source": pageview_source,
        "ga_present": ga_present,
        "events_count": len(event_set),
        "events_fired": ", ".join(event_set) or "None",
        "container_id": container_id,
        "measurement_id": measurement_id,
        "comscore_present": bool(network["comscore_hits"]),
        "chartbeat_present": bool(network["chartbeat_hits"]),
        "issues": "; ".join(issues) or "None",
        "execution_failures": execution_failures,
        "event_failures": event_failures,
        "audit_duration_seconds": round(time.time() - start, 2),
        "detail_payload": {
            "execution_values": execution_values,
            "events": build_event_summary(ga_events),
            "comscore_hits": network["comscore_hits"][:5],
            "chartbeat_hits": network["chartbeat_hits"][:5],
            "dataLayer_state": state,
        },
    }


def insert_result(job_id: str, plan_row: dict, result: dict):
    template = plan_row.get("template") or {}
    row = {
        "result_id": f"res_{uuid.uuid4().hex}",
        "job_id": job_id,
        "template_id": str(template.get("template_id") or plan_row.get("template_id") or ""),
        "template_name": result.get("template_name") or "",
        "sample_url": result.get("sample_url") or "",
        "audit_outcome": result.get("audit_outcome") or "",
        "implementation_status": result.get("implementation_status") or "",
        "ga_present": bool(result.get("ga_present")),
        "pageview_triggered": bool(result.get("pageview_triggered")),
        "pageview_source": result.get("pageview_source") or "",
        "events_count": int(result.get("events_count") or 0),
        "events_fired": result.get("events_fired") or "",
        "measurement_id": result.get("measurement_id") or "",
        "container_id": result.get("container_id") or "",
        "comscore_present": bool(result.get("comscore_present")),
        "chartbeat_present": bool(result.get("chartbeat_present")),
        "issues": result.get("issues") or "",
        "result_json": result,
    }
    supabase_request("POST", SUPABASE_RESULT_TABLE, payload=row, prefer="return=minimal")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--job-id", required=True)
    args = parser.parse_args()

    job = load_job(args.job_id)
    payload = job.get("payload") or {}
    if isinstance(payload, str):
        payload = json.loads(payload)
    plan = payload.get("plan") or []
    wait_seconds = int(payload.get("wait_seconds") or 8)
    total = len(plan)

    update_job(args.job_id, {"status": "running", "started_at": utc_now(), "total_count": total})
    completed = 0
    failed = 0
    try:
        for plan_row in plan:
            try:
                result = audit_url(plan_row, wait_seconds)
            except Exception as exc:
                failed += 1
                template = plan_row.get("template") or {}
                result = {
                    "domain": payload.get("domain_name") or "",
                    "template_name": template.get("template_name") or plan_row.get("template_name") or "Unnamed template",
                    "sample_url": plan_row.get("sample_url") or "",
                    "audit_outcome": "Issue",
                    "implementation_status": "ERROR",
                    "pageview_triggered": False,
                    "pageview_source": "Not tested",
                    "ga_present": False,
                    "events_count": 0,
                    "events_fired": "None",
                    "container_id": "Not found",
                    "measurement_id": "Not found",
                    "comscore_present": False,
                    "chartbeat_present": False,
                    "issues": str(exc),
                    "execution_failures": [],
                    "event_failures": [],
                    "audit_duration_seconds": 0,
                    "detail_payload": {},
                }
            insert_result(args.job_id, plan_row, result)
            completed += 1
            update_job(args.job_id, {"completed_count": completed, "failed_count": failed})
        update_job(args.job_id, {"status": "completed", "completed_at": utc_now(), "completed_count": completed, "failed_count": failed})
    except Exception as exc:
        update_job(args.job_id, {"status": "failed", "error_message": str(exc), "completed_at": utc_now(), "completed_count": completed, "failed_count": failed})
        raise


if __name__ == "__main__":
    main()
