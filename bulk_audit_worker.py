import argparse
import json
import os
import time
import uuid
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional
from urllib.parse import parse_qs, urlparse, unquote_plus

import requests
from seleniumwire import webdriver
from selenium.webdriver.chrome.options import Options
from selenium.webdriver.chrome.service import Service


SUPABASE_JOB_TABLE = "bulk_audit_jobs"
SUPABASE_RESULT_TABLE = "bulk_audit_results"
GA4_EVENT_PARAM_KEYS = ("en", "event_name")


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
    options.add_argument("--window-size=1365,1600")
    options.add_argument("--ignore-certificate-errors")
    options.add_argument("--disable-blink-features=AutomationControlled")
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
  window.__gaAudit = window.__gaAudit || { pushes: [], state: {}, gtag: [] };
  const clone = (value) => {
    try { return JSON.parse(JSON.stringify(value)); } catch (e) { return String(value); }
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
        values[key] = unquote_plus(str(raw_values[-1]))
    return values


def is_ga_request(url: str) -> bool:
    host = urlparse(url).netloc.lower()
    path = urlparse(url).path.lower()
    return "google-analytics.com" in host and "collect" in path


def is_comscore_request(url: str) -> bool:
    host = urlparse(url).netloc.lower()
    return "scorecardresearch.com" in host or "sb.scorecardresearch.com" in host


def is_chartbeat_request(url: str) -> bool:
    parsed = urlparse(url)
    return "chartbeat.net" in parsed.netloc.lower() and "ping" in parsed.path.lower()


def normalize_event_name(name: str) -> str:
    text = str(name or "").strip()
    return "page_view" if text in {"pageview", "page_view"} else text


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
            event_name = ""
            for key in GA4_EVENT_PARAM_KEYS:
                if params.get(key):
                    event_name = normalize_event_name(params.get(key))
                    break
            if not event_name and params.get("t") == "pageview":
                event_name = "page_view"
            tid = params.get("tid") or params.get("measurement_id") or ""
            if tid and tid not in measurement_ids:
                measurement_ids.append(tid)
            gtm = params.get("ep.gtm_container_id") or params.get("gtm") or params.get("gtm_container_id") or ""
            if gtm and gtm not in container_ids:
                container_ids.append(gtm)
            clean_params = {}
            for key, value in params.items():
                clean_key = key
                if key.startswith("ep."):
                    clean_key = key[3:]
                elif key.startswith("up."):
                    clean_key = key[3:]
                clean_params[clean_key] = value
            ga_events.append(
                {
                    "event_name": event_name or "collect",
                    "params": clean_params,
                    "status": status_code,
                    "url": url,
                }
            )
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


def validate_rule(rule: dict, actual: Any) -> Optional[str]:
    rule_type = str(rule.get("rule_type") or "").strip()
    expected = parse_expected_values(rule.get("expected_values"))
    actual_text = "" if actual is None else str(actual).strip()
    if rule_type == "optional":
        return None
    if rule_type == "required":
        return None if actual_text else f"{rule.get('field_name')} missing"
    if not actual_text:
        return f"{rule.get('field_name')} missing"
    if rule_type == "exact":
        return None if any(actual_text == item for item in expected) else f"{rule.get('field_name')} expected {expected}, got {actual_text}"
    if rule_type == "one_of":
        return None if actual_text in expected else f"{rule.get('field_name')} expected one of {expected}, got {actual_text}"
    if rule_type == "contains":
        return None if any(item in actual_text for item in expected) else f"{rule.get('field_name')} expected to contain {expected}, got {actual_text}"
    if rule_type == "regex":
        import re
        return None if any(re.search(pattern, actual_text) for pattern in expected if pattern) else f"{rule.get('field_name')} did not match regex"
    return None


def audit_url(plan_row: dict, wait_seconds: int) -> dict:
    template = plan_row.get("template") or {}
    rules = plan_row.get("rules") or []
    sample_url = plan_row.get("sample_url") or ""
    if plan_row.get("sample_error") or not sample_url:
        raise RuntimeError(plan_row.get("sample_error") or "No sample URL available.")

    start = time.time()
    driver = create_driver()
    try:
        install_datalayer_probe(driver)
        driver.get(sample_url)
        time.sleep(max(1, int(wait_seconds or 8)))
        probe = get_probe_payload(driver)
        network = extract_network(driver)
    finally:
        try:
            driver.quit()
        except Exception:
            pass

    state = probe.get("state") if isinstance(probe.get("state"), dict) else {}
    ga_events = network["ga_events"]
    event_names = [event.get("event_name") for event in ga_events if event.get("event_name")]
    event_set = sorted({name for name in event_names if name})
    pageview_triggered = "page_view" in event_set
    pageview_source = "Network" if pageview_triggered else "Not fired"
    latest_params = {}
    for event in ga_events:
        latest_params.update(event.get("params") or {})
    execution_values = {**state, **latest_params}

    execution_failures = []
    event_failures = []
    for rule in rules:
        scope = str(rule.get("rule_scope") or "").strip()
        field_name = str(rule.get("field_name") or "").strip()
        if scope == "event":
            if field_name not in event_set:
                event_failures.append(f"Event {field_name} not fired")
        elif scope == "execution":
            failure = validate_rule(rule, execution_values.get(field_name))
            if failure:
                execution_failures.append(failure)

    ga_present = bool(ga_events)
    issues = []
    if not ga_present:
        issues.append("GA4 collect hit not observed")
    if not pageview_triggered:
        issues.append("page_view not observed in GA4 network")
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
        "container_id": network["container_id"],
        "measurement_id": network["measurement_id"],
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

