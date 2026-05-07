import json
from urllib.parse import parse_qs, urlparse


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
