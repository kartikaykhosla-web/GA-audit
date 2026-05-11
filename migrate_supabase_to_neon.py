import json
import os
from typing import Any, Dict, Iterable, List

import psycopg
import requests
from psycopg.rows import dict_row
from psycopg.types.json import Jsonb


SUPABASE_TABLES = [
    "ga_audit_templates",
    "ga_audit_template_rules",
    "ga_audit_logs",
    "bulk_audit_jobs",
    "bulk_audit_results",
]

SCHEMA_SQL = """
CREATE TABLE IF NOT EXISTS ga_audit_templates (
    template_id text PRIMARY KEY,
    template_name text,
    domain_name text,
    measurement_id text,
    container_id text,
    url_pattern text,
    active boolean DEFAULT true,
    created_by text,
    created_at text
);

CREATE TABLE IF NOT EXISTS ga_audit_template_rules (
    rule_id text PRIMARY KEY,
    template_id text,
    rule_scope text,
    field_name text,
    rule_type text,
    expected_values text,
    notes text,
    created_by text,
    created_at text
);

CREATE TABLE IF NOT EXISTS ga_audit_logs (
    id bigserial PRIMARY KEY,
    date text,
    email_id text,
    url_checked text,
    pageview_trigger_found boolean,
    execution_custom_dimensions text,
    execution_dimensions jsonb,
    created_at text DEFAULT now()::text
);

CREATE TABLE IF NOT EXISTS bulk_audit_jobs (
    job_id text PRIMARY KEY,
    domain_name text,
    status text,
    total_count integer DEFAULT 0,
    completed_count integer DEFAULT 0,
    failed_count integer DEFAULT 0,
    requested_by text,
    payload jsonb,
    error_message text,
    created_at text DEFAULT now()::text,
    started_at text,
    completed_at text
);

CREATE TABLE IF NOT EXISTS bulk_audit_results (
    result_id text PRIMARY KEY,
    job_id text,
    template_id text,
    template_name text,
    sample_url text,
    audit_outcome text,
    implementation_status text,
    ga_present boolean,
    pageview_triggered boolean,
    pageview_source text,
    events_count integer DEFAULT 0,
    events_fired text,
    measurement_id text,
    container_id text,
    comscore_present boolean,
    chartbeat_present boolean,
    issues text,
    result_json jsonb,
    created_at text DEFAULT now()::text
);
"""


def env(name: str) -> str:
    return str(os.environ.get(name) or "").strip()


def supabase_headers() -> Dict[str, str]:
    key = env("SUPABASE_SERVICE_ROLE_KEY") or env("SUPABASE_ANON_KEY") or env("SUPABASE_KEY")
    return {
        "apikey": key,
        "Authorization": f"Bearer {key}",
    }


def fetch_supabase_table(table: str) -> List[dict]:
    base_url = env("SUPABASE_URL").rstrip("/")
    if not base_url or not supabase_headers()["apikey"]:
        raise RuntimeError("SUPABASE_URL and SUPABASE_SERVICE_ROLE_KEY are required.")

    rows = []
    offset = 0
    page_size = 1000
    while True:
        response = requests.get(
            f"{base_url}/rest/v1/{table}",
            headers=supabase_headers(),
            params={
                "select": "*",
                "limit": str(page_size),
                "offset": str(offset),
            },
            timeout=60,
        )
        if response.status_code >= 400:
            raise RuntimeError(f"Supabase GET {table} failed: {response.status_code} {response.text}")
        page = response.json()
        rows.extend(page)
        if len(page) < page_size:
            return rows
        offset += page_size


def neon_url() -> str:
    value = env("NEON_DATABASE_URL") or env("DATABASE_URL") or env("POSTGRES_URL")
    if not value:
        raise RuntimeError("NEON_DATABASE_URL or DATABASE_URL is required.")
    return value


def jsonb_value(value: Any):
    if value in ("", None):
        return Jsonb({})
    if isinstance(value, str):
        try:
            return Jsonb(json.loads(value))
        except Exception:
            return Jsonb(value)
    return Jsonb(value)


def text_value(value: Any) -> str:
    return "" if value is None else str(value)


def bool_value(value: Any) -> bool:
    if isinstance(value, bool):
        return value
    return str(value or "").strip().lower() in {"true", "1", "yes"}


def int_value(value: Any) -> int:
    try:
        return int(float(str(value or "0").strip() or "0"))
    except Exception:
        return 0


def insert_rows(conn, table: str, rows: Iterable[dict]) -> int:
    rows = list(rows)
    if not rows:
        return 0
    with conn.cursor() as cur:
        if table == "ga_audit_templates":
            cur.executemany(
                """
                INSERT INTO ga_audit_templates (
                    template_id, template_name, domain_name, measurement_id,
                    container_id, url_pattern, active, created_by, created_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (template_id) DO UPDATE SET
                    template_name = EXCLUDED.template_name,
                    domain_name = EXCLUDED.domain_name,
                    measurement_id = EXCLUDED.measurement_id,
                    container_id = EXCLUDED.container_id,
                    url_pattern = EXCLUDED.url_pattern,
                    active = EXCLUDED.active,
                    created_by = EXCLUDED.created_by,
                    created_at = EXCLUDED.created_at
                """,
                [
                    (
                        text_value(row.get("template_id")),
                        text_value(row.get("template_name")),
                        text_value(row.get("domain_name")),
                        text_value(row.get("measurement_id")),
                        text_value(row.get("container_id")),
                        text_value(row.get("url_pattern")),
                        bool_value(row.get("active", True)),
                        text_value(row.get("created_by")),
                        text_value(row.get("created_at")),
                    )
                    for row in rows
                ],
            )
        elif table == "ga_audit_template_rules":
            cur.executemany(
                """
                INSERT INTO ga_audit_template_rules (
                    rule_id, template_id, rule_scope, field_name, rule_type,
                    expected_values, notes, created_by, created_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (rule_id) DO UPDATE SET
                    template_id = EXCLUDED.template_id,
                    rule_scope = EXCLUDED.rule_scope,
                    field_name = EXCLUDED.field_name,
                    rule_type = EXCLUDED.rule_type,
                    expected_values = EXCLUDED.expected_values,
                    notes = EXCLUDED.notes,
                    created_by = EXCLUDED.created_by,
                    created_at = EXCLUDED.created_at
                """,
                [
                    (
                        text_value(row.get("rule_id")),
                        text_value(row.get("template_id")),
                        text_value(row.get("rule_scope")),
                        text_value(row.get("field_name")),
                        text_value(row.get("rule_type")),
                        text_value(row.get("expected_values")),
                        text_value(row.get("notes")),
                        text_value(row.get("created_by")),
                        text_value(row.get("created_at")),
                    )
                    for row in rows
                ],
            )
        elif table == "ga_audit_logs":
            cur.executemany(
                """
                INSERT INTO ga_audit_logs (
                    date, email_id, url_checked, pageview_trigger_found,
                    execution_custom_dimensions, execution_dimensions, created_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s)
                """,
                [
                    (
                        text_value(row.get("date")),
                        text_value(row.get("email_id")),
                        text_value(row.get("url_checked")),
                        bool_value(row.get("pageview_trigger_found")),
                        text_value(row.get("execution_custom_dimensions")),
                        jsonb_value(row.get("execution_dimensions")),
                        text_value(row.get("created_at")),
                    )
                    for row in rows
                ],
            )
        elif table == "bulk_audit_jobs":
            cur.executemany(
                """
                INSERT INTO bulk_audit_jobs (
                    job_id, domain_name, status, total_count, completed_count,
                    failed_count, requested_by, payload, error_message,
                    created_at, started_at, completed_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (job_id) DO UPDATE SET
                    domain_name = EXCLUDED.domain_name,
                    status = EXCLUDED.status,
                    total_count = EXCLUDED.total_count,
                    completed_count = EXCLUDED.completed_count,
                    failed_count = EXCLUDED.failed_count,
                    requested_by = EXCLUDED.requested_by,
                    payload = EXCLUDED.payload,
                    error_message = EXCLUDED.error_message,
                    created_at = EXCLUDED.created_at,
                    started_at = EXCLUDED.started_at,
                    completed_at = EXCLUDED.completed_at
                """,
                [
                    (
                        text_value(row.get("job_id")),
                        text_value(row.get("domain_name")),
                        text_value(row.get("status")),
                        int_value(row.get("total_count")),
                        int_value(row.get("completed_count")),
                        int_value(row.get("failed_count")),
                        text_value(row.get("requested_by")),
                        jsonb_value(row.get("payload")),
                        text_value(row.get("error_message")),
                        text_value(row.get("created_at")),
                        text_value(row.get("started_at")),
                        text_value(row.get("completed_at")),
                    )
                    for row in rows
                ],
            )
        elif table == "bulk_audit_results":
            cur.executemany(
                """
                INSERT INTO bulk_audit_results (
                    result_id, job_id, template_id, template_name, sample_url,
                    audit_outcome, implementation_status, ga_present,
                    pageview_triggered, pageview_source, events_count,
                    events_fired, measurement_id, container_id,
                    comscore_present, chartbeat_present, issues,
                    result_json, created_at
                )
                VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s, %s)
                ON CONFLICT (result_id) DO UPDATE SET
                    job_id = EXCLUDED.job_id,
                    template_id = EXCLUDED.template_id,
                    template_name = EXCLUDED.template_name,
                    sample_url = EXCLUDED.sample_url,
                    audit_outcome = EXCLUDED.audit_outcome,
                    implementation_status = EXCLUDED.implementation_status,
                    ga_present = EXCLUDED.ga_present,
                    pageview_triggered = EXCLUDED.pageview_triggered,
                    pageview_source = EXCLUDED.pageview_source,
                    events_count = EXCLUDED.events_count,
                    events_fired = EXCLUDED.events_fired,
                    measurement_id = EXCLUDED.measurement_id,
                    container_id = EXCLUDED.container_id,
                    comscore_present = EXCLUDED.comscore_present,
                    chartbeat_present = EXCLUDED.chartbeat_present,
                    issues = EXCLUDED.issues,
                    result_json = EXCLUDED.result_json,
                    created_at = EXCLUDED.created_at
                """,
                [
                    (
                        text_value(row.get("result_id")),
                        text_value(row.get("job_id")),
                        text_value(row.get("template_id")),
                        text_value(row.get("template_name")),
                        text_value(row.get("sample_url")),
                        text_value(row.get("audit_outcome")),
                        text_value(row.get("implementation_status")),
                        bool_value(row.get("ga_present")),
                        bool_value(row.get("pageview_triggered")),
                        text_value(row.get("pageview_source")),
                        int_value(row.get("events_count")),
                        text_value(row.get("events_fired")),
                        text_value(row.get("measurement_id")),
                        text_value(row.get("container_id")),
                        bool_value(row.get("comscore_present")),
                        bool_value(row.get("chartbeat_present")),
                        text_value(row.get("issues")),
                        jsonb_value(row.get("result_json")),
                        text_value(row.get("created_at")),
                    )
                    for row in rows
                ],
            )
    return len(rows)


def main():
    with psycopg.connect(neon_url(), row_factory=dict_row) as conn:
        with conn.cursor() as cur:
            cur.execute(SCHEMA_SQL)
        for table in SUPABASE_TABLES:
            rows = fetch_supabase_table(table)
            inserted = insert_rows(conn, table, rows)
            print(f"{table}: migrated {inserted} row(s)")


if __name__ == "__main__":
    main()
