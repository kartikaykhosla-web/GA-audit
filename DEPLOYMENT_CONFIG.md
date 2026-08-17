# Deployment Configuration

This app has two runtime surfaces that need credentials after migrating to `adminjnmgit/GA-audit`:

- Cloud Run service environment variables for the interactive Streamlit app.
- A Cloud Run Job for the background bulk audit worker.

Do not commit real secrets. Use `.streamlit/secrets.toml.example` as the shape to paste into Streamlit Cloud.

## Streamlit Cloud

Deploy with:

- Repository: `adminjnmgit/GA-audit`
- Branch: `main`
- Main file path: `GA4audit_streamlit.py`
- Python dependencies: `requirements.txt`
- System packages: `packages.txt`

Add these sections in Streamlit secrets:

- `[gcp_service_account]`: the Google service account JSON fields.
- `[sheets]`: spreadsheet and worksheet names.
- `[neon]`: `database_url`.
- `[cloud_run_job]`: optional Cloud Run Job trigger settings if not using environment variables.

The Google service account email must have access to the configured spreadsheet. Share the sheet with the `client_email` value from the service account JSON.

The default spreadsheet and worksheet names used by the app are:

- `spreadsheet_id`: `1e_fp0fAOeEAHaRtFJUv-rt-i0sqUOhszYOrOk7Cv5QU`
- `worksheet_name`: `Audit Logs`
- `template_worksheet_name`: `Audit Templates`
- `template_rules_worksheet_name`: `Audit Template Rules`
- `bulk_jobs_worksheet_name`: `Bulk Audit Jobs`
- `bulk_results_worksheet_name`: `Bulk Audit Results`

For Cloud Run Job dispatch from the app, set:

```toml
[cloud_run_job]
project_id = "your-gcp-project"
region = "asia-south1"
job_name = "ga-audit-worker"
```

GitHub workflow dispatch is still supported as a fallback, but Cloud Run Jobs are preferred for production.

## Neon

Set one of these connection values:

- Streamlit secrets: `[neon] database_url = "postgresql://..."`
- Cloud Run environment variable or Secret Manager-backed variable: `NEON_DATABASE_URL`
- Cloud Run Job environment variable or Secret Manager-backed variable: `NEON_DATABASE_URL`
- Fallback names supported by code: `DATABASE_URL`, `POSTGRES_URL`

The app creates the required Neon tables automatically when it connects:

- `ga_audit_templates`
- `ga_audit_template_rules`
- `ga_audit_logs`
- `bulk_audit_jobs`
- `bulk_audit_results`

Use a pooled Neon connection string if the deployed app has connection churn. Keep `sslmode=require` in the URL.

## Cloud Run Environment Variables

Cloud Run does not need Streamlit `st.secrets` for Neon. Configure the deployed service with environment variables, preferably backed by Secret Manager.

Required for Neon:

```text
NEON_DATABASE_URL=postgresql://user:password@host/neondb?sslmode=require&channel_binding=require
```

Supported fallback names, if your platform already uses them:

```text
DATABASE_URL=postgresql://...
POSTGRES_URL=postgresql://...
```

The app checks environment variables first, then falls back to Streamlit secrets. For Cloud Run, prefer `NEON_DATABASE_URL` so the purpose is clear.

Required if the Cloud Run app should trigger Cloud Run Jobs bulk audits:

```text
CLOUD_RUN_PROJECT_ID=your-gcp-project
CLOUD_RUN_REGION=asia-south1
CLOUD_RUN_JOB_NAME=ga-audit-worker
```

The Cloud Run service account used by the Streamlit app needs permission to run the job. Grant a role that includes `run.jobs.run`, such as `roles/run.developer`, on the worker job or project.

The app also supports these aliases:

```text
GCP_PROJECT_ID=your-gcp-project
GCP_REGION=asia-south1
GOOGLE_CLOUD_PROJECT=your-gcp-project
GOOGLE_CLOUD_REGION=asia-south1
```

## Cloud Run Job

Create a Cloud Run Job from the same image used by the app, but configure the job command for the worker:

```text
Command: python
Arguments: bulk_audit_worker.py --job-id placeholder
```

The app overrides the job arguments at runtime with:

```text
bulk_audit_worker.py --job-id <job_id> --chunk-index <n> --chunk-count <total>
```

Required worker environment variables:

```text
NEON_DATABASE_URL=postgresql://...
BULK_AUDIT_CONCURRENCY=1
BULK_ROW_TIMEOUT_SECONDS=150
BULK_VIDEO_MVP_TIMEOUT_SECONDS=30
```

Use the same Secret Manager-backed `NEON_DATABASE_URL` as the Cloud Run app. If the job uses a different service account, make sure it has access to the DB secret.

## GitHub Actions Secrets

GitHub Actions are now optional fallback only. The bulk audit workflow reads secrets from the `adminjnmgit/GA-audit` repository settings if you still use that backend.

Required for Neon-backed bulk jobs:

- `NEON_DATABASE_URL`

Required if using Google Sheets-backed bulk jobs:

- `GCP_SERVICE_ACCOUNT_JSON`
- `GOOGLE_SHEET_ID`

Supported aliases:

- `DATABASE_URL`
- `POSTGRES_URL`
- `GOOGLE_SERVICE_ACCOUNT_JSON`
- `GOOGLE_APPLICATION_CREDENTIALS_JSON`
- `SHEETS_SPREADSHEET_ID`
- `SPREADSHEET_ID`
- `BULK_JOBS_WORKSHEET_NAME`
- `BULK_RESULTS_WORKSHEET_NAME`

Legacy Supabase fallback, only if still needed:

- `SUPABASE_URL`
- `SUPABASE_SERVICE_ROLE_KEY`

## Google Sheets Setup

1. Create or choose the Google Sheet.
2. Share it with the service account `client_email`.
3. Add these worksheets or let the app create/fill them where supported:
   - `Audit Logs`
   - `Audit Templates`
   - `Audit Template Rules`
   - `Bulk Audit Jobs`
   - `Bulk Audit Results`
4. Put the sheet ID in Streamlit `[sheets].spreadsheet_id`.
5. Put the same sheet ID in the GitHub Actions secret `GOOGLE_SHEET_ID` if using Sheets for bulk worker storage.

## Keep-Awake URL

`.github/workflows/keep_streamlit_awake.yml` currently pings:

```text
https://ga4-audit.streamlit.app/
```

Update that URL if the migrated Streamlit app uses a different domain.
