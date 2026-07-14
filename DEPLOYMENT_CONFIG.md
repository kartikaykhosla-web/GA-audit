# Deployment Configuration

This app has two runtime surfaces that need credentials after migrating to `adminjnmgit/GA-audit`:

- Streamlit Cloud secrets for the interactive app.
- GitHub Actions repository secrets for the background bulk audit worker.

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
- `[github]`: workflow dispatch settings for the migrated repo.

The Google service account email must have access to the configured spreadsheet. Share the sheet with the `client_email` value from the service account JSON.

The default spreadsheet and worksheet names used by the app are:

- `spreadsheet_id`: `1e_fp0fAOeEAHaRtFJUv-rt-i0sqUOhszYOrOk7Cv5QU`
- `worksheet_name`: `Audit Logs`
- `template_worksheet_name`: `Audit Templates`
- `template_rules_worksheet_name`: `Audit Template Rules`
- `bulk_jobs_worksheet_name`: `Bulk Audit Jobs`
- `bulk_results_worksheet_name`: `Bulk Audit Results`

For GitHub workflow dispatch from the app, set:

```toml
[github]
owner = "adminjnmgit"
repo = "GA-audit"
workflow = "bulk-audit.yml"
ref = "main"
token = "github_pat_or_fine_grained_token_with_actions_write"
```

## Neon

Set one of these connection values:

- Streamlit secrets: `[neon] database_url = "postgresql://..."`
- Environment/repository secret: `NEON_DATABASE_URL`
- Fallback names supported by code: `DATABASE_URL`, `POSTGRES_URL`

The app creates the required Neon tables automatically when it connects:

- `ga_audit_templates`
- `ga_audit_template_rules`
- `ga_audit_logs`
- `bulk_audit_jobs`
- `bulk_audit_results`

Use a pooled Neon connection string if the deployed app has connection churn. Keep `sslmode=require` in the URL.

## GitHub Actions Secrets

The bulk audit workflow reads secrets from the `adminjnmgit/GA-audit` repository settings.

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
