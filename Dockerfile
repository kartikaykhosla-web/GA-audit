FROM python:3.11-slim

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PORT=8080

WORKDIR /app

# Install OS packages
COPY packages.txt .

RUN apt-get update && \
    xargs -a packages.txt apt-get install -y --no-install-recommends && \
    rm -rf /var/lib/apt/lists/*

# Install Python dependencies
COPY requirements.txt .

RUN pip install --upgrade pip && \
    pip install --no-cache-dir -r requirements.txt

# Copy application
COPY . .

EXPOSE 8080

CMD ["streamlit", "run", "GA4audit_streamlit.py", "--server.port=8080", "--server.address=0.0.0.0"]
