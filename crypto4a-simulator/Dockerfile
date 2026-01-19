# Crypto4A QRNG Simulator
# Simulates quantum RNG API for development/testing

FROM python:3.11-slim

WORKDIR /app

# Install dependencies
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# Copy application
COPY main.py .

# Create non-root user
RUN useradd -m -u 1000 appuser && chown -R appuser:appuser /app
USER appuser

# Health check
HEALTHCHECK --interval=30s --timeout=5s --start-period=10s --retries=3 \
    CMD python -c "import urllib.request; urllib.request.urlopen('http://localhost:8106/health')" || exit 1

# Expose port
EXPOSE 8106

# Environment
ENV PORT=8106

# Run
CMD ["python", "main.py"]
