#!/bin/bash
# Simple server for the Notarial App

PORT=${1:-8000}

echo "Starting QuantumHarmony Notarial App on http://localhost:$PORT"
echo "Press Ctrl+C to stop"

# Use Python's built-in HTTP server
if command -v python3 &> /dev/null; then
    python3 -m http.server $PORT
elif command -v python &> /dev/null; then
    python -m SimpleHTTPServer $PORT
else
    echo "Error: Python not found. Install Python or use another HTTP server."
    exit 1
fi
