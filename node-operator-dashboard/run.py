#!/usr/bin/env python3
"""
QuantumHarmony Dashboard - Standalone Server
Connects to remote or local node RPC
"""
import http.server
import socketserver
import urllib.request
import json
import os
import webbrowser

PORT = 8080
DIRECTORY = os.path.dirname(os.path.abspath(__file__))

# Default to production testnet, override with env var
RPC_URL = os.environ.get("RPC_URL", "http://51.79.26.123:9944")

class Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=DIRECTORY, **kwargs)

    def send_json(self, data, status=200):
        self.send_response(status)
        self.send_header("Content-Type", "application/json")
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(json.dumps(data).encode())

    def do_OPTIONS(self):
        self.send_response(200)
        self.send_header("Access-Control-Allow-Origin", "*")
        self.send_header("Access-Control-Allow-Methods", "GET, POST, OPTIONS")
        self.send_header("Access-Control-Allow-Headers", "Content-Type")
        self.end_headers()

    def do_POST(self):
        if self.path == "/rpc":
            length = int(self.headers.get('Content-Length', 0))
            body = self.rfile.read(length) if length > 0 else b'{}'
            try:
                req = urllib.request.Request(
                    RPC_URL,
                    data=body,
                    headers={"Content-Type": "application/json"}
                )
                with urllib.request.urlopen(req, timeout=10) as resp:
                    self.send_json(json.loads(resp.read().decode()))
            except Exception as e:
                self.send_json({"jsonrpc": "2.0", "id": 1, "error": {"code": -32000, "message": str(e)}})
        else:
            self.send_json({"error": "not found"}, 404)

    def log_message(self, format, *args):
        try:
            msg = str(args[0]) if args else ""
            if "/rpc" not in msg:
                print(f"[{__import__('time').strftime('%H:%M:%S')}] {msg}")
        except:
            pass


if __name__ == '__main__':
    print(f"""
╔══════════════════════════════════════════════════════════╗
║         QuantumHarmony Production Testnet                ║
╠══════════════════════════════════════════════════════════╣
║  Dashboard:  http://localhost:{PORT}                       ║
║  Network:    {RPC_URL}                ║
╚══════════════════════════════════════════════════════════╝

Inject keys via dashboard to participate in block production.

Connect to different node:
  RPC_URL=http://localhost:9944 python3 run.py
""")

    webbrowser.open(f"http://localhost:{PORT}")

    with socketserver.TCPServer(("", PORT), Handler) as httpd:
        try:
            httpd.serve_forever()
        except KeyboardInterrupt:
            print("\nShutting down...")
