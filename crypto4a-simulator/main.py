"""
Crypto4A QRNG Simulator
=======================
Simulates the Crypto4A HSM QRNG API for development/testing.
Returns cryptographically secure random bytes from urandom.

In production, this would be replaced by actual Crypto4A HSM hardware.
"""

import os
import secrets
import time
from fastapi import FastAPI, Query, Response
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel
from typing import Optional

app = FastAPI(
    title="Crypto4A QRNG Simulator",
    description="Simulates quantum random number generator for QuantumHarmony",
    version="1.0.0"
)

# Allow CORS for dashboard access
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Statistics tracking
stats = {
    "bytes_served": 0,
    "requests": 0,
    "start_time": time.time()
}


class HealthResponse(BaseModel):
    status: str
    uptime_seconds: float
    bytes_served: int
    requests: int


class EntropyResponse(BaseModel):
    entropy: str
    qber: float
    timestamp: int
    source: str


@app.get("/health")
def health() -> HealthResponse:
    """Health check endpoint"""
    return HealthResponse(
        status="healthy",
        uptime_seconds=time.time() - stats["start_time"],
        bytes_served=stats["bytes_served"],
        requests=stats["requests"]
    )


@app.get("/v1/random")
def get_random_bytes(size: int = Query(default=32, ge=1, le=1024)) -> Response:
    """
    Get raw random bytes (Crypto4A HSM API compatible)

    This is the endpoint kirq-hub's crypto4a source calls.
    Returns raw bytes, not JSON.
    """
    stats["requests"] += 1
    stats["bytes_served"] += size

    # Generate cryptographically secure random bytes
    entropy = secrets.token_bytes(size)

    return Response(
        content=entropy,
        media_type="application/octet-stream"
    )


@app.get("/entropy/crypto4a")
def get_entropy_json(size: int = Query(default=32, ge=1, le=1024)) -> EntropyResponse:
    """
    Get entropy as JSON (alternative API)

    Returns entropy as hex string with metadata.
    """
    stats["requests"] += 1
    stats["bytes_served"] += size

    entropy = secrets.token_bytes(size)

    return EntropyResponse(
        entropy=entropy.hex(),
        qber=0.005,  # Simulated quantum bit error rate
        timestamp=int(time.time() * 1000),
        source="crypto4a-simulator"
    )


@app.post("/entropy/mixed")
def get_mixed_entropy(
    num_bytes: int = 32,
    sources: list[str] = None,
    proof_required: bool = False
):
    """
    Get mixed entropy from multiple simulated sources
    """
    stats["requests"] += 1
    stats["bytes_served"] += num_bytes

    entropy = secrets.token_bytes(num_bytes)

    response = {
        "entropy": entropy.hex(),
        "encoding": "hex",
        "sources_used": sources or ["crypto4a"],
        "timestamp": int(time.time() * 1000),
    }

    if proof_required:
        # Simulate STARK proof (in production this would be real)
        response["proof"] = {
            "type": "STARK",
            "valid": True,
            "commitment": secrets.token_hex(32)
        }

    return response


if __name__ == "__main__":
    import uvicorn
    port = int(os.environ.get("PORT", "8106"))
    uvicorn.run(app, host="0.0.0.0", port=port)
