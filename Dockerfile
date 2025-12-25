# QuantumHarmony Node Docker Image
#
# This Dockerfile uses a pre-built binary. To build:
#   1. Build the node: cargo build --release -p quantumharmony-node
#   2. Build image: docker build -t quantumharmony:latest .
#
# For building from source, use Dockerfile.multinode instead.
#
FROM ubuntu:22.04

LABEL org.opencontainers.image.title="QuantumHarmony Node"
LABEL org.opencontainers.image.description="Post-quantum secure blockchain node using SPHINCS+ signatures"
LABEL org.opencontainers.image.vendor="QuantumVerseProtocols"

# Install runtime dependencies
RUN apt-get update && apt-get install -y \
    ca-certificates \
    curl \
    libssl3 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd -m -u 1000 -s /bin/bash node

# Copy the compiled binary
COPY target/release/quantumharmony-node /usr/local/bin/
RUN chmod +x /usr/local/bin/quantumharmony-node

# Create data directory with correct ownership
RUN mkdir -p /data && chown node:node /data

# Expose ports
# 30333: P2P networking
# 9944: RPC (HTTP + WebSocket)
# 9615: Prometheus metrics
EXPOSE 30333 9944 9615

# Volume for chain data
VOLUME ["/data"]

# Run as non-root user
USER node

# Default command (can be overridden)
ENTRYPOINT ["/usr/local/bin/quantumharmony-node"]
CMD ["--help"]
