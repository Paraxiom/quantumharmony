# QuantumHarmony Node Operator Docker Image
#
# Post-quantum secure validator management service with encrypted messaging.
#
# Build:
#   cargo build --release -p node-operator
#   docker build -t sylvaincormier/quantumharmony-node-operator:latest node-operator/
#
FROM ubuntu:22.04

LABEL org.opencontainers.image.title="QuantumHarmony Node Operator"
LABEL org.opencontainers.image.description="Quantum-safe validator management with encrypted P2P messaging"
LABEL org.opencontainers.image.vendor="QuantumVerseProtocols"

# Install runtime dependencies
RUN apt-get update && apt-get install -y \
    ca-certificates \
    curl \
    libssl3 \
    && rm -rf /var/lib/apt/lists/* \
    && useradd -m -u 1000 -U -s /bin/bash qhoperator

# Copy the compiled binary (build from repo root with: docker build -f node-operator/Dockerfile .)
COPY target/release/node-operator /usr/local/bin/
RUN chmod +x /usr/local/bin/node-operator

# Create data directories
RUN mkdir -p /data/messaging /data/keystore && chown -R qhoperator:qhoperator /data

# Expose ports
# 9955: Operator API (HTTP + WebSocket)
EXPOSE 9955

# Volume for data persistence
VOLUME ["/data"]

# Run as non-root user
USER qhoperator

# Environment defaults
ENV OPERATOR_PORT=9955
ENV DATA_DIR=/data
ENV ALLOW_UNAUTHENTICATED=false

# Health check
HEALTHCHECK --interval=30s --timeout=5s --start-period=5s --retries=3 \
    CMD curl -f http://localhost:9955/health || exit 1

ENTRYPOINT ["/usr/local/bin/node-operator"]
CMD ["--data-dir", "/data", "--port", "9955"]
