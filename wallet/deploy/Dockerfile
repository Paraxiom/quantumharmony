# Build stage
FROM rust:1.75 as builder

WORKDIR /usr/src/quantum-wallet

# Copy manifests
COPY Cargo.toml Cargo.lock ./

# Copy source code
COPY src ./src
COPY examples ./examples

# Build release binaries
RUN cargo build --release --features std --bins

# Runtime stage
FROM ubuntu:22.04

# Install runtime dependencies
RUN apt-get update && apt-get install -y \
    ca-certificates \
    libssl3 \
    && rm -rf /var/lib/apt/lists/*

# Create quantum user
RUN useradd -m -s /bin/bash quantum

# Create directories
RUN mkdir -p /app /var/lib/quantum-wallet /var/log/quantum-wallet \
    && chown -R quantum:quantum /app /var/lib/quantum-wallet /var/log/quantum-wallet

# Copy binaries from builder
COPY --from=builder /usr/src/quantum-wallet/target/release/quantum_tunnel_server /app/
COPY --from=builder /usr/src/quantum-wallet/target/release/quantum_wallet_web /app/
COPY --from=builder /usr/src/quantum-wallet/target/release/kirq_tunnel_client /app/

# Make binaries executable
RUN chmod +x /app/*

# Copy static files (if any)
COPY static /app/static

# Switch to quantum user
USER quantum

# Expose ports
EXPOSE 9999 3030 9090

# Default command
CMD ["/app/quantum_tunnel_server"]