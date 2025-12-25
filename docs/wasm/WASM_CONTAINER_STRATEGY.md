# WASM Containerization Strategy for QuantumHarmony

## Overview
Running WASM runtime in containers provides isolation and safer testing before production deployment.

## Benefits
1. **Isolation**: WASM runtime errors won't affect host system
2. **Version Control**: Easy to test different WASM builds
3. **Reproducibility**: Consistent environment across machines
4. **Resource Limits**: Control memory/CPU usage
5. **Easy Rollback**: Quick recovery if issues arise

## Container Architecture

```
┌─────────────────────────────────────┐
│      Docker Host (Ubuntu)           │
├─────────────────────────────────────┤
│                                     │
│  ┌─────────────────────────────┐   │
│  │  quantum-wasm-test:latest   │   │
│  │                             │   │
│  │  • Substrate Node           │   │
│  │  • WASM Runtime             │   │
│  │  • Quantum Pallets          │   │
│  │  • Mock KIRQ Entropy        │   │
│  └─────────────────────────────┘   │
│                                     │
│  ┌─────────────────────────────┐   │
│  │  quantum-wasm-prod:latest   │   │
│  │                             │   │
│  │  • Production WASM          │   │
│  │  • Real KIRQ Connection     │   │
│  │  • Full Security            │   │
│  └─────────────────────────────┘   │
└─────────────────────────────────────┘
```

## Implementation Steps

### 1. Create Test Container
```dockerfile
FROM rust:1.70 as builder

# Build dependencies
RUN apt-get update && apt-get install -y \
    clang \
    libclang-dev \
    protobuf-compiler

# Copy source
WORKDIR /quantum
COPY . .

# Build WASM runtime only
RUN cargo build --release --features runtime-benchmarks

FROM ubuntu:22.04
RUN apt-get update && apt-get install -y \
    ca-certificates \
    && rm -rf /var/lib/apt/lists/*

COPY --from=builder /quantum/target/release/wbuild/quantum-runtime/quantum_runtime.wasm /runtime/
COPY --from=builder /quantum/target/release/quantum-node /usr/local/bin/

# Mock KIRQ entropy for testing
ENV KIRQ_MOCK=true
ENV WASM_RUNTIME_OVERRIDE=/runtime/quantum_runtime.wasm

EXPOSE 9944 9933 30333

CMD ["quantum-node", "--dev", "--rpc-external"]
```

### 2. Isolation Testing Script
```bash
#!/bin/bash
# test_wasm_isolated.sh

# Build test container
docker build -t quantum-wasm-test:latest -f Dockerfile.wasm .

# Run with resource limits
docker run -d \
  --name quantum-wasm-test \
  --memory="2g" \
  --cpus="2" \
  -p 9944:9944 \
  -v $(pwd)/wasm-overrides:/wasm-overrides:ro \
  quantum-wasm-test:latest

# Monitor logs
docker logs -f quantum-wasm-test
```

### 3. WASM Hot-Reload Development
```yaml
# docker-compose.wasm-dev.yml
version: '3.8'

services:
  quantum-wasm-dev:
    build:
      context: .
      dockerfile: Dockerfile.wasm
    volumes:
      - ./target/release/wbuild:/wasm:ro
      - ./chainspec:/chainspec:ro
    environment:
      - RUST_LOG=runtime=debug
      - WASM_RUNTIME_OVERRIDE=/wasm/quantum_runtime.wasm
    ports:
      - "9944:9944"
      - "9933:9933"
    restart: unless-stopped
```

## Testing Strategy

### Phase 1: Container Validation
1. Build WASM in isolated container
2. Test basic runtime calls
3. Verify quantum pallet functions
4. Check memory usage and performance

### Phase 2: Integration Testing
1. Connect containerized node to test network
2. Test with mock KIRQ entropy
3. Validate consensus mechanisms
4. Run stress tests

### Phase 3: Production Preparation
1. Switch to real KIRQ connection
2. Enable full security features
3. Performance optimization
4. Security audit

## Quick Start Commands

```bash
# Build WASM container
cd /home/paraxiom/quantumharmony
docker build -t quantum-wasm:test -f docker/Dockerfile.wasm .

# Run isolated test
docker run -it --rm \
  -p 9944:9944 \
  -e RUST_LOG=runtime=debug \
  quantum-wasm:test

# Connect to running container
docker exec -it quantum-wasm-test /bin/bash

# Check WASM runtime
docker exec quantum-wasm-test ls -la /runtime/
```

## Next Steps
1. Create Dockerfile.wasm for isolated builds
2. Set up GitHub Actions for automated container builds
3. Implement WASM versioning system
4. Create test suite for containerized runtime