#!/bin/bash
#
# QuantumHarmony Docker Entrypoint
#
# This script handles:
#   1. Key injection from Docker secrets or environment variables
#   2. Node configuration from environment variables
#   3. Graceful startup with proper signal handling
#
# Environment Variables:
#   CHAIN_SPEC        - Path to chain spec file (default: /config/chainspec.json)
#   BASE_PATH         - Directory for chain data (default: /data)
#   NODE_NAME         - Human-readable node name
#   VALIDATOR         - Run as validator (true/false)
#   RPC_PORT          - RPC/WebSocket port (default: 9944)
#   P2P_PORT          - P2P networking port (default: 30333)
#   PROMETHEUS_PORT   - Metrics port (default: 9615)
#   RPC_CORS          - CORS setting (default: all)
#   RPC_METHODS       - RPC methods: Safe, Unsafe (default: Safe)
#   BOOTNODES         - Comma-separated list of bootnodes
#   PUBLIC_ADDR       - Public address for P2P
#   NODE_KEY          - 64-char hex node key (for stable peer ID)
#
# Key Injection (for validators):
#   SPHINCS_SECRET_KEY - 128-byte hex SPHINCS+ secret key
#   AURA_PUBLIC_KEY    - 64-byte hex SPHINCS+ public key for Aura
#
# Docker Secrets (alternative to env vars):
#   /run/secrets/sphincs_secret_key
#   /run/secrets/node_key

set -e

# =============================================================================
# Helper Functions
# =============================================================================

log() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] $1"
}

error() {
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] ERROR: $1" >&2
    exit 1
}

# Read from Docker secret file or environment variable
get_secret() {
    local secret_name="$1"
    local env_var="$2"
    local secret_file="/run/secrets/${secret_name}"

    if [ -f "$secret_file" ]; then
        cat "$secret_file"
    elif [ -n "${!env_var}" ]; then
        echo "${!env_var}"
    else
        echo ""
    fi
}

# Wait for RPC to be available
wait_for_rpc() {
    local max_attempts=30
    local attempt=0

    log "Waiting for RPC endpoint..."
    while [ $attempt -lt $max_attempts ]; do
        if curl -sf "http://localhost:${RPC_PORT}/health" > /dev/null 2>&1; then
            log "RPC endpoint ready"
            return 0
        fi
        attempt=$((attempt + 1))
        sleep 1
    done

    log "WARNING: RPC endpoint not ready after ${max_attempts}s"
    return 1
}

# Inject SPHINCS+ session key via RPC
inject_sphincs_key() {
    local secret_key="$1"
    local public_key="$2"

    if [ -z "$secret_key" ] || [ -z "$public_key" ]; then
        log "No SPHINCS+ keys provided, skipping injection"
        return 0
    fi

    log "Injecting SPHINCS+ session key..."

    # Ensure keys have 0x prefix
    [[ "$secret_key" != 0x* ]] && secret_key="0x${secret_key}"
    [[ "$public_key" != 0x* ]] && public_key="0x${public_key}"

    local response
    response=$(curl -sf -H "Content-Type: application/json" \
        -d "{\"id\":1, \"jsonrpc\":\"2.0\", \"method\":\"author_insertKey\", \"params\":[\"aura\", \"${secret_key}\", \"${public_key}\"]}" \
        "http://localhost:${RPC_PORT}" 2>&1)

    if echo "$response" | grep -q '"result"'; then
        log "SPHINCS+ key injected successfully"
        return 0
    else
        log "WARNING: Key injection failed: $response"
        return 1
    fi
}

# =============================================================================
# Main Configuration
# =============================================================================

log "QuantumHarmony Node Starting..."

# Build command arguments
ARGS=()

# Chain spec
if [ -f "$CHAIN_SPEC" ]; then
    ARGS+=("--chain" "$CHAIN_SPEC")
    log "Using chain spec: $CHAIN_SPEC"
else
    log "WARNING: Chain spec not found at $CHAIN_SPEC, using default"
fi

# Base path for chain data
ARGS+=("--base-path" "$BASE_PATH")
log "Data directory: $BASE_PATH"

# Node name
if [ -n "$NODE_NAME" ]; then
    ARGS+=("--name" "$NODE_NAME")
    log "Node name: $NODE_NAME"
fi

# Validator mode
if [ "$VALIDATOR" = "true" ]; then
    ARGS+=("--validator")
    log "Running as VALIDATOR"
else
    log "Running as FULL NODE"
fi

# RPC configuration
ARGS+=("--rpc-port" "$RPC_PORT")
ARGS+=("--rpc-cors" "$RPC_CORS")
ARGS+=("--rpc-methods" "$RPC_METHODS")
ARGS+=("--rpc-external")

# P2P configuration
ARGS+=("--port" "$P2P_PORT")

# Prometheus metrics
ARGS+=("--prometheus-port" "$PROMETHEUS_PORT")
ARGS+=("--prometheus-external")

# Public address (for NAT traversal)
if [ -n "$PUBLIC_ADDR" ]; then
    ARGS+=("--public-addr" "$PUBLIC_ADDR")
    log "Public address: $PUBLIC_ADDR"
fi

# Bootnodes
if [ -n "$BOOTNODES" ]; then
    IFS=',' read -ra BOOTNODE_ARRAY <<< "$BOOTNODES"
    for bootnode in "${BOOTNODE_ARRAY[@]}"; do
        ARGS+=("--bootnodes" "$bootnode")
    done
    log "Bootnodes configured: ${#BOOTNODE_ARRAY[@]}"
fi

# Node key (for stable peer ID)
NODE_KEY_VALUE=$(get_secret "node_key" "NODE_KEY")
if [ -n "$NODE_KEY_VALUE" ]; then
    ARGS+=("--node-key" "$NODE_KEY_VALUE")
    log "Using provided node key"
fi

# =============================================================================
# Key Injection Setup (for validators)
# =============================================================================

SPHINCS_SECRET=$(get_secret "sphincs_secret_key" "SPHINCS_SECRET_KEY")
AURA_PUBLIC=$(get_secret "aura_public_key" "AURA_PUBLIC_KEY")

if [ "$VALIDATOR" = "true" ] && [ -n "$SPHINCS_SECRET" ]; then
    log "Validator key provided, will inject after node starts"
    INJECT_KEY=true
else
    INJECT_KEY=false
fi

# =============================================================================
# Start Node
# =============================================================================

log "Starting node with args: ${ARGS[*]}"

# If we need to inject keys, start node in background first
if [ "$INJECT_KEY" = true ]; then
    # Start node in background
    /usr/local/bin/quantumharmony-node "${ARGS[@]}" &
    NODE_PID=$!

    # Wait for RPC and inject key
    if wait_for_rpc; then
        inject_sphincs_key "$SPHINCS_SECRET" "$AURA_PUBLIC"
    fi

    # Clear sensitive data
    unset SPHINCS_SECRET
    unset SPHINCS_SECRET_KEY

    # Wait for node process
    wait $NODE_PID
else
    # Just exec the node directly
    exec /usr/local/bin/quantumharmony-node "${ARGS[@]}"
fi
