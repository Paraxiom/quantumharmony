#!/bin/bash
# deploy-pqc-peerid-fix.sh — Deploy the PQC PeerId override fix
#
# This script deploys the fix for the dual-PeerId bug where the Swarm used
# an Ed25519-derived PeerId but the PQC transport authenticator returned
# Falcon-1024-derived PeerIds, causing WrongPeerId errors and dropped connections.
#
# After this fix:
#   - local_peer_id is overridden with the Falcon-derived PeerId
#   - Bootnode addresses use Falcon-derived PeerIds (Qm... format)
#   - PQC handshake returns matching Falcon PeerIds → stable peering
#
# PQC PeerIds (Falcon-1024 derived, SHA3-256 hash of public key):
#   Alice:   QmNVxWSGHMvTeLTHxZfd8WcWDSiEnQBVyZboaVqPc4y3ox
#   Bob:     QmeZwWcveZ5faSHYpJkiuCwx4wy7ByUUvn3rJhhQETWbYC
#   Charlie: QmQMjTeQZ56wV4nYGS2MAF2fM5tECQ2ETjGv6nsn5ESLMa

set -euo pipefail

ALICE_IP="51.79.26.123"
BOB_IP="51.79.26.168"
CHARLIE_IP="209.38.225.4"

ALICE_PQC_PEERID="QmNVxWSGHMvTeLTHxZfd8WcWDSiEnQBVyZboaVqPc4y3ox"
BOB_PQC_PEERID="QmeZwWcveZ5faSHYpJkiuCwx4wy7ByUUvn3rJhhQETWbYC"
CHARLIE_PQC_PEERID="QmQMjTeQZ56wV4nYGS2MAF2fM5tECQ2ETjGv6nsn5ESLMa"

IMAGE="${DOCKER_IMAGE:-sylvaincormier/quantumharmony-node:v28.1-pqc-peerid-fix}"

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

log() { echo -e "${GREEN}[deploy]${NC} $*"; }
warn() { echo -e "${YELLOW}[warn]${NC} $*"; }
err() { echo -e "${RED}[error]${NC} $*" >&2; }

check_health() {
    local host=$1
    local name=$2
    local result
    result=$(ssh -o ConnectTimeout=5 "$host" \
        "curl -sf -H 'Content-Type: application/json' \
        -d '{\"id\":1,\"jsonrpc\":\"2.0\",\"method\":\"system_health\",\"params\":[]}' \
        http://localhost:9944" 2>/dev/null) || { warn "$name: RPC not responding"; return 1; }
    echo "$result" | python3 -c "import sys,json; h=json.load(sys.stdin)['result']; print(f'  peers={h[\"peers\"]}, syncing={h[\"isSyncing\"]}, blocks={h.get(\"shouldHavePeers\",\"?\")}')" 2>/dev/null
}

show_status() {
    log "Current network status:"
    echo "  Alice ($ALICE_IP):"
    check_health quantumharmony1 "Alice" || true
    echo "  Bob ($BOB_IP):"
    check_health quantumharmony2 "Bob" || true
    echo "  Charlie ($CHARLIE_IP):"
    check_health quantumharmony3 "Charlie" || true
}

deploy_validator() {
    local ssh_host=$1
    local name=$2
    local container=$3
    local bootnodes=$4

    log "Deploying $name ($ssh_host)..."

    # Stop existing container
    ssh "$ssh_host" "docker stop $container 2>/dev/null; docker rm $container 2>/dev/null" || true

    # Pull new image
    ssh "$ssh_host" "docker pull $IMAGE"

    # Start with updated bootnodes
    ssh "$ssh_host" "docker run -d \
        --name $container \
        --restart unless-stopped \
        -p 9944:9944 -p 30333:30333 -p 9615:9615 \
        -v /root/quantumharmony/data:/data \
        -v /root/quantumharmony/chainspec.json:/config/chainspec.json:ro \
        -v /root/quantumharmony/wasm-overrides:/wasm-overrides:ro \
        $IMAGE \
        --chain=/config/chainspec.json \
        --sync=full \
        --wasm-runtime-overrides=/wasm-overrides \
        --validator \
        --base-path=/data \
        --name=$name \
        --rpc-external \
        --rpc-cors=all \
        --rpc-methods=Unsafe \
        --rpc-port=9944 \
        --port=30333 \
        --prometheus-port=9615 \
        --prometheus-external \
        $bootnodes"

    log "$name started."
}

case "${1:-help}" in
    status)
        show_status
        ;;

    deploy-all)
        warn "This will restart ALL 3 validators. Network will be briefly offline."
        read -p "Continue? (y/N) " -n 1 -r
        echo
        [[ $REPLY =~ ^[Yy]$ ]] || { echo "Cancelled."; exit 0; }

        log "Starting rolling deployment..."
        echo ""

        # Deploy Alice (bootnodes: Bob + Charlie)
        deploy_validator quantumharmony1 "Alice" "quantumharmony-node" \
            "--bootnodes=/ip4/$BOB_IP/tcp/30333/p2p/$BOB_PQC_PEERID --bootnodes=/ip4/$CHARLIE_IP/tcp/30333/p2p/$CHARLIE_PQC_PEERID"

        # Deploy Bob (bootnodes: Alice + Charlie)
        deploy_validator quantumharmony2 "Bob" "quantumharmony-node" \
            "--bootnodes=/ip4/$ALICE_IP/tcp/30333/p2p/$ALICE_PQC_PEERID --bootnodes=/ip4/$CHARLIE_IP/tcp/30333/p2p/$CHARLIE_PQC_PEERID"

        # Deploy Charlie (bootnodes: Alice + Bob)
        deploy_validator quantumharmony3 "Charlie" "charlie-validator" \
            "--bootnodes=/ip4/$ALICE_IP/tcp/30333/p2p/$ALICE_PQC_PEERID --bootnodes=/ip4/$BOB_IP/tcp/30333/p2p/$BOB_PQC_PEERID"

        echo ""
        log "All validators deployed. Waiting 15s for startup..."
        sleep 15
        show_status
        ;;

    deploy-alice)
        deploy_validator quantumharmony1 "Alice" "quantumharmony-node" \
            "--bootnodes=/ip4/$BOB_IP/tcp/30333/p2p/$BOB_PQC_PEERID --bootnodes=/ip4/$CHARLIE_IP/tcp/30333/p2p/$CHARLIE_PQC_PEERID"
        ;;

    deploy-bob)
        deploy_validator quantumharmony2 "Bob" "quantumharmony-node" \
            "--bootnodes=/ip4/$ALICE_IP/tcp/30333/p2p/$ALICE_PQC_PEERID --bootnodes=/ip4/$CHARLIE_IP/tcp/30333/p2p/$CHARLIE_PQC_PEERID"
        ;;

    deploy-charlie)
        deploy_validator quantumharmony3 "Charlie" "charlie-validator" \
            "--bootnodes=/ip4/$ALICE_IP/tcp/30333/p2p/$ALICE_PQC_PEERID --bootnodes=/ip4/$BOB_IP/tcp/30333/p2p/$BOB_PQC_PEERID"
        ;;

    verify)
        log "Verifying PQC PeerId fix..."
        echo ""
        for host_info in "quantumharmony1:Alice:quantumharmony-node" "quantumharmony2:Bob:quantumharmony-node" "quantumharmony3:Charlie:charlie-validator"; do
            IFS=':' read -r host name container <<< "$host_info"
            echo "  $name ($host):"
            # Check that the override log appears
            local_pqc=$(ssh -o ConnectTimeout=5 "$host" \
                "docker logs $container 2>&1 | grep 'Overriding local PeerId with PQC' | tail -1" 2>/dev/null)
            if [ -n "$local_pqc" ]; then
                echo "    PQC override: $local_pqc"
            else
                warn "    PQC override NOT found — fix may not be deployed"
            fi
            check_health "$host" "$name" || true
            echo ""
        done
        ;;

    print-bootnodes)
        echo "# Bootnode addresses with Falcon-1024 PeerIds"
        echo "# Use these in --bootnodes or --reserved-nodes arguments"
        echo ""
        echo "# Alice"
        echo "/ip4/$ALICE_IP/tcp/30333/p2p/$ALICE_PQC_PEERID"
        echo ""
        echo "# Bob"
        echo "/ip4/$BOB_IP/tcp/30333/p2p/$BOB_PQC_PEERID"
        echo ""
        echo "# Charlie"
        echo "/ip4/$CHARLIE_IP/tcp/30333/p2p/$CHARLIE_PQC_PEERID"
        ;;

    help|*)
        echo "Usage: $0 <command>"
        echo ""
        echo "Commands:"
        echo "  status          Check current health of all validators"
        echo "  deploy-all      Deploy fix to all 3 validators (rolling restart)"
        echo "  deploy-alice    Deploy fix to Alice only"
        echo "  deploy-bob      Deploy fix to Bob only"
        echo "  deploy-charlie  Deploy fix to Charlie only"
        echo "  verify          Check that PQC PeerId override is active"
        echo "  print-bootnodes Print bootnode addresses with Falcon PeerIds"
        echo ""
        echo "Environment:"
        echo "  DOCKER_IMAGE    Override Docker image (default: $IMAGE)"
        echo ""
        echo "PQC PeerIds (Falcon-1024 derived):"
        echo "  Alice:   $ALICE_PQC_PEERID"
        echo "  Bob:     $BOB_PQC_PEERID"
        echo "  Charlie: $CHARLIE_PQC_PEERID"
        ;;
esac
