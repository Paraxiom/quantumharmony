#!/bin/bash
# QuantumHarmony Node Operator - Quick Start

cd "$(dirname "$0")"

echo "╔══════════════════════════════════════════════════════════╗"
echo "║         QuantumHarmony Node Operator                     ║"
echo "╚══════════════════════════════════════════════════════════╝"
echo ""

case "${1:-}" in
    ui|dashboard)
        echo "Starting dashboard (view-only, connects to production testnet)..."
        echo "To run your own node and produce blocks, use: ./start.sh"
        echo ""
        python3 dashboard/run.py
        ;;
    local)
        echo "Starting dashboard (connects to localhost:9944)..."
        RPC_URL=http://localhost:9944 python3 dashboard/run.py
        ;;
    docker|"")
        # Check Docker
        if ! command -v docker &> /dev/null; then
            echo "Docker not found. Run dashboard only with:"
            echo "  ./start.sh ui"
            exit 1
        fi
        if ! docker info &> /dev/null; then
            echo "Docker not running. Run dashboard only with:"
            echo "  ./start.sh ui"
            exit 1
        fi
        echo "Starting your QuantumHarmony node..."
        echo ""
        echo "  Dashboard:  http://localhost:8080"
        echo "  RPC:        http://localhost:9944"
        echo "  P2P:        30333"
        echo ""
        echo "Inject keys via dashboard to participate in block production."
        echo "Press Ctrl+C to stop."
        echo ""
        docker-compose up
        ;;
    *)
        echo "Usage: ./start.sh [command]"
        echo ""
        echo "Commands:"
        echo "  (none)    Run your node + dashboard (can produce blocks)"
        echo "  ui        Dashboard only (view production testnet)"
        echo "  local     Dashboard for local node at localhost:9944"
        ;;
esac
