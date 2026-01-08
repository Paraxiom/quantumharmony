#!/bin/bash
# QuantumHarmony Node Operator - Quick Start v1.1
# Includes: blockchain node, VOTE SYNC messaging, and dashboard
# Updated: January 2026 - Fixed cache/CORS issues

set -e
cd "$(dirname "$0")"

VERSION="1.1.0"
TIMESTAMP=$(date +%s)

echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║         QuantumHarmony Node Operator v${VERSION}                 ║"
echo "║         Post-Quantum Secure Blockchain                       ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

# Default bootnodes for production testnet
DEFAULT_BOOTNODES="/ip4/51.79.26.123/tcp/30333/p2p/12D3KooWDmLjhsvwEh3Xdat6daVhRm87ed88J9Sx4ti44osaDM8W,/ip4/51.79.26.168/tcp/30333/p2p/12D3KooWDQp7gSEEHgpGpvnui67v8s3PQ6RvYpocu96WvyuYwak1,/ip4/209.38.225.4/tcp/30333/p2p/12D3KooWPA9JZqTaDokCDToirUuA6DcfPuc2QN9DSzaJvMe3Yvcy"

# Export environment variables
export NODE_NAME="${NODE_NAME:-Operator}"
export BOOTNODES="${BOOTNODES:-$DEFAULT_BOOTNODES}"
export VALIDATOR="${VALIDATOR:-true}"
export RPC_METHODS="${RPC_METHODS:-Unsafe}"

show_help() {
    echo "Usage: ./start.sh [command]"
    echo ""
    echo "Commands:"
    echo "  start       Start all services (node + messaging + dashboard) [default]"
    echo "  ui          Dashboard only - no Docker needed (port 8081)"
    echo "  stop        Stop all services"
    echo "  restart     Restart all services"
    echo "  logs        Show live logs"
    echo "  status      Show service status"
    echo "  pull        Pull latest images (no cache)"
    echo "  fresh       Full update: stop, remove images, pull fresh, start"
    echo "  clean       Stop and remove all data (WARNING: deletes blockchain data)"
    echo "  help        Show this help"
    echo ""
    echo "Environment variables:"
    echo "  NODE_NAME   Your validator name (default: Operator)"
    echo "  BOOTNODES   Comma-separated bootnode addresses"
    echo "  VALIDATOR   Run as validator true/false (default: true)"
    echo "  RPC_URL     RPC endpoint for 'ui' mode (default: Alice production)"
    echo ""
    echo "Examples:"
    echo "  ./start.sh                              # Start full node + dashboard"
    echo "  NODE_NAME=Edwin ./start.sh              # Start as 'Edwin'"
    echo "  ./start.sh ui                           # Dashboard only (no Docker)"
    echo "  ./start.sh fresh                        # Full update and restart"
    echo ""
}

check_docker() {
    if ! command -v docker &> /dev/null; then
        echo "ERROR: Docker not found."
        echo "Please install Docker: https://docs.docker.com/get-docker/"
        exit 1
    fi
    if ! docker info &> /dev/null; then
        echo "ERROR: Docker daemon not running."
        echo "Please start Docker and try again."
        exit 1
    fi
}

case "${1:-start}" in
    start|up|"")
        check_docker
        echo "Starting QuantumHarmony Node Operator..."
        echo ""
        echo "Services:"
        echo "  Dashboard:    http://localhost:8080"
        echo "  RPC:          http://localhost:9944"
        echo "  VOTE SYNC:    http://localhost:9955"
        echo "  P2P:          port 30333"
        echo ""
        echo "Node Name: ${NODE_NAME:-Operator}"
        echo ""
        echo "Press Ctrl+C to stop."
        echo ""
        docker-compose up -d
        echo ""
        echo "Services started! Opening dashboard..."
        sleep 2
        docker-compose logs -f
        ;;
    ui|dashboard-only)
        echo "Starting dashboard only (connects to production testnet)..."
        echo ""
        echo "  Dashboard:  http://localhost:8081"
        echo "  Network:    Production testnet (Alice)"
        echo ""
        echo "To connect to local node: RPC_URL=http://localhost:9944 ./start.sh ui"
        echo ""
        python3 run.py
        ;;
    stop|down)
        check_docker
        echo "Stopping all services..."
        docker-compose down
        echo "Done."
        ;;
    restart)
        check_docker
        echo "Restarting all services..."
        docker-compose down
        docker-compose up -d
        echo "Done. View logs with: ./start.sh logs"
        ;;
    logs)
        check_docker
        docker-compose logs -f
        ;;
    status|ps)
        check_docker
        docker-compose ps
        ;;
    pull)
        check_docker
        echo "Pulling latest images (no cache)..."
        docker-compose pull --ignore-pull-failures
        docker pull sylvaincormier/quantumharmony-node:latest --quiet || true
        docker pull sylvaincormier/quantumharmony-node-operator:latest --quiet || true
        echo "Done. Restart with: ./start.sh restart"
        ;;
    fresh|update)
        check_docker
        echo "Performing fresh start (stop, remove images, pull latest, start)..."
        echo "Build timestamp: ${TIMESTAMP}"
        echo ""
        echo "Stopping containers..."
        docker-compose down 2>/dev/null || true
        docker stop quantumharmony-node quantumharmony-dashboard quantumharmony-operator quantumharmony-proxy 2>/dev/null || true
        docker rm quantumharmony-node quantumharmony-dashboard quantumharmony-operator quantumharmony-proxy 2>/dev/null || true
        echo ""
        echo "Removing old images (forcing fresh pull)..."
        docker rmi sylvaincormier/quantumharmony-node:latest 2>/dev/null || true
        docker rmi sylvaincormier/quantumharmony-node-operator:latest 2>/dev/null || true
        docker rmi nginx:alpine 2>/dev/null || true
        echo ""
        echo "Clearing Docker build cache..."
        docker builder prune -f 2>/dev/null || true
        echo ""
        echo "Pulling latest code..."
        git pull origin main 2>/dev/null || echo "Git pull skipped (not a git repo or no remote)"
        echo ""
        echo "Pulling fresh images (no cache)..."
        docker-compose pull --ignore-pull-failures
        echo ""
        echo "Configuration:"
        echo "  NODE_NAME:  ${NODE_NAME}"
        echo "  VALIDATOR:  ${VALIDATOR}"
        echo "  BOOTNODES:  (${#BOOTNODES} chars)"
        echo ""
        echo "Starting services..."
        docker-compose up -d --force-recreate --remove-orphans
        echo ""
        echo "Waiting for services to initialize..."
        sleep 5
        echo ""
        echo "Done! Services:"
        echo "  Dashboard:    http://localhost:8080"
        echo "  RPC:          http://localhost:9944"
        echo "  VOTE SYNC:    http://localhost:9955"
        echo ""
        echo "Checking health..."
        curl -s http://localhost:9944/health 2>/dev/null && echo " Node: OK" || echo " Node: Starting..."
        echo ""
        echo "View logs with: ./start.sh logs"
        ;;
    clean|reset)
        check_docker
        echo "WARNING: This will delete all local blockchain data!"
        read -p "Are you sure? (y/N) " -n 1 -r
        echo
        if [[ $REPLY =~ ^[Yy]$ ]]; then
            docker-compose down -v
            echo "All data removed. Start fresh with: ./start.sh"
        else
            echo "Cancelled."
        fi
        ;;
    help|--help|-h)
        show_help
        ;;
    *)
        echo "Unknown command: $1"
        show_help
        exit 1
        ;;
esac
