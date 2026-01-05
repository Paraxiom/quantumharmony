#!/bin/bash
# QuantumHarmony Node Operator - Quick Start
# Includes: blockchain node, VOTE SYNC messaging, and dashboard

set -e
cd "$(dirname "$0")"

echo ""
echo "╔══════════════════════════════════════════════════════════════╗"
echo "║         QuantumHarmony Node Operator v1.0                    ║"
echo "║         Post-Quantum Secure Blockchain                       ║"
echo "╚══════════════════════════════════════════════════════════════╝"
echo ""

show_help() {
    echo "Usage: ./start.sh [command]"
    echo ""
    echo "Commands:"
    echo "  start       Start all services (node + messaging + dashboard)"
    echo "  stop        Stop all services"
    echo "  restart     Restart all services"
    echo "  logs        Show live logs"
    echo "  status      Show service status"
    echo "  pull        Pull latest images"
    echo "  clean       Stop and remove all data (fresh start)"
    echo "  help        Show this help"
    echo ""
    echo "Environment variables:"
    echo "  NODE_NAME   Your validator name (default: Operator)"
    echo ""
    echo "Example:"
    echo "  NODE_NAME=MyValidator ./start.sh start"
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
    pull|update)
        check_docker
        echo "Pulling latest images..."
        docker-compose pull
        echo "Done. Restart with: ./start.sh restart"
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
