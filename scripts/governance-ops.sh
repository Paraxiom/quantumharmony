#!/bin/bash
# QuantumHarmony Governance Operations Script
# Handles backup, restore, upgrade, and maintenance

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
PROJECT_ROOT="$( cd "$SCRIPT_DIR/.." && pwd )"
BACKUP_DIR="${PROJECT_ROOT}/backups"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

# Functions
print_header() {
    echo -e "${GREEN}========================================${NC}"
    echo -e "${GREEN}$1${NC}"
    echo -e "${GREEN}========================================${NC}"
}

# Backup governance data and chain state
backup() {
    print_header "Creating Governance Backup"
    
    TIMESTAMP=$(date +%Y%m%d_%H%M%S)
    BACKUP_PATH="${BACKUP_DIR}/manual/backup_${TIMESTAMP}"
    mkdir -p "${BACKUP_PATH}"
    
    echo "📦 Backing up database..."
    docker-compose -f docker-compose-governance.yml exec -T postgres \
        pg_dump -U quantum governance > "${BACKUP_PATH}/governance.sql"
    
    echo "📦 Backing up chain data..."
    docker-compose -f docker-compose-governance.yml run --rm -v alice-data:/data \
        alpine tar czf /backup/chain-data.tar.gz /data
    mv "${BACKUP_DIR}/chain-data.tar.gz" "${BACKUP_PATH}/"
    
    echo "📦 Backing up Redis state..."
    docker-compose -f docker-compose-governance.yml exec -T redis \
        redis-cli BGSAVE
    sleep 2
    docker-compose -f docker-compose-governance.yml run --rm -v redis_data:/data \
        alpine cp /data/dump.rdb /backup/
    mv "${BACKUP_DIR}/dump.rdb" "${BACKUP_PATH}/redis.rdb"
    
    echo -e "${GREEN}✅ Backup completed: ${BACKUP_PATH}${NC}"
}

# Restore from backup
restore() {
    print_header "Restoring from Backup"
    
    if [ -z "$1" ]; then
        echo "Available backups:"
        ls -la "${BACKUP_DIR}/manual/"
        echo -e "${YELLOW}Usage: $0 restore <backup_timestamp>${NC}"
        exit 1
    fi
    
    BACKUP_PATH="${BACKUP_DIR}/manual/backup_$1"
    
    if [ ! -d "${BACKUP_PATH}" ]; then
        echo -e "${RED}❌ Backup not found: ${BACKUP_PATH}${NC}"
        exit 1
    fi
    
    echo -e "${YELLOW}⚠️  This will overwrite current data! Continue? (y/N)${NC}"
    read -r response
    if [[ ! "$response" =~ ^[Yy]$ ]]; then
        echo "Restore cancelled."
        exit 0
    fi
    
    echo "🔄 Stopping services..."
    docker-compose -f docker-compose-governance.yml down
    
    echo "🔄 Restoring database..."
    docker-compose -f docker-compose-governance.yml up -d postgres
    sleep 5
    docker-compose -f docker-compose-governance.yml exec -T postgres \
        psql -U quantum -d governance < "${BACKUP_PATH}/governance.sql"
    
    echo "🔄 Restoring chain data..."
    docker volume rm quantumharmony_alice-data || true
    docker volume create quantumharmony_alice-data
    docker run --rm -v quantumharmony_alice-data:/data \
        -v "${BACKUP_PATH}:/backup" \
        alpine tar xzf /backup/chain-data.tar.gz -C /
    
    echo "🔄 Restoring Redis..."
    docker-compose -f docker-compose-governance.yml up -d redis
    docker-compose -f docker-compose-governance.yml exec -T redis \
        redis-cli FLUSHALL
    docker cp "${BACKUP_PATH}/redis.rdb" qh_redis:/data/dump.rdb
    docker-compose -f docker-compose-governance.yml restart redis
    
    echo -e "${GREEN}✅ Restore completed${NC}"
}

# Upgrade runtime (with automatic backup)
upgrade() {
    print_header "Upgrading QuantumHarmony Runtime"
    
    echo "📸 Creating pre-upgrade backup..."
    backup
    
    echo "🔨 Building new runtime..."
    cd "${PROJECT_ROOT}"
    cargo build --release -p quantumharmony-runtime
    
    WASM_PATH="${PROJECT_ROOT}/target/release/wbuild/quantumharmony-runtime/quantumharmony_runtime.wasm"
    
    if [ ! -f "${WASM_PATH}" ]; then
        echo -e "${RED}❌ WASM runtime not found${NC}"
        exit 1
    fi
    
    echo "📤 Uploading new runtime..."
    # This would normally use sudo key or governance proposal
    # For now, showing the manual process
    echo -e "${YELLOW}To upgrade runtime:${NC}"
    echo "1. Go to https://polkadot.js.org/apps/?rpc=ws://localhost:9945"
    echo "2. Navigate to Developer > Extrinsics"
    echo "3. Select sudo > sudoUncheckedWeight"
    echo "4. Select system > setCode"
    echo "5. Upload: ${WASM_PATH}"
    echo "6. Submit transaction"
}

# Start governance network
start() {
    print_header "Starting Governance Network"
    
    echo "🚀 Starting services..."
    docker-compose -f docker-compose-governance.yml up -d
    
    echo "⏳ Waiting for services to be ready..."
    sleep 10
    
    echo "🔍 Checking service health..."
    docker-compose -f docker-compose-governance.yml ps
    
    echo -e "${GREEN}✅ Governance network started${NC}"
    echo ""
    echo "📊 Access points:"
    echo "   Polkadot.js: http://localhost:3000"
    echo "   RPC: http://localhost:9944"
    echo "   WebSocket: ws://localhost:9945"
}

# Stop governance network
stop() {
    print_header "Stopping Governance Network"
    
    echo "📸 Creating shutdown backup..."
    backup
    
    echo "🛑 Stopping services..."
    docker-compose -f docker-compose-governance.yml down
    
    echo -e "${GREEN}✅ Governance network stopped${NC}"
}

# View logs
logs() {
    docker-compose -f docker-compose-governance.yml logs -f "$@"
}

# Database operations
db() {
    case "$1" in
        "shell")
            docker-compose -f docker-compose-governance.yml exec postgres \
                psql -U quantum -d governance
            ;;
        "init")
            docker-compose -f docker-compose-governance.yml exec -T postgres \
                psql -U quantum -d governance < "${SCRIPT_DIR}/governance-db-init.sql"
            echo -e "${GREEN}✅ Database initialized${NC}"
            ;;
        "export")
            TIMESTAMP=$(date +%Y%m%d_%H%M%S)
            docker-compose -f docker-compose-governance.yml exec -T postgres \
                pg_dump -U quantum governance > "${BACKUP_DIR}/governance_export_${TIMESTAMP}.sql"
            echo -e "${GREEN}✅ Database exported to: ${BACKUP_DIR}/governance_export_${TIMESTAMP}.sql${NC}"
            ;;
        *)
            echo "Usage: $0 db [shell|init|export]"
            ;;
    esac
}

# Show usage
usage() {
    echo "QuantumHarmony Governance Operations"
    echo ""
    echo "Usage: $0 <command> [options]"
    echo ""
    echo "Commands:"
    echo "  start       - Start governance network"
    echo "  stop        - Stop governance network (with backup)"
    echo "  restart     - Restart governance network"
    echo "  backup      - Create manual backup"
    echo "  restore     - Restore from backup"
    echo "  upgrade     - Upgrade runtime (with backup)"
    echo "  logs        - View logs (optional: service name)"
    echo "  db          - Database operations (shell|init|export)"
    echo "  status      - Show network status"
    echo ""
}

# Main command handler
case "$1" in
    "start")
        start
        ;;
    "stop")
        stop
        ;;
    "restart")
        stop
        start
        ;;
    "backup")
        backup
        ;;
    "restore")
        restore "$2"
        ;;
    "upgrade")
        upgrade
        ;;
    "logs")
        shift
        logs "$@"
        ;;
    "db")
        shift
        db "$@"
        ;;
    "status")
        docker-compose -f docker-compose-governance.yml ps
        ;;
    *)
        usage
        ;;
esac