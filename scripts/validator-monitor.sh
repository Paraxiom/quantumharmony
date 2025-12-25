#!/bin/bash
# QuantumHarmony Validator Monitor Daemon
# Monitors validator health and auto-restarts on failure
set -e

# === CONFIGURATION ===
MONITOR_INTERVAL="${MONITOR_INTERVAL:-30}"  # Check every 30 seconds
DATA_DIR="${DATA_DIR:-$HOME/.quantumharmony}"
RPC_PORT="${RPC_PORT:-9944}"
LOG_FILE="${LOG_FILE:-$DATA_DIR/monitor.log}"
MAX_BLOCK_STALL="${MAX_BLOCK_STALL:-120}"  # Alert if no new blocks for 2 minutes
MIN_PEERS="${MIN_PEERS:-1}"  # Minimum required peers
RESTART_ON_CRASH="${RESTART_ON_CRASH:-true}"

# Alert configuration (optional)
ALERT_WEBHOOK="${ALERT_WEBHOOK:-}"  # Discord/Slack webhook URL
ALERT_EMAIL="${ALERT_EMAIL:-}"

# State tracking
LAST_BLOCK=0
LAST_BLOCK_TIME=0
STALL_ALERTED=false

# === FUNCTIONS ===
log() {
    local msg="[$(date '+%Y-%m-%d %H:%M:%S')] $1"
    echo "$msg" | tee -a "$LOG_FILE"
}

send_alert() {
    local title="$1"
    local message="$2"
    local severity="${3:-warning}"  # info, warning, critical

    log "ALERT [$severity]: $title - $message"

    # Send to webhook if configured
    if [ -n "$ALERT_WEBHOOK" ]; then
        curl -s -X POST "$ALERT_WEBHOOK" \
            -H "Content-Type: application/json" \
            -d "{\"content\":\"**[$severity]** $title\\n$message\"}" \
            > /dev/null 2>&1 || true
    fi

    # Log to alert file
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] [$severity] $title: $message" >> "$DATA_DIR/alerts.log"
}

check_node_running() {
    if [ -f "$DATA_DIR/validator.pid" ]; then
        local pid=$(cat "$DATA_DIR/validator.pid")
        if kill -0 "$pid" 2>/dev/null; then
            return 0
        fi
    fi
    # Also check by process name
    if pgrep -x quantumharmony-node > /dev/null; then
        return 0
    fi
    return 1
}

get_node_health() {
    local rpc_url="http://localhost:$RPC_PORT"
    local health=$(curl -s --max-time 5 "$rpc_url" -H "Content-Type: application/json" \
        -d '{"id":1,"jsonrpc":"2.0","method":"system_health","params":[]}' 2>/dev/null)

    if [ -z "$health" ]; then
        echo "UNREACHABLE"
        return 1
    fi

    local peers=$(echo "$health" | python3 -c "import sys,json; print(json.load(sys.stdin)['result']['peers'])" 2>/dev/null || echo "0")
    local syncing=$(echo "$health" | python3 -c "import sys,json; print(json.load(sys.stdin)['result']['isSyncing'])" 2>/dev/null || echo "false")

    echo "peers:$peers,syncing:$syncing"
    return 0
}

get_block_number() {
    local rpc_url="http://localhost:$RPC_PORT"
    local block=$(curl -s --max-time 5 "$rpc_url" -H "Content-Type: application/json" \
        -d '{"id":1,"jsonrpc":"2.0","method":"chain_getHeader","params":[]}' 2>/dev/null)

    if [ -z "$block" ]; then
        echo "0"
        return 1
    fi

    local num=$(echo "$block" | python3 -c "import sys,json; print(int(json.load(sys.stdin)['result']['number'], 16))" 2>/dev/null || echo "0")
    echo "$num"
}

restart_node() {
    log "Attempting to restart node..."
    if [ -f "$DATA_DIR/../scripts/validator-start.sh" ]; then
        bash "$DATA_DIR/../scripts/validator-start.sh" restart
    elif [ -f "$HOME/quantumharmony/scripts/validator-start.sh" ]; then
        bash "$HOME/quantumharmony/scripts/validator-start.sh" restart
    else
        log "ERROR: Cannot find validator-start.sh script"
        return 1
    fi
}

monitor_loop() {
    log "Starting validator monitor (interval: ${MONITOR_INTERVAL}s)"
    log "  Min peers: $MIN_PEERS"
    log "  Max block stall: ${MAX_BLOCK_STALL}s"
    log "  Auto restart: $RESTART_ON_CRASH"

    while true; do
        local current_time=$(date +%s)

        # Check 1: Is node process running?
        if ! check_node_running; then
            send_alert "Node Crashed" "Validator process is not running" "critical"
            if [ "$RESTART_ON_CRASH" = "true" ]; then
                restart_node
                sleep 30  # Give it time to start
            fi
            sleep "$MONITOR_INTERVAL"
            continue
        fi

        # Check 2: Is RPC responding?
        local health=$(get_node_health)
        if [ "$health" = "UNREACHABLE" ]; then
            send_alert "RPC Unreachable" "Node is running but RPC is not responding" "warning"
            sleep "$MONITOR_INTERVAL"
            continue
        fi

        # Parse health data
        local peers=$(echo "$health" | sed 's/.*peers:\([0-9]*\).*/\1/')
        local syncing=$(echo "$health" | sed 's/.*syncing:\([^,]*\).*/\1/')

        # Check 3: Peer count
        if [ "$peers" -lt "$MIN_PEERS" ]; then
            send_alert "Low Peers" "Only $peers peers connected (min: $MIN_PEERS)" "warning"
        fi

        # Check 4: Block production
        local current_block=$(get_block_number)
        if [ "$current_block" -gt "$LAST_BLOCK" ]; then
            LAST_BLOCK=$current_block
            LAST_BLOCK_TIME=$current_time
            STALL_ALERTED=false
            log "Block: $current_block, Peers: $peers, Syncing: $syncing"
        else
            local stall_time=$((current_time - LAST_BLOCK_TIME))
            if [ "$stall_time" -gt "$MAX_BLOCK_STALL" ] && [ "$STALL_ALERTED" = "false" ]; then
                send_alert "Block Stall" "No new blocks for ${stall_time}s (stuck at #$LAST_BLOCK)" "critical"
                STALL_ALERTED=true
            fi
        fi

        # Write status file for external monitoring
        cat > "$DATA_DIR/status.json" << EOF
{
    "timestamp": $current_time,
    "block": $current_block,
    "peers": $peers,
    "syncing": $syncing,
    "stalled": $STALL_ALERTED,
    "last_block_time": $LAST_BLOCK_TIME
}
EOF

        sleep "$MONITOR_INTERVAL"
    done
}

status() {
    if [ -f "$DATA_DIR/status.json" ]; then
        cat "$DATA_DIR/status.json" | python3 -c "
import sys, json
d = json.load(sys.stdin)
print(f'Block: {d[\"block\"]}')
print(f'Peers: {d[\"peers\"]}')
print(f'Syncing: {d[\"syncing\"]}')
print(f'Stalled: {d[\"stalled\"]}')
"
    else
        echo "No status file found. Monitor may not be running."
    fi
}

# === MAIN ===
mkdir -p "$DATA_DIR"

case "${1:-start}" in
    start)
        # Run in foreground for systemd/docker
        monitor_loop
        ;;
    daemon)
        # Run in background
        nohup "$0" start > /dev/null 2>&1 &
        echo "Monitor started in background (PID: $!)"
        ;;
    stop)
        pkill -f "validator-monitor.sh" 2>/dev/null || true
        echo "Monitor stopped"
        ;;
    status)
        status
        ;;
    *)
        echo "Usage: $0 {start|daemon|stop|status}"
        echo ""
        echo "Environment variables:"
        echo "  MONITOR_INTERVAL  - Check interval in seconds (default: 30)"
        echo "  DATA_DIR          - Data directory (default: ~/.quantumharmony)"
        echo "  RPC_PORT          - RPC port (default: 9944)"
        echo "  MAX_BLOCK_STALL   - Alert if no blocks for N seconds (default: 120)"
        echo "  MIN_PEERS         - Minimum required peers (default: 1)"
        echo "  RESTART_ON_CRASH  - Auto-restart on crash (default: true)"
        echo "  ALERT_WEBHOOK     - Discord/Slack webhook URL (optional)"
        exit 1
        ;;
esac
