#!/bin/bash
# =============================================================================
# QuantumHarmony Network Integration Tests Runner
# =============================================================================
#
# This script runs the threshold QRNG network integration tests against the
# canary production network.
#
# Usage:
#   ./scripts/run_network_tests.sh [options]
#
# Options:
#   --setup     Run one-time setup (create test accounts)
#   --verify    Verify test accounts are funded
#   --full      Run full test suite
#   --health    Check node health only
#   --quick     Run quick smoke tests
#   --all       Run everything (setup if needed, then full tests)
#
# Prerequisites:
#   - Canary network must be running (Alice, Bob, Charlie)
#   - Rust and Cargo must be installed
#   - Test accounts must be funded (for full tests)
#
# =============================================================================

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Canary network endpoints
ALICE_RPC="http://51.79.26.123:9944"
BOB_RPC="http://51.79.26.168:9944"
CHARLIE_RPC="http://209.38.225.4:9944"

# Test accounts file
TEST_ACCOUNTS_FILE="tests/test_accounts.json"

echo -e "${BLUE}"
echo "=============================================="
echo " QuantumHarmony Network Integration Tests"
echo "=============================================="
echo -e "${NC}"

# Function to check if a node is healthy
check_node_health() {
    local name=$1
    local endpoint=$2

    echo -n "  Checking $name ($endpoint)... "

    response=$(curl -s -X POST "$endpoint" \
        -H "Content-Type: application/json" \
        -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' \
        --connect-timeout 5 2>/dev/null || echo "FAILED")

    if [[ "$response" == *"isSyncing"* ]]; then
        echo -e "${GREEN}OK${NC}"
        return 0
    else
        echo -e "${RED}UNREACHABLE${NC}"
        return 1
    fi
}

# Function to check all nodes
check_all_nodes() {
    echo -e "\n${YELLOW}Checking canary network health...${NC}\n"

    local all_healthy=true

    if ! check_node_health "Alice" "$ALICE_RPC"; then all_healthy=false; fi
    if ! check_node_health "Bob" "$BOB_RPC"; then all_healthy=false; fi
    if ! check_node_health "Charlie" "$CHARLIE_RPC"; then all_healthy=false; fi

    echo ""

    if [ "$all_healthy" = true ]; then
        echo -e "${GREEN}All nodes healthy!${NC}\n"
        return 0
    else
        echo -e "${RED}Some nodes are unreachable!${NC}\n"
        return 1
    fi
}

# Function to run setup
run_setup() {
    echo -e "\n${YELLOW}Running one-time setup...${NC}\n"

    if [ -f "$TEST_ACCOUNTS_FILE" ]; then
        echo -e "${YELLOW}Warning: Test accounts file already exists.${NC}"
        read -p "Overwrite? (y/N) " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            echo "Skipping setup."
            return 0
        fi
    fi

    cargo test setup_test_accounts -- --ignored --nocapture

    echo -e "\n${GREEN}Setup complete!${NC}"
    echo -e "${YELLOW}IMPORTANT: You must fund the test accounts before running tests.${NC}"
    echo "See the output above for funding instructions."
}

# Function to verify accounts
run_verify() {
    echo -e "\n${YELLOW}Verifying test accounts are funded...${NC}\n"

    if [ ! -f "$TEST_ACCOUNTS_FILE" ]; then
        echo -e "${RED}Error: Test accounts file not found.${NC}"
        echo "Run: $0 --setup first"
        exit 1
    fi

    cargo test test_accounts_funded -- --ignored --nocapture
}

# Function to run health tests
run_health() {
    echo -e "\n${YELLOW}Running node health tests...${NC}\n"

    cargo test test_all_nodes_healthy -- --ignored --nocapture
}

# Function to run quick smoke tests
run_quick() {
    echo -e "\n${YELLOW}Running quick smoke tests...${NC}\n"

    cargo test --test network_integration_tests -- --ignored --nocapture \
        test_get_threshold_config \
        test_get_device_queues \
        print_current_round_info
}

# Function to run full test suite
run_full() {
    echo -e "\n${YELLOW}Running full test suite...${NC}\n"

    # Check nodes first
    if ! check_all_nodes; then
        echo -e "${RED}Cannot run tests - some nodes are unreachable.${NC}"
        exit 1
    fi

    # Run tests sequentially to avoid race conditions
    cargo test --test network_integration_tests -- --ignored --test-threads=1 --nocapture

    echo -e "\n${GREEN}All tests complete!${NC}"
}

# Function to run everything
run_all() {
    echo -e "\n${YELLOW}Running complete test workflow...${NC}\n"

    # Check nodes
    if ! check_all_nodes; then
        echo -e "${RED}Cannot proceed - some nodes are unreachable.${NC}"
        exit 1
    fi

    # Setup if needed
    if [ ! -f "$TEST_ACCOUNTS_FILE" ]; then
        echo -e "${YELLOW}Test accounts not found. Running setup...${NC}"
        run_setup

        echo -e "\n${YELLOW}Please fund the test accounts, then run:${NC}"
        echo "  $0 --full"
        exit 0
    fi

    # Verify accounts
    echo -e "\n${YELLOW}Verifying test accounts...${NC}"
    if ! cargo test test_accounts_funded -- --ignored --nocapture 2>/dev/null; then
        echo -e "\n${RED}Test accounts not funded!${NC}"
        echo "Please fund the accounts shown by: $0 --setup"
        exit 1
    fi

    # Run full suite
    run_full
}

# Function to show help
show_help() {
    echo "Usage: $0 [options]"
    echo ""
    echo "Options:"
    echo "  --setup     Create test accounts (run once)"
    echo "  --verify    Verify test accounts are funded"
    echo "  --health    Check node health only"
    echo "  --quick     Run quick smoke tests"
    echo "  --full      Run full test suite"
    echo "  --all       Run complete workflow"
    echo "  --help      Show this help message"
    echo ""
    echo "Examples:"
    echo "  $0 --setup    # First time setup"
    echo "  $0 --verify   # After funding accounts"
    echo "  $0 --full     # Run all tests"
    echo ""
    echo "Canary Network:"
    echo "  Alice:   $ALICE_RPC"
    echo "  Bob:     $BOB_RPC"
    echo "  Charlie: $CHARLIE_RPC"
}

# Parse arguments
case "${1:-}" in
    --setup)
        run_setup
        ;;
    --verify)
        run_verify
        ;;
    --health)
        check_all_nodes
        run_health
        ;;
    --quick)
        check_all_nodes
        run_quick
        ;;
    --full)
        run_full
        ;;
    --all)
        run_all
        ;;
    --help|-h)
        show_help
        ;;
    *)
        # Default: check health and run quick tests
        check_all_nodes
        run_quick
        ;;
esac

echo -e "\n${BLUE}Done!${NC}\n"
