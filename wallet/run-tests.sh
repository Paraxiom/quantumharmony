#!/bin/bash
# QuantumHarmony Wallet Test Runner
# Runs all tests for the Node Operator Interface

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
WALLET_DIR="$SCRIPT_DIR"
TAURI_DIR="$WALLET_DIR/src-tauri"
PROJECT_ROOT="$(dirname "$WALLET_DIR")"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

echo -e "${BLUE}╔══════════════════════════════════════════════════════════════╗${NC}"
echo -e "${BLUE}║     QuantumHarmony Node Operator Interface Test Suite        ║${NC}"
echo -e "${BLUE}╚══════════════════════════════════════════════════════════════╝${NC}"
echo ""

# Check for running node
check_node() {
    curl -s -X POST http://localhost:9944 \
        -H "Content-Type: application/json" \
        -d '{"jsonrpc":"2.0","id":1,"method":"system_health","params":[]}' \
        > /dev/null 2>&1
    return $?
}

# Run unit tests
run_unit_tests() {
    echo -e "${YELLOW}━━━ Unit Tests (No Node Required) ━━━${NC}"
    echo ""

    cd "$TAURI_DIR"

    if cargo test --lib 2>&1; then
        echo -e "\n${GREEN}✓ Unit tests passed${NC}\n"
        return 0
    else
        echo -e "\n${RED}✗ Unit tests failed${NC}\n"
        return 1
    fi
}

# Run integration tests
run_integration_tests() {
    echo -e "${YELLOW}━━━ Integration Tests (Node Required) ━━━${NC}"
    echo ""

    if check_node; then
        echo -e "${GREEN}✓ Node is running at localhost:9944${NC}\n"

        cd "$TAURI_DIR"

        if cargo test --test '*' -- --nocapture 2>&1; then
            echo -e "\n${GREEN}✓ Integration tests passed${NC}\n"
            return 0
        else
            echo -e "\n${RED}✗ Integration tests failed${NC}\n"
            return 1
        fi
    else
        echo -e "${YELLOW}⚠ Node not running - skipping integration tests${NC}"
        echo -e "  Start node with: ./target/release/quantumharmony-node --dev --tmp\n"
        return 0
    fi
}

# Run E2E scenarios
run_e2e_tests() {
    echo -e "${YELLOW}━━━ End-to-End Scenarios ━━━${NC}"
    echo ""

    if check_node; then
        cd "$WALLET_DIR"

        if cargo test --test e2e_scenarios -- --nocapture 2>&1; then
            echo -e "\n${GREEN}✓ E2E scenarios passed${NC}\n"
            return 0
        else
            echo -e "\n${RED}✗ E2E scenarios failed${NC}\n"
            return 1
        fi
    else
        echo -e "${YELLOW}⚠ Node not running - skipping E2E tests${NC}\n"
        return 0
    fi
}

# Quick RPC smoke test
run_rpc_smoke_test() {
    echo -e "${YELLOW}━━━ RPC Smoke Test ━━━${NC}"
    echo ""

    if ! check_node; then
        echo -e "${YELLOW}⚠ Node not available${NC}\n"
        return 0
    fi

    echo "Testing core RPC methods..."

    # Test system_health
    HEALTH=$(curl -s -X POST http://localhost:9944 \
        -H "Content-Type: application/json" \
        -d '{"jsonrpc":"2.0","id":1,"method":"system_health","params":[]}')

    if echo "$HEALTH" | grep -q '"result"'; then
        echo -e "  ${GREEN}✓ system_health${NC}"
    else
        echo -e "  ${RED}✗ system_health${NC}"
    fi

    # Test chain_getHeader
    HEADER=$(curl -s -X POST http://localhost:9944 \
        -H "Content-Type: application/json" \
        -d '{"jsonrpc":"2.0","id":1,"method":"chain_getHeader","params":[]}')

    if echo "$HEADER" | grep -q '"number"'; then
        BLOCK_NUM=$(echo "$HEADER" | grep -o '"number":"[^"]*"' | cut -d'"' -f4)
        echo -e "  ${GREEN}✓ chain_getHeader (block: $BLOCK_NUM)${NC}"
    else
        echo -e "  ${RED}✗ chain_getHeader${NC}"
    fi

    # Test state_getRuntimeVersion
    VERSION=$(curl -s -X POST http://localhost:9944 \
        -H "Content-Type: application/json" \
        -d '{"jsonrpc":"2.0","id":1,"method":"state_getRuntimeVersion","params":[]}')

    if echo "$VERSION" | grep -q '"specVersion"'; then
        SPEC_VER=$(echo "$VERSION" | grep -o '"specVersion":[0-9]*' | cut -d':' -f2)
        echo -e "  ${GREEN}✓ state_getRuntimeVersion (spec: $SPEC_VER)${NC}"
    else
        echo -e "  ${RED}✗ state_getRuntimeVersion${NC}"
    fi

    echo ""
}

# Main execution
main() {
    FAILED=0

    # Parse arguments
    case "${1:-all}" in
        unit)
            run_unit_tests || FAILED=1
            ;;
        integration)
            run_integration_tests || FAILED=1
            ;;
        e2e)
            run_e2e_tests || FAILED=1
            ;;
        smoke)
            run_rpc_smoke_test || FAILED=1
            ;;
        all)
            run_unit_tests || FAILED=1
            run_rpc_smoke_test || FAILED=1
            run_integration_tests || FAILED=1
            run_e2e_tests || FAILED=1
            ;;
        *)
            echo "Usage: $0 [unit|integration|e2e|smoke|all]"
            echo ""
            echo "  unit        - Run unit tests (no node required)"
            echo "  integration - Run RPC integration tests (node required)"
            echo "  e2e         - Run end-to-end scenarios (node required)"
            echo "  smoke       - Quick RPC connectivity test"
            echo "  all         - Run all tests (default)"
            exit 1
            ;;
    esac

    # Summary
    echo -e "${BLUE}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    if [ $FAILED -eq 0 ]; then
        echo -e "${GREEN}All tests completed successfully!${NC}"
    else
        echo -e "${RED}Some tests failed. Check output above.${NC}"
        exit 1
    fi
}

main "$@"
