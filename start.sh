#!/bin/bash

# Start a local QuantumHarmony node connecting to the dev3 network

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
DATA_DIR="${HOME}/local-node-data"

docker rm -f local-node 2>/dev/null

docker run -d --name local-node \
  -p 9944:9944 -p 30333:30333 \
  -v "${DATA_DIR}:/data" \
  -v "${SCRIPT_DIR}/chainspec-production.json:/chainspec.json:ro" \
  sylvaincormier/quantumharmony-node:mesh-forum \
  --chain=/chainspec.json \
  --base-path=/data \
  --port=30333 \
  --rpc-port=9944 \
  --rpc-cors=all \
  --rpc-methods=Unsafe \
  --unsafe-rpc-external \
  --name=LocalNode \
  --bootnodes=/ip4/51.79.26.168/tcp/30333/p2p/12D3KooWHdiAxVd8uMQR1hGWXccidmfCwLqcMpGwR6QcTP6QRMuD \
  --bootnodes=/ip4/51.79.26.123/tcp/30333/p2p/12D3KooWEyoppNCUx8Yx66oV9fJnriXwCcXwDDUA2kj6vnc6iDEp \
  --bootnodes=/ip4/209.38.225.4/tcp/30333/p2p/12D3KooWSCufgHzV4fCwRijfH2k3abrpAJxTKxEvN1FDuRXA2U9x

echo "Node starting... View logs with: docker logs -f local-node"
echo "RPC available at: ws://localhost:9944"
