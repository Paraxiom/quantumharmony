# QuantumHarmony Quick Start

## TL;DR

```bash
# Get testnet tokens
curl -X POST http://YOUR_NODE_IP:8080/drip \
  -H "Content-Type: application/json" \
  -d '{"address": "5YourAddressHere..."}'

# Check balance
curl "http://YOUR_NODE_IP:8080/balance?address=5YourAddressHere..."

# View in block explorer
open "https://polkadot.js.org/apps/?rpc=wss://v1.quantumharmony.network"
```

## Endpoints

| Service | URL |
|---------|-----|
| RPC | `https://v1.quantumharmony.network` |
| WSS | `wss://v1.quantumharmony.network` |
| Faucet | `http://YOUR_NODE_IP:8080` |

## Key Info

- **Token:** QMHY (18 decimals)
- **Block time:** 6 seconds
- **Crypto:** SPHINCS+ (post-quantum)
- **Faucet drip:** 100 QMHY per request

## Run a Node

```bash
./quantumharmony-node --chain local --name MyNode \
  --bootnodes /ip4/YOUR_NODE_IP/tcp/30333/p2p/12D3KooWNpaTf134DUqez17tRCLPwdgBeQGAwh7hV94iPnd1u37d
```
