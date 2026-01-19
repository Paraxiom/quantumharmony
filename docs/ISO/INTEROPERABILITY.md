# ISO 23631 DLT Interoperability Specification

## Overview

This document specifies QuantumHarmony's interoperability interfaces following ISO 23631:2024 guidelines.

**Standard:** ISO 23631:2024 - Blockchain and distributed ledger technologies — DLT systems interaction

---

## Interoperability Layers

```
┌─────────────────────────────────────────────────────────────────────────────┐
│                    ISO 23631 INTEROPERABILITY STACK                          │
├─────────────────────────────────────────────────────────────────────────────┤
│                                                                              │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ APPLICATION INTEROPERABILITY                                         │    │
│  │ Cross-application data exchange                                      │    │
│  ├─────────────────────────────────────────────────────────────────────┤    │
│  │ QH: Dashboard ←→ External Applications                               │    │
│  │     • WebSocket subscriptions for real-time data                     │    │
│  │     • REST-compatible JSON-RPC interface                             │    │
│  │     • Webhook callbacks for event notifications                      │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ SEMANTIC INTEROPERABILITY                                            │    │
│  │ Shared meaning of data across systems                                │    │
│  ├─────────────────────────────────────────────────────────────────────┤    │
│  │ QH: ISO 22739 vocabulary alignment                                   │    │
│  │     • Standardized signal schema (see below)                         │    │
│  │     • Common data types (H256, AccountId, Balance)                   │    │
│  │     • Event naming conventions                                       │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ SYNTACTIC INTEROPERABILITY                                           │    │
│  │ Data format and encoding standards                                   │    │
│  ├─────────────────────────────────────────────────────────────────────┤    │
│  │ QH: SCALE codec (Substrate standard)                                 │    │
│  │     • JSON-RPC 2.0 wire format                                       │    │
│  │     • Hex-encoded binary data (0x prefix)                            │    │
│  │     • SS58 address encoding                                          │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                    │                                         │
│                                    ▼                                         │
│  ┌─────────────────────────────────────────────────────────────────────┐    │
│  │ NETWORK INTEROPERABILITY                                             │    │
│  │ Transport and protocol compatibility                                 │    │
│  ├─────────────────────────────────────────────────────────────────────┤    │
│  │ QH: libp2p networking                                                │    │
│  │     • HTTP/1.1 + HTTP/2 for RPC                                      │    │
│  │     • WebSocket for subscriptions                                    │    │
│  │     • TCP + Noise protocol for P2P                                   │    │
│  └─────────────────────────────────────────────────────────────────────┘    │
│                                                                              │
└─────────────────────────────────────────────────────────────────────────────┘
```

---

## Signal Format Specification

### ISO-Compliant Signal Schema v1.0

```json
{
  "$schema": "https://json-schema.org/draft/2020-12/schema",
  "$id": "https://quantumharmony.io/schemas/signal-v1.json",
  "title": "QuantumHarmony Signal",
  "description": "ISO 23631 compliant signal format for cross-node data exchange",
  "type": "object",
  "required": ["version", "schema", "source", "payload"],
  "properties": {
    "version": {
      "type": "string",
      "const": "1.0",
      "description": "Signal format version"
    },
    "schema": {
      "type": "string",
      "pattern": "^iso:tc307:signal:v[0-9]+$",
      "description": "Schema identifier",
      "examples": ["iso:tc307:signal:v1"]
    },
    "source": {
      "type": "object",
      "required": ["node_id", "timestamp", "signature"],
      "properties": {
        "node_id": {
          "type": "string",
          "pattern": "^0x[a-fA-F0-9]{64}$",
          "description": "256-bit node identifier (libp2p PeerId hash)"
        },
        "reporter_id": {
          "type": "string",
          "pattern": "^5[a-zA-Z0-9]{47}$",
          "description": "SS58-encoded reporter account (optional)"
        },
        "timestamp": {
          "type": "integer",
          "minimum": 0,
          "description": "Unix timestamp in milliseconds"
        },
        "signature": {
          "type": "string",
          "pattern": "^falcon1024:0x[a-fA-F0-9]+$",
          "description": "Falcon-1024 signature over (schema + payload + timestamp)"
        }
      }
    },
    "payload": {
      "type": "object",
      "required": ["type", "data"],
      "properties": {
        "type": {
          "type": "string",
          "enum": ["qrng_entropy", "oracle_price", "oracle_data", "attestation", "custom"],
          "description": "Signal type classification"
        },
        "feed_id": {
          "type": "string",
          "description": "Oracle feed identifier (for oracle types)"
        },
        "data": {
          "type": "string",
          "pattern": "^0x[a-fA-F0-9]*$",
          "description": "Hex-encoded payload data"
        },
        "metadata": {
          "type": "object",
          "additionalProperties": true,
          "description": "Type-specific metadata"
        }
      }
    },
    "routing": {
      "type": "object",
      "description": "Optional routing hints for network propagation",
      "properties": {
        "ttl": {
          "type": "integer",
          "minimum": 0,
          "maximum": 255,
          "description": "Time-to-live hop count"
        },
        "priority": {
          "type": "string",
          "enum": ["low", "normal", "high", "critical"],
          "description": "Processing priority"
        },
        "target_nodes": {
          "type": "array",
          "items": { "type": "string" },
          "description": "Specific target node IDs (empty = broadcast)"
        }
      }
    }
  }
}
```

### Signal Type Specifications

#### QRNG Entropy Signal

```json
{
  "version": "1.0",
  "schema": "iso:tc307:signal:v1",
  "source": {
    "node_id": "0x1234...abcd",
    "timestamp": 1705680000000,
    "signature": "falcon1024:0x..."
  },
  "payload": {
    "type": "qrng_entropy",
    "data": "0x7f3c9a2b1e4d8c6f5a0b9e2d7c4f1a8b3e6d9c0f5a2b7e4d1c8f3a6b9e0d2c7f",
    "metadata": {
      "source_type": "crypto4a",
      "qber": 0.005,
      "bits": 256,
      "certification": "NIST SP 800-90B"
    }
  },
  "routing": {
    "ttl": 10,
    "priority": "high"
  }
}
```

#### Oracle Price Signal

```json
{
  "version": "1.0",
  "schema": "iso:tc307:signal:v1",
  "source": {
    "node_id": "0x1234...abcd",
    "reporter_id": "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
    "timestamp": 1705680000000,
    "signature": "falcon1024:0x..."
  },
  "payload": {
    "type": "oracle_price",
    "feed_id": "BTC/USD",
    "data": "0x00000000000000000000000000000000000000000000000000009184e72a000000",
    "metadata": {
      "price_usd": "42000.00",
      "decimal_places": 8,
      "sources": ["coinbase", "binance", "kraken"],
      "aggregation": "median"
    }
  }
}
```

#### Document Attestation Signal

```json
{
  "version": "1.0",
  "schema": "iso:tc307:signal:v1",
  "source": {
    "node_id": "0x1234...abcd",
    "reporter_id": "5GrwvaEF5zXb26Fz9rcQpDWS57CtERHpNehXCPcNoHGKutQY",
    "timestamp": 1705680000000,
    "signature": "falcon1024:0x..."
  },
  "payload": {
    "type": "attestation",
    "data": "0x8f434346648f6b96df89dda901c5176b10a6d83961dd3c1ac88b59b2dc327aa4",
    "metadata": {
      "document_type": "contract",
      "hash_algorithm": "blake2b-256",
      "notary_id": "5FHneW46xGXgs5mUiveU4sbTyGBzmstUspZC92UhjJM694ty",
      "jurisdiction": "CA-QC"
    }
  }
}
```

---

## RPC Interface Specification

### Connection Endpoints

| Endpoint | Protocol | Port | Purpose |
|----------|----------|------|---------|
| `/` | HTTP POST | 9944 | JSON-RPC requests |
| `/ws` | WebSocket | 9944 | Subscriptions |
| `/health` | HTTP GET | 9944 | Health check |
| `/metrics` | HTTP GET | 9615 | Prometheus metrics |

### Authentication

```
┌─────────────────────────────────────────────────────────────────┐
│                    RPC AUTHENTICATION                            │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  Public Methods (no auth required):                             │
│  • system_* - Chain metadata and health                         │
│  • chain_* - Block and state queries                            │
│  • state_* - Storage queries                                    │
│                                                                  │
│  Authenticated Methods (signature required):                    │
│  • author_* - Transaction submission                            │
│  • gateway_* - Signed transaction gateway                       │
│  • oracle_submitSignal - Reporter signals                       │
│                                                                  │
│  Validator-Only Methods:                                        │
│  • author_rotateKeys - Session key rotation                     │
│  • governance_* - Validator governance actions                  │
│                                                                  │
│  Authentication Header:                                         │
│  X-QH-Signature: falcon1024:<timestamp>:<signature>             │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Complete RPC Method Reference

#### System Module

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `system_name` | `[]` | `string` | None |
| `system_version` | `[]` | `string` | None |
| `system_chain` | `[]` | `string` | None |
| `system_chainType` | `[]` | `string` | None |
| `system_health` | `[]` | `{peers, isSyncing, shouldHavePeers}` | None |
| `system_peers` | `[]` | `[{peerId, roles, bestHash, bestNumber}]` | None |
| `system_properties` | `[]` | `{ss58Format, tokenDecimals, tokenSymbol}` | None |

#### Chain Module

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `chain_getBlockHash` | `[blockNumber?]` | `H256` | None |
| `chain_getBlock` | `[hash?]` | `{block, justifications}` | None |
| `chain_getHeader` | `[hash?]` | `Header` | None |
| `chain_getFinalizedHead` | `[]` | `H256` | None |

#### State Module

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `state_getStorage` | `[key, hash?]` | `hex` | None |
| `state_getStorageHash` | `[key, hash?]` | `H256` | None |
| `state_getStorageSize` | `[key, hash?]` | `u64` | None |
| `state_getMetadata` | `[hash?]` | `hex` | None |
| `state_getRuntimeVersion` | `[hash?]` | `RuntimeVersion` | None |
| `state_queryStorage` | `[keys, from, to?]` | `[{block, changes}]` | None |

#### Author Module

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `author_submitExtrinsic` | `[extrinsic]` | `H256` | Signed |
| `author_pendingExtrinsics` | `[]` | `[hex]` | None |
| `author_rotateKeys` | `[]` | `hex` | Validator |
| `author_hasSessionKeys` | `[keys]` | `bool` | None |
| `author_insertKey` | `[keyType, suri, publicKey]` | `null` | Validator |

#### Gateway Module (QuantumHarmony Custom)

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `gateway_submit` | `[{from, to, amount, nonce, genesisHash, secretKey}]` | `{hash, segment, status}` | Signed |
| `gateway_getNonce` | `[address]` | `u64` | None |
| `gateway_getBalance` | `[address]` | `{free, reserved, frozen}` | None |
| `gateway_estimateFee` | `[extrinsic]` | `{baseFee, lenFee, adjustedWeightFee}` | None |

#### Oracle Module (QuantumHarmony Custom)

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `oracle_submitSignal` | `[signal]` | `{hash, status}` | Reporter |
| `oracle_getAvailableSignals` | `[{type?, from?, limit?}]` | `[Signal]` | None |
| `oracle_acceptExternalSignal` | `[signalId]` | `{accepted}` | Validator |
| `oracle_getReporters` | `[]` | `[{id, stake, feeds, reputation}]` | None |
| `oracle_getFeeds` | `[]` | `[{id, name, reporters, lastUpdate}]` | None |
| `oracle_getFeedValue` | `[feedId]` | `{value, timestamp, reporter}` | None |

#### QRNG Module (QuantumHarmony Custom)

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `qrng_getEntropy` | `[{bytes}]` | `{entropy, source, qber}` | None |
| `qrng_fetchFromCrypto4a` | `[]` | `{entropy, timestamp, qber}` | Validator |
| `qrng_getPoolStatus` | `[]` | `{size, sources, healthy, lastUpdate}` | None |
| `qrng_pushToQueue` | `[signal]` | `{queued, position}` | Validator |
| `qrng_getSources` | `[]` | `[{id, type, status, qber}]` | None |

#### Notarial Module (QuantumHarmony Custom)

| Method | Parameters | Returns | Auth |
|--------|------------|---------|------|
| `notarial_attest` | `[{documentHash, metadata}]` | `{attestationId, timestamp}` | Signed |
| `notarial_verify` | `[attestationId]` | `{valid, timestamp, attester, documentHash}` | None |
| `notarial_getAttestations` | `[{attester?, from?, to?}]` | `[Attestation]` | None |
| `notarial_revokeAttestation` | `[attestationId, reason]` | `{revoked}` | Original Attester |

---

## Subscription Interface

### WebSocket Subscription Methods

```javascript
// Subscribe to new blocks
{
  "jsonrpc": "2.0",
  "id": 1,
  "method": "chain_subscribeNewHeads",
  "params": []
}
// Returns subscription ID, then pushes headers

// Subscribe to finalized blocks
{
  "jsonrpc": "2.0",
  "id": 2,
  "method": "chain_subscribeFinalizedHeads",
  "params": []
}

// Subscribe to storage changes
{
  "jsonrpc": "2.0",
  "id": 3,
  "method": "state_subscribeStorage",
  "params": [["0x..."]]  // Storage keys to watch
}

// Subscribe to oracle signals (QH custom)
{
  "jsonrpc": "2.0",
  "id": 4,
  "method": "oracle_subscribeSignals",
  "params": [{"type": "qrng_entropy"}]  // Optional filter
}

// Subscribe to QRNG pool updates (QH custom)
{
  "jsonrpc": "2.0",
  "id": 5,
  "method": "qrng_subscribePoolUpdates",
  "params": []
}
```

### Subscription Message Format

```json
{
  "jsonrpc": "2.0",
  "method": "chain_newHead",
  "params": {
    "subscription": "0x1234",
    "result": {
      "parentHash": "0x...",
      "number": "0x1a2b3c",
      "stateRoot": "0x...",
      "extrinsicsRoot": "0x...",
      "digest": {...}
    }
  }
}
```

---

## Cross-Chain Interoperability

### Relay Chain Integration (Future)

```
┌─────────────────────────────────────────────────────────────────┐
│                    XCMP MESSAGING (PLANNED)                      │
├─────────────────────────────────────────────────────────────────┤
│                                                                  │
│  QuantumHarmony ←──────────────────────────→ Relay Chain        │
│       │                                           │              │
│       │  1. Register as parachain                │              │
│       │  2. Submit PoV blocks                    │              │
│       │  3. Receive finality from relay          │              │
│       │                                           │              │
│       └──── XCMP Messages ────────────────────────┘              │
│                                                                  │
│  Message Types:                                                 │
│  • TransferAsset - Cross-chain token transfers                  │
│  • Transact - Execute calls on other chains                     │
│  • QueryResponse - Inter-chain queries                          │
│  • OracleData - Share oracle signals across chains              │
│                                                                  │
└─────────────────────────────────────────────────────────────────┘
```

### Bridge Protocol (Future)

| Bridge Type | Target | Status |
|-------------|--------|--------|
| Light Client | Ethereum | Planned |
| Relay | Polkadot | Planned |
| Hash Time Lock | Bitcoin | Research |
| IBC | Cosmos | Research |

---

## Error Codes

### Standard JSON-RPC Errors

| Code | Message | Description |
|------|---------|-------------|
| -32700 | Parse error | Invalid JSON |
| -32600 | Invalid request | Missing required fields |
| -32601 | Method not found | Unknown RPC method |
| -32602 | Invalid params | Wrong parameter types |
| -32603 | Internal error | Server-side error |

### QuantumHarmony Custom Errors

| Code | Message | Description |
|------|---------|-------------|
| -32000 | Transaction pool error | Tx rejected by pool |
| -32001 | Bad signature | Signature verification failed |
| -32002 | Insufficient balance | Not enough funds |
| -32003 | Invalid nonce | Wrong nonce value |
| -32004 | Not a reporter | Caller not approved reporter |
| -32005 | Not a validator | Caller not a validator |
| -32006 | QRNG unavailable | No entropy sources available |
| -32007 | Signal rejected | Signal failed validation |
| -32008 | Rate limited | Too many requests |

---

## SDK Support

### JavaScript/TypeScript

```typescript
import { ApiPromise, WsProvider } from '@polkadot/api';
import { quantumHarmonyTypes } from '@quantumharmony/types';

const api = await ApiPromise.create({
  provider: new WsProvider('wss://node.quantumharmony.io'),
  types: quantumHarmonyTypes,
});

// Query oracle feed
const btcPrice = await api.query.oracle.feeds('BTC/USD');

// Subscribe to signals
api.rpc.oracle.subscribeSignals({ type: 'qrng_entropy' }, (signal) => {
  console.log('New QRNG entropy:', signal.payload.data);
});
```

### Python

```python
from substrateinterface import SubstrateInterface

substrate = SubstrateInterface(
    url="wss://node.quantumharmony.io",
    type_registry_preset="quantumharmony"
)

# Get QRNG entropy
result = substrate.rpc_request("qrng_getEntropy", [{"bytes": 32}])
print(f"Entropy: {result['result']['entropy']}")

# Submit oracle signal
signal = {
    "version": "1.0",
    "schema": "iso:tc307:signal:v1",
    # ... full signal
}
result = substrate.rpc_request("oracle_submitSignal", [signal])
```

### Rust

```rust
use jsonrpsee::ws_client::WsClientBuilder;
use quantumharmony_rpc::OracleRpcClient;

#[tokio::main]
async fn main() {
    let client = WsClientBuilder::default()
        .build("wss://node.quantumharmony.io")
        .await?;

    // Get available signals
    let signals = client.get_available_signals(None).await?;

    for signal in signals {
        println!("Signal: {:?}", signal);
    }
}
```

---

## References

- [ISO 23631:2024](https://www.iso.org/standard/76573.html) - DLT Systems Interaction
- [JSON-RPC 2.0 Specification](https://www.jsonrpc.org/specification)
- [Substrate RPC Documentation](https://docs.substrate.io/reference/rpc/)
- [libp2p Specification](https://github.com/libp2p/specs)
