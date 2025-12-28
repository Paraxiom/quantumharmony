# QuantumHarmony Notarial Service

Post-quantum secure document attestation on the QuantumHarmony blockchain.

## Features

- **Document Attestation**: Create immutable on-chain proof that a document existed at a specific time
- **Document Verification**: Check if a document has been attested on the blockchain
- **Witness System**: Multiple parties can vouch for document authenticity
- **Certificate Generation**: Generate certificates for fully witnessed attestations
- **Privacy First**: Documents never leave your browser - only SHA-256 hashes are stored on-chain

## Quick Start

### 1. Start the Web App

```bash
cd notarial-app
chmod +x serve.sh
./serve.sh
```

Open http://localhost:8000 in your browser.

### 2. Configure RPC Endpoint

The app connects to Alice validator by default: `http://51.79.26.123:9944`

You can change this to your local node: `http://localhost:9944`

### 3. Attest a Document

1. Go to **Attest Document** tab
2. Drop a file or click to upload
3. Select category and validity period
4. Enter your SPHINCS+ secret key (128 bytes hex)
5. Click **Submit Attestation**

### 4. Verify a Document

1. Go to **Verify Document** tab
2. Upload the same file OR paste the document hash
3. Click **Verify Document**
4. See attestation details if found

### 5. Witness an Attestation

1. Go to **Witness** tab
2. Enter the attestation ID
3. Optionally add a note
4. Enter your SPHINCS+ key
5. Click **Submit Witness**

## RPC Methods

The notarial pallet exposes these RPC methods:

| Method | Description |
|--------|-------------|
| `notarial_attestDocument` | Attest a document hash on-chain |
| `notarial_witnessAttestation` | Witness an existing attestation |
| `notarial_verifyDocument` | Check if a document exists on-chain |
| `notarial_getAttestation` | Get attestation details by ID |
| `notarial_generateCertificate` | Generate certificate for certified attestation |
| `notarial_getCertificate` | Get certificate by ID |

## Document Categories

| Code | Category |
|------|----------|
| 0 | Academic Credential |
| 1 | Legal Document |
| 2 | Contract |
| 3 | Intellectual Property |
| 4 | Identity |
| 5 | Financial |
| 6 | Medical |
| 7 | Other |

## How It Works

```
┌─────────────────┐
│   Your Browser  │
│   ┌───────────┐ │     ┌──────────────────┐
│   │ Document  │─┼────>│ SHA-256 Hash     │
│   └───────────┘ │     │ (computed locally)│
│                 │     └────────┬─────────┘
│   ┌───────────┐ │              │
│   │SPHINCS+   │─┼──────────────┤
│   │ Key       │ │              │
│   └───────────┘ │              ▼
└─────────────────┘     ┌──────────────────┐
                        │  Sign Transaction │
                        │  with SPHINCS+    │
                        └────────┬─────────┘
                                 │
                                 ▼
                        ┌──────────────────┐
                        │  QuantumHarmony  │
                        │  Blockchain      │
                        │  (Notarial Pallet)│
                        └──────────────────┘
```

1. **Document stays local**: Only the SHA-256 hash is sent to the blockchain
2. **Post-quantum signatures**: All transactions are signed with SPHINCS+
3. **Immutable timestamp**: Block number proves when attestation was created
4. **Multi-witness certification**: When enough witnesses sign, attestation becomes certified

## Security

- **SPHINCS+**: Post-quantum secure signatures resistant to quantum computer attacks
- **SHA-256**: Cryptographic hash ensures document integrity
- **On-chain immutability**: Once attested, the record cannot be altered
- **Privacy**: Document content is never transmitted or stored

## Requirements

- Modern web browser with Web Crypto API support
- Access to a QuantumHarmony RPC endpoint
- SPHINCS+ keypair for signing transactions

## Support

- Telegram: https://t.me/paraxiom
- GitHub: https://github.com/QuantumVerseProtocols/quantumharmony
