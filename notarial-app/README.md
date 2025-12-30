# QuantumHarmony Notarial Service

Post-quantum secure document attestation and Ricardian contracts on the QuantumHarmony blockchain.

## Live Demo

- **Full App**: http://51.79.26.123:8081/app.html
- **Simple Version**: http://51.79.26.123:8081/index.html

## Features

### Document Attestation
- **Document Attestation**: Create immutable on-chain proof that a document existed at a specific time
- **Document Verification**: Check if a document has been attested on the blockchain
- **Witness System**: Multiple parties can vouch for document authenticity
- **Certificate Generation**: Generate certificates for fully witnessed attestations
- **Privacy First**: Documents never leave your browser - only SHA-256 hashes are stored on-chain

### Encrypted Keystore
- **Password Protection**: Keys encrypted with AES-256-GCM
- **Key Derivation**: PBKDF2 with 100,000 iterations (Argon2id for production)
- **Multiple Accounts**: Create and manage multiple keystores
- **Session Unlock**: Unlock once per session for seamless signing

### IPFS Integration
- **Pinata Support**: Pin documents to IPFS via Pinata API
- **Encrypted Upload**: Optional client-side AES-256-GCM encryption before upload
- **Multiple Gateways**: Automatic gateway fallback for retrieval
- **Decentralized Storage**: Documents persist across the decentralized network

### Ricardian Contracts
- **Multi-Party Contracts**: Create legally-binding contracts between multiple parties
- **On-Chain Signatures**: All signatures recorded immutably on blockchain
- **Contract Lifecycle**: Draft → Active → Executed status tracking
- **Amendment System**: Propose and approve contract amendments

## Quick Start

### 1. Start the Web App

```bash
cd notarial-app
chmod +x serve.sh
./serve.sh
```

Open http://localhost:8081/app.html in your browser.

### 2. Create an Account

1. Go to **Account** tab
2. Click **Create New Keystore**
3. Enter a name and strong password
4. Your SPHINCS+ keypair is generated and encrypted

### 3. Unlock Your Account

1. Select your keystore from the dropdown
2. Enter your password
3. Click **Unlock** - you'll see the green "Unlocked" indicator

### 4. Attest a Document

1. Go to **Attest** tab
2. Drop a file or click to upload
3. Select category and storage option:
   - **Local Only**: Hash stored on-chain, document stays on your device
   - **IPFS Public**: Document pinned to IPFS, retrievable by anyone
   - **IPFS Encrypted**: Document encrypted before IPFS upload
4. Click **Submit Attestation**

### 5. Verify a Document

1. Go to **Verify** tab
2. Upload the file OR paste the document hash
3. Click **Verify Document**
4. See attestation details if found

### 6. Create a Ricardian Contract

1. Go to **Contracts** tab
2. Click **Create New Contract**
3. **Step 1**: Enter title, select type, add description
4. **Step 2**: Add all parties (name + blockchain address)
5. **Step 3**: Review and submit to blockchain
6. Share the Contract ID with other parties for signing

### 7. Sign a Contract

1. Go to **Contracts** tab
2. Click **Sign Contract**
3. Enter the Contract ID you received
4. Click **Sign Contract** to add your signature on-chain

### 8. Configure IPFS (Optional)

1. Go to **Settings** tab
2. Enter your Pinata API Key and Secret
3. Click **Test Connection** to verify
4. Save settings

## Contract Types

| Type | Use Case |
|------|----------|
| Academic Program | University agreements, course enrollments |
| Partnership | Business partnerships, joint ventures |
| Service Agreement | Service contracts, consulting agreements |
| NDA | Non-disclosure agreements |
| Employment | Employment contracts, contractor agreements |
| License | Software licenses, IP licensing |
| Custom | Any other contract type |

## Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                        Browser                               │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────────────┐  │
│  │  Document   │  │  Keystore   │  │  Contract Manager   │  │
│  │  (local)    │  │  (encrypted)│  │  (local + on-chain) │  │
│  └──────┬──────┘  └──────┬──────┘  └──────────┬──────────┘  │
│         │                │                     │             │
│         ▼                ▼                     ▼             │
│  ┌─────────────────────────────────────────────────────┐    │
│  │              JavaScript Application                  │    │
│  │  - SHA-256 hashing      - SPHINCS+ signing          │    │
│  │  - AES-256-GCM encrypt  - SCALE encoding            │    │
│  └──────────────────────────┬──────────────────────────┘    │
└─────────────────────────────┼───────────────────────────────┘
                              │
              ┌───────────────┴───────────────┐
              │                               │
              ▼                               ▼
    ┌──────────────────┐           ┌──────────────────┐
    │  QuantumHarmony  │           │      Pinata      │
    │   Blockchain     │           │   IPFS Gateway   │
    │                  │           │                  │
    │  Pallet 20:      │           │  - Document      │
    │  Ricardian       │           │    storage       │
    │  Contracts       │           │  - CID indexing  │
    │                  │           │                  │
    │  Pallet 21:      │           └──────────────────┘
    │  Notarial        │
    └──────────────────┘
```

## Pallet Indices

| Pallet | Index | Purpose |
|--------|-------|---------|
| Ricardian Contracts | 20 | Multi-party contract management |
| Notarial | 21 | Document attestation & witnesses |

## RPC Methods

### Notarial Pallet (Index 21)

| Method | Description |
|--------|-------------|
| `notarial_attestDocument` | Attest a document hash on-chain |
| `notarial_witnessAttestation` | Witness an existing attestation |
| `notarial_verifyDocument` | Check if a document exists on-chain |
| `notarial_getAttestation` | Get attestation details by ID |
| `notarial_generateCertificate` | Generate certificate for certified attestation |
| `notarial_getCertificate` | Get certificate by ID |

### Ricardian Contracts Pallet (Index 20)

| Method | Description |
|--------|-------------|
| `ricardian_createContract` | Create a new multi-party contract |
| `ricardian_signContract` | Add a party's signature to contract |
| `ricardian_getContract` | Get contract details by ID |
| `ricardian_proposeAmendment` | Propose a contract amendment |
| `ricardian_approveAmendment` | Approve a pending amendment |

### Generic RPC

| Method | Description |
|--------|-------------|
| `quantumharmony_submitSignedExtrinsic` | Submit any signed transaction |

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

## File Structure

```
notarial-app/
├── app.html           # Full-featured application
├── index.html         # Simple attestation interface
├── serve.sh           # Web server startup script
├── README.md          # This documentation
└── js/
    ├── keystore.js    # Encrypted keystore management
    └── ipfs.js        # IPFS/Pinata integration
```

## Security Model

### Key Protection
- **Never Transmitted**: Private keys never leave the browser
- **Encrypted at Rest**: AES-256-GCM encryption with password-derived key
- **Memory Isolation**: Keys cleared from memory on lock
- **Session-Based**: Unlock valid only for current session

### Document Privacy
- **Hash Only On-Chain**: Document content never stored on blockchain
- **Optional IPFS**: User chooses whether to upload to IPFS
- **Client-Side Encryption**: IPFS uploads can be encrypted before transmission

### Post-Quantum Security
- **SPHINCS+**: All signatures use SPHINCS+ (128-byte secret keys)
- **Quantum Resistant**: Secure against future quantum computer attacks
- **SHA-256**: Cryptographic hash ensures document integrity

## Local Development

```bash
# Clone the repository
git clone https://github.com/QuantumVerseProtocols/quantumharmony.git
cd quantumharmony/notarial-app

# Start local web server
python3 -m http.server 8081

# Or use the provided script
./serve.sh
```

## Environment Requirements

- Modern web browser with Web Crypto API support
- Access to a QuantumHarmony RPC endpoint (default: http://51.79.26.123:9944)
- For IPFS: Pinata account with API credentials

## Troubleshooting

### "crypto.subtle is undefined"
This occurs when accessing via HTTP instead of HTTPS. The app includes fallback implementations for development, but HTTPS is recommended for production.

### "Pinata upload failed"
1. Check your API keys in Settings
2. Click "Test Connection" to verify
3. Ensure your Pinata account has available storage

### "Failed to submit transaction"
1. Verify your keystore is unlocked (green indicator)
2. Check that the RPC endpoint is accessible
3. Ensure the blockchain node is running

## Support

- Telegram: https://t.me/paraxiom
- GitHub: https://github.com/QuantumVerseProtocols/quantumharmony
