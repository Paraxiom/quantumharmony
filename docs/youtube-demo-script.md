# QuantumHarmony YouTube Demo Script

## Video Title Suggestion
"QuantumHarmony: Live Post-Quantum Blockchain Demo - SPHINCS+ Signatures in Action"

---

## Pre-Recording Checklist
- [ ] Terminal with large font (Cmd+Plus to enlarge)
- [ ] Dark terminal theme for better visibility
- [ ] Close notifications
- [ ] Have this script on a second monitor

---

## PART 1: Introduction (30 seconds)

**Say:** "This is QuantumHarmony - a post-quantum blockchain using real SPHINCS+ signatures, not just marketing claims. Let me show you a live network with three validators producing blocks right now."

---

## PART 2: Show Live Network (1 minute)

### Command 1: Check Network Health
```bash
curl -s -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' \
  http://51.79.26.123:9944 | jq .
```

**Expected output:**
```json
{
  "peers": 3,
  "isSyncing": false,
  "shouldHavePeers": true
}
```

**Say:** "Three validators connected, network is synchronized."

### Command 2: Show Chain Properties
```bash
curl -s -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"system_properties","params":[],"id":1}' \
  http://51.79.26.123:9944 | jq .
```

**Expected output:**
```json
{
  "ss58Format": 42,
  "tokenDecimals": 18,
  "tokenSymbol": "QMHY"
}
```

**Say:** "Native token is QMHY with 18 decimals, standard Substrate SS58 format."

### Command 3: Show Block Production
```bash
# Run twice with 6-second gap to show blocks incrementing
echo "Block 1:" && curl -s -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"chain_getHeader","params":[],"id":1}' \
  http://51.79.26.123:9944 | jq '.result.number'

sleep 6

echo "Block 2 (6 seconds later):" && curl -s -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"chain_getHeader","params":[],"id":1}' \
  http://51.79.26.123:9944 | jq '.result.number'
```

**Say:** "Blocks are being produced every 6 seconds. This is a live, functioning blockchain."

---

## PART 3: Show Custom RPC Methods (1 minute)

### Command 4: List QuantumHarmony-Specific Methods
```bash
curl -s -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"rpc_methods","params":[],"id":1}' \
  http://51.79.26.123:9944 | jq '.result.methods | map(select(startswith("gateway") or startswith("notarial")))'
```

**Say:** "These are custom RPC methods we've built. Gateway methods for wallet integration. Notarial methods for document attestation - a decentralized notary system."

### Command 5: Test Transaction Gateway
```bash
# Get genesis hash (proves chain identity)
echo "Genesis Hash:" && curl -s -H "Content-Type: application/json" \
  -d '{"jsonrpc":"2.0","method":"gateway_genesisHash","params":[],"id":1}' \
  http://51.79.26.123:9944 | jq -r '.result'
```

**Say:** "The transaction gateway provides wallet-friendly APIs. This genesis hash uniquely identifies our chain."

---

## PART 4: Notarial System Demo (1 minute)

### Command 6: Verify a Document Hash
```bash
# Create a hash of any document
DOCUMENT_HASH="0x$(echo -n 'QuantumHarmony Demo Document' | sha256sum | cut -d' ' -f1)"
echo "Document hash: $DOCUMENT_HASH"

# Verify if it's attested (it won't be yet)
curl -s -H "Content-Type: application/json" \
  -d "{\"jsonrpc\":\"2.0\",\"method\":\"notarial_verifyDocument\",\"params\":[\"$DOCUMENT_HASH\"],\"id\":1}" \
  http://51.79.26.123:9944 | jq .
```

**Say:** "The notarial system can verify any document hash. This one isn't attested yet - exists is false. Once attested on-chain, this becomes immutable, timestamped proof."

---

## PART 5: SPHINCS+ Explanation (1 minute)

**Say:** "Now here's what makes this different from chains claiming quantum security. QuantumHarmony uses SPHINCS+ - a hash-based signature scheme that's resistant to quantum computer attacks."

### Show the signature scheme in code (optional - screen share file):
```bash
# If you want to show the code
cat runtime/src/lib.rs | grep -A5 "sphincs"
```

**Say:** "SPHINCS+ signatures are larger than ECDSA - about 8KB versus 64 bytes - but they're mathematically proven secure against both classical and quantum attacks. This isn't a marketing claim. It's running right now."

---

## PART 6: Three Validators (30 seconds)

### Command 7: Show All Three Validators
```bash
echo "=== Alice (Canada) ===" && curl -s http://51.79.26.123:9944 -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"system_name","params":[],"id":1}' | jq -r '.result'
echo "=== Bob (Canada) ===" && curl -s http://51.79.26.168:9944 -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"system_name","params":[],"id":1}' | jq -r '.result'
echo "=== Charlie (France) ===" && curl -s http://209.38.225.4:9944 -H "Content-Type: application/json" -d '{"jsonrpc":"2.0","method":"system_name","params":[],"id":1}' | jq -r '.result'
```

**Say:** "Three independent validators - two in Canada, one in France - all running the same QuantumHarmony runtime with post-quantum cryptography."

---

## PART 7: Reality Check - QuantumHarmony vs Marketing Claims (1-2 minutes)

**Say:** "Let me show you the difference between real post-quantum technology and marketing."

### On-Screen Comparison Table (create graphic or show text):

```
┌─────────────────────────────────────────────────────────────────────────────┐
│           QUANTUMHARMONY              │     KROWN / QUANTUM eMOTION         │
├───────────────────────────────────────┼─────────────────────────────────────┤
│ ✅ SPHINCS+ signatures (NIST PQC)     │ ❌ No PQC in public audit           │
│ ✅ Live blockchain (verifiable now)   │ ❌ Web app only (NestJS/Next.js)    │
│ ✅ Open source, auditable code        │ ❌ "NDA'd hardware" claims          │
│ ✅ 3 validators producing blocks      │ ❌ No blockchain evidence           │
│ ✅ On-chain notarial system           │ ❌ Centralized server signing       │
│ ✅ Decentralized key management       │ ❌ Private keys in env vars (!)     │
│ ✅ 115 passing cryptographic tests    │ ❌ Web vulnerability scan only      │
└───────────────────────────────────────┴─────────────────────────────────────┘
```

**Say:** "On the left, QuantumHarmony - what you just saw running live. On the right, a company claiming quantum security."

### Key Points to Mention:

**Point 1 - Their "Security Audit":**
> "Their public security audit - from CFG Ninja, December 2024 - covers a NestJS backend and Next.js frontend. That's a TypeScript web application. The audit checks for SQL injection, XSS, CORS issues. Standard OWASP Top 10 web vulnerabilities. Not a single mention of post-quantum cryptography, blockchain consensus, or smart contracts."

**Point 2 - Private Keys in Environment Variables:**
> "The audit found they were storing private keys in environment variables. For anyone technical watching - this is a fundamental security failure. Environment variables are visible in process listings, logged during crashes, exposed in container systems. This is how keys get leaked. And this is from a company claiming to be leaders in quantum security."

**Point 3 - Server-Side Signing:**
> "The audit also revealed server-side transaction signing. That means their backend holds user private keys. It's a custodial architecture - the opposite of blockchain's trustless model. If their server is compromised, everyone's keys are compromised."

**Point 4 - The Contrast:**
> "Meanwhile, QuantumHarmony uses SPHINCS+ - a NIST-standardized post-quantum signature scheme. Every transaction you saw is signed with cryptography that will remain secure even when quantum computers exist. And you can verify this yourself - the code is open, the validators are public, the RPC endpoints respond."

### Optional - Show the Audit Finding (if you have it):

**Say:** "Here's the actual finding from their audit - CFG01, Critical severity: 'Private keys stored in environment variables.' This isn't FUD. This is their own auditor's finding."

---

## PART 8: Closing (30 seconds)

**Say:** "So what have we seen today?

A live post-quantum blockchain with SPHINCS+ signatures. Three validators across two continents producing blocks every 6 seconds. Custom RPC methods for wallet integration and notarial services. 115 passing cryptographic tests. All verifiable, all open source.

Compare that to marketing claims backed by a web app security scan and private keys in environment variables.

The difference between real technology and vaporware is simple: one you can verify, one you have to trust.

Don't trust - verify. The endpoints are public. Run the commands yourself.

Subscribe for more deep dives into QuantumHarmony. Next up: Ricardian contracts for legally-binding on-chain agreements, and our decentralized stablecoin system."

---

## Quick Reference - Copy/Paste Commands

```bash
# Health check
curl -s -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' -H "Content-Type: application/json" http://51.79.26.123:9944 | jq .

# Current block
curl -s -d '{"jsonrpc":"2.0","method":"chain_getHeader","params":[],"id":1}' -H "Content-Type: application/json" http://51.79.26.123:9944 | jq '.result.number'

# Chain properties
curl -s -d '{"jsonrpc":"2.0","method":"system_properties","params":[],"id":1}' -H "Content-Type: application/json" http://51.79.26.123:9944 | jq .

# Genesis hash
curl -s -d '{"jsonrpc":"2.0","method":"gateway_genesisHash","params":[],"id":1}' -H "Content-Type: application/json" http://51.79.26.123:9944 | jq -r '.result'

# Custom RPC methods
curl -s -d '{"jsonrpc":"2.0","method":"rpc_methods","params":[],"id":1}' -H "Content-Type: application/json" http://51.79.26.123:9944 | jq '.result.methods | map(select(startswith("gateway") or startswith("notarial")))'

# Verify document
curl -s -d '{"jsonrpc":"2.0","method":"notarial_verifyDocument","params":["0x1234..."],"id":1}' -H "Content-Type: application/json" http://51.79.26.123:9944 | jq .
```

---

## Validator IPs (for reference)
- **Alice**: 51.79.26.123:9944 (OVH Canada)
- **Bob**: 51.79.26.168:9944 (OVH Canada)
- **Charlie**: 209.38.225.4:9944 (OVH France)

---

## Video Length Target: ~7 minutes

---

## Key Hashtags / Tags
```
#PostQuantum #Blockchain #SPHINCS #QuantumComputing #Cryptography
#QuantumSecurity #Web3 #Substrate #Rust #NIST #PQC
```

## Suggested Description
```
Live demonstration of QuantumHarmony - a post-quantum blockchain using NIST-standardized SPHINCS+ signatures.

In this video:
- Live network with 3 validators (Canada + France)
- Real-time block production (6-second blocks)
- Custom RPC methods for wallets and notarial services
- Comparison with marketing-only "quantum security" claims

Validator endpoints (try them yourself):
- Alice: http://51.79.26.123:9944
- Bob: http://51.79.26.168:9944
- Charlie: http://209.38.225.4:9944

Example command:
curl -s -d '{"jsonrpc":"2.0","method":"system_health","params":[],"id":1}' \
  -H "Content-Type: application/json" http://51.79.26.123:9944

Don't trust - verify.
```
