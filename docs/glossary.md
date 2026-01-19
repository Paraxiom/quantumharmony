# QuantumHarmony Glossary

ISO 22739:2024 Aligned Terminology

---

## Core Concepts

### Block
**ISO Definition:** A data structure containing an ordered set of transactions and metadata linking to the previous block.

**QH Implementation:** Substrate block containing extrinsics, state root, and BABE/GRANDPA metadata.

---

### Blockchain
**ISO Definition:** A distributed ledger with confirmed blocks organized in an append-only, sequential chain using cryptographic links.

**QH Implementation:** Post-quantum secure blockchain using Falcon-1024 signatures and GRANDPA finality.

---

### Consensus Mechanism
**ISO Definition:** Rules and procedures by which agreement is reached among DLT nodes.

**QH Implementation:** Hybrid BABE (block production) + GRANDPA (finality) with Falcon-1024 validator signatures.

---

### Crypto-asset
**ISO Definition:** A digital asset that uses cryptographic techniques for access, validation, and transfer.

**QH Implementation:** Native token (QH) used for transaction fees and validator staking.

---

### Digital Token
**ISO Definition:** A digital asset representing a unit of value or rights within a DLT system.

**QH Implementation:** Pallet-managed tokens including stablecoins and carbon credits (future).

---

### Distributed Application (DApp)
**ISO Definition:** An application that runs on a distributed computing infrastructure.

**QH Implementation:** Off-chain applications interacting with on-chain pallets via RPC.

---

### Distributed Ledger
**ISO Definition:** A ledger shared across a set of DLT nodes and synchronized between them using a consensus mechanism.

**QH Implementation:** Substrate-based state trie replicated across all validating nodes.

---

### DLT Node
**ISO Definition:** A device or process that participates in a distributed ledger technology network.

**QH Implementation:** `quantumharmony-node` binary running as validator or full node.

---

### DLT Platform
**ISO Definition:** An integrated infrastructure enabling the creation and operation of DLT systems.

**QH Implementation:** Complete Substrate-based platform with pallets, RPC, and dashboard.

---

### Finality
**ISO Definition:** The property that a confirmed transaction cannot be reversed.

**QH Implementation:** GRANDPA finality - once 2/3+ validators vote, block is permanently finalized.

---

### Genesis Block
**ISO Definition:** The first block in a blockchain, with no predecessor.

**QH Implementation:** Configured via chain spec, contains initial validator set and balances.

---

### Hash
**ISO Definition:** A fixed-size output produced by a hash function from variable-size input.

**QH Implementation:** BLAKE2b-256 for block hashes, state roots, and transaction IDs.

---

### Immutability
**ISO Definition:** The property that recorded data cannot be changed after confirmation.

**QH Implementation:** Achieved through cryptographic linking of blocks and GRANDPA finality.

---

### Node (see DLT Node)

---

### Oracle
**ISO Definition:** A mechanism that provides external data to a DLT system.

**QH Implementation:** `pallet-oracle` with approved reporters, staking, and signal submission.

---

### Peer
**ISO Definition:** A DLT node that can communicate directly with other nodes in the network.

**QH Implementation:** Any node connected via libp2p P2P networking (port 30333).

---

### Private Key
**ISO Definition:** A cryptographic key known only to its owner, used for signing transactions.

**QH Implementation:** Falcon-1024 secret key (2305 bytes) or SPHINCS+ secret key (128 bytes).

---

### Public Key
**ISO Definition:** A cryptographic key that can be shared publicly, derived from a private key.

**QH Implementation:** Falcon-1024 public key (1793 bytes), encoded as SS58 address for users.

---

### Smart Contract
**ISO Definition:** A computer program stored in a DLT system where the outcome of execution is recorded on the distributed ledger.

**QH Implementation:** Substrate pallets providing deterministic on-chain logic.

---

### Transaction
**ISO Definition:** A digitally signed message submitted to a DLT system for processing.

**QH Implementation:** Extrinsic signed with Falcon-1024, containing call data and metadata.

---

### Validating Node
**ISO Definition:** A DLT node that participates in the consensus mechanism to validate and confirm transactions.

**QH Implementation:** Validator node with Falcon-1024 session keys, approved through governance.

---

### Wallet
**ISO Definition:** Software or hardware that stores private keys and enables interaction with a DLT system.

**QH Implementation:** Dashboard-integrated signing or external Falcon-1024/SPHINCS+ wallet.

---

## QuantumHarmony-Specific Terms

### Crypto4A Simulator
Hardware security module (HSM) simulator providing quantum random number generation (QRNG) entropy via HTTP API.

---

### Entropy Gossip
P2P protocol for distributing QRNG signals across the network, ensuring all nodes have access to quantum randomness.

---

### Falcon-1024
Post-quantum digital signature algorithm selected by NIST, providing NIST PQC Level V security (256-bit classical equivalent).

---

### GRANDPA
GHOST-based Recursive ANcestor Deriving Prefix Agreement - Substrate's finality gadget providing deterministic finality.

---

### K-of-M Threshold
Cryptographic scheme requiring K out of M sources to contribute for a valid result, used in QRNG combination.

---

### Notarial Service
On-chain attestation service for documenting timestamps and hashes of external documents.

---

### Priority Queue
Ordered queue for signal processing, ensuring time-sensitive oracle data is handled appropriately.

---

### QBER
Quantum Bit Error Rate - metric indicating the quality of quantum random numbers, should be < 1%.

---

### QRNG
Quantum Random Number Generator - hardware device producing true random numbers from quantum phenomena.

---

### Reporter
Entity approved by validators to submit oracle data, required to stake tokens as collateral.

---

### Runtime Segmentation
Technique for partitioning blockchain state across multiple segments for scalability.

---

### Session Keys
Ephemeral keys used by validators for block production (BABE) and finality voting (GRANDPA).

---

### Signal
Data packet containing oracle information, QRNG entropy, or other external data, signed by a reporter.

---

### SPHINCS+
Stateless Hash-Based Signature scheme, post-quantum secure, used for account/transaction signatures.

---

### SS58
Address format used in Substrate-based chains, encoding public keys with network prefix and checksum.

---

### Threshold QRNG
System combining entropy from multiple QRNG sources using K-of-M threshold for fault tolerance.

---

### Tonnetz
Musical topology used in SMDR for attention bias, reducing LLM hallucinations through geometric constraints.

---

## Abbreviations

| Abbreviation | Expansion |
|--------------|-----------|
| BABE | Blind Assignment for Blockchain Extension |
| DLT | Distributed Ledger Technology |
| GRANDPA | GHOST-based Recursive ANcestor Deriving Prefix Agreement |
| HSM | Hardware Security Module |
| NIST | National Institute of Standards and Technology |
| P2P | Peer-to-Peer |
| PQC | Post-Quantum Cryptography |
| QBER | Quantum Bit Error Rate |
| QH | QuantumHarmony |
| QRNG | Quantum Random Number Generator |
| RPC | Remote Procedure Call |
| SDG | Sustainable Development Goal |
| SMDR | Sparse Meta Distributed Representations |

---

## References

- [ISO 22739:2024](https://www.iso.org/standard/73771.html) - Blockchain and DLT Vocabulary
- [NIST PQC](https://csrc.nist.gov/projects/post-quantum-cryptography) - Post-Quantum Cryptography Standards
- [Substrate Documentation](https://docs.substrate.io/)
