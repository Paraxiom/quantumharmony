# Security Policy

## Project Status

QuantumHarmony is an **experimental research testnet** implementing post-quantum cryptographic primitives. It is **not production-ready** and has **not been audited**.

## Supported Versions

| Version | Status |
| ------- | ------ |
| 0.30.x  | Technical Preview - Active Development |

## Reporting a Vulnerability

If you discover a security vulnerability, please report it responsibly:

1. **Do NOT open a public GitHub issue** for security vulnerabilities
2. Email security concerns to: security@quantumverseprotocols.com
3. Include:
   - Description of the vulnerability
   - Steps to reproduce
   - Potential impact assessment
   - Any suggested fixes (optional)

## Response Timeline

- **Acknowledgment**: Within 48 hours
- **Initial Assessment**: Within 7 days
- **Resolution Timeline**: Varies by severity

## Scope

### In Scope
- SPHINCS+ signature implementation
- Consensus mechanism vulnerabilities
- Key management in `pallet-sphincs-keystore`
- Runtime security issues
- Cryptographic primitive misuse

### Out of Scope
- Known limitations documented in README
- Issues in upstream dependencies (report to respective projects)
- Denial of service on testnet (expected for research network)
- Social engineering attacks

## Known Limitations

This is a research testnet. Known security considerations:

1. **No Security Audit**: Code has not been professionally audited
2. **Experimental Cryptography**: Post-quantum primitives are implemented for research
3. **Test Keys in Repository**: Development keys exist in `tools/` - these are NOT production keys
4. **No Economic Security**: Testnet tokens have no value; do not use for real assets

## Cryptographic Components

| Component | Implementation | Status |
|-----------|---------------|--------|
| SPHINCS+ | pqcrypto-sphincsplus | Research Implementation |
| Keccak-256 | sha3 crate | Standard Implementation |
| Falcon-1024 | pqcrypto-falcon | P2P Layer Only |

## Development Keys Warning

The repository contains development/test keys in:
- `tools/runtime-upgrade/src/main.rs` - Test account keys for local development
- Various test files

**These keys are for development only and must never be used in any production context.**

## Acknowledgments

We appreciate responsible disclosure and will acknowledge security researchers who report valid vulnerabilities (with permission).
