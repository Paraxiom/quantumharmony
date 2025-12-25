# Quantum Entropy Vault Configuration Guide

QuantumHarmony provides flexible quantum entropy management through three vault backends:

## Vault Backends

### 1. Hardware Security Module (HSM) - Crypto4A
**Best for**: Production deployments requiring maximum security

- **Hardware**: Crypto4A QxEPP HSM
- **Entropy Source**: True quantum random number generation
- **Quality Score**: 95-99 (highest)
- **Setup**: Requires Crypto4A hardware and network access

```bash
# Set HSM endpoint
export CRYPTO4A_ENDPOINT="http://192.168.0.41:8132"

# Run node (will use HSM vault)
./target/release/quantumharmony-node --dev
```

### 2. Software Security Module (SSM)
**Best for**: Development, testing, or deployments without HSM hardware

- **Hardware**: None required
- **Entropy Sources**:
  - Operating system entropy pool (OsRng)
  - CPU jitter and timing variations
  - SHA3-512 entropy conditioning
- **Quality Score**: 75-90
- **Setup**: Works out of the box

```bash
# No configuration needed, SSM is default
./target/release/quantumharmony-node --dev
```

### 3. Unified Vault (HSM + SSM Fallback)
**Best for**: Production with automatic fallback

- **Primary**: Crypto4A HSM
- **Fallback**: Software entropy vault
- **Behavior**: Uses HSM if available, falls back to SSM if HSM fails
- **Setup**: Configure HSM endpoint, enable fallback

```bash
export CRYPTO4A_ENDPOINT="http://192.168.0.41:8132"
# Node automatically uses HSM with SSM fallback
./target/release/quantumharmony-node --dev
```

## Configuration Options

### Environment Variables

| Variable | Description | Default |
|----------|-------------|---------|
| `CRYPTO4A_ENDPOINT` | Crypto4A HSM endpoint URL | None (uses SSM) |

### Programmatic Configuration

```rust
use crate::unified_vault::{UnifiedVault, UnifiedVaultConfig, VaultBackend};

// Software-only mode
let config = UnifiedVaultConfig::software_only();
let vault = UnifiedVault::new(config)?;

// HSM-only mode (no fallback)
let config = UnifiedVaultConfig::hsm_only("http://192.168.0.41:8132".to_string());
let vault = UnifiedVault::new(config)?;

// HSM with software fallback (recommended)
let config = UnifiedVaultConfig::hsm_with_fallback("http://192.168.0.41:8132".to_string());
let vault = UnifiedVault::new(config)?;
```

## Vault Features

### Common Features (All Backends)

1. **Entropy Provisioning**
   ```rust
   // Get entropy for Falcon1024 signatures
   let falcon_entropy = vault.get_falcon_entropy()?; // 40 bytes

   // Get entropy for SPHINCS+ signatures
   let sphincs_entropy = vault.get_sphincs_entropy()?; // 32 bytes

   // Get entropy for consensus operations
   let consensus_entropy = vault.get_consensus_entropy()?; // 32 bytes
   ```

2. **Statistics**
   ```rust
   let stats = vault.get_stats();
   match stats {
       UnifiedVaultStats::HSM { backend, stats } => {
           println!("HSM: {} segments, {} bytes consumed",
                    stats.segment_count, stats.total_consumed);
       }
       UnifiedVaultStats::SSM { backend, stats } => {
           println!("SSM: {} bytes in pool, {} collected",
                    stats.pool_size, stats.total_collected);
       }
   }
   ```

### HSM-Specific Features

1. **Entropy Quality Threshold**: Minimum 80 (enforced)
2. **Segment Management**: Up to 16 encrypted segments (32KB each)
3. **AES-256-GCM Encryption**: All entropy encrypted at rest
4. **Replay Protection**: Usage counters prevent reuse
5. **Emergency Sealing**: `vault.seal()` clears all entropy

### SSM-Specific Features

1. **Auto-Refill**: Automatically replenishes entropy pool
2. **Quality Assessment**: Statistical tests for entropy quality
3. **Multiple Sources**: Combines OS, CPU jitter, and timing entropy
4. **Configurable Thresholds**: Customize quality and pool size

## Security Considerations

### Production Recommendations

1. **Use HSM with Fallback**
   - Provides quantum-safe entropy when available
   - Maintains availability if HSM fails
   - Best of both worlds

2. **Network Security**
   - Crypto4A HSM should be on isolated network
   - Use firewall rules to restrict access
   - Consider VPN for remote HSM access

3. **Monitoring**
   - Monitor vault statistics regularly
   - Alert on quality score drops
   - Track entropy consumption rates

### Development & Testing

1. **Use SSM**
   - No hardware dependencies
   - Faster setup and testing
   - Sufficient quality for non-production use

2. **Test Both Modes**
   - Ensure code works with both HSM and SSM
   - Test fallback scenarios
   - Verify entropy quality requirements

## Entropy Quality Scores

| Source | Quality Range | Notes |
|--------|---------------|-------|
| Crypto4A QxEPP | 95-99 | True quantum entropy |
| OS Entropy Pool | 85-95 | Good quality, kernel-managed |
| CPU Jitter | 75-90 | Variable, timing-based |
| Network Timing | 60-80 | Lower quality, use with caution |

## Troubleshooting

### HSM Connection Fails

```
ERROR: Failed to connect to Crypto4A HSM at http://192.168.0.41:8132
```

**Solutions**:
1. Check HSM is powered on and network-accessible
2. Verify endpoint URL is correct
3. Check firewall rules allow port 8132
4. Enable fallback to SSM: `allow_fallback: true`

### Low Entropy Quality

```
WARN: Entropy quality below threshold: 65 < 75
```

**Solutions**:
1. Check system load (high load reduces jitter quality)
2. Increase CPU jitter collection iterations
3. Add more entropy sources
4. Consider upgrading to HSM

### Insufficient Entropy

```
ERROR: Insufficient entropy in vault
```

**Solutions**:
1. **HSM**: Add entropy via QRNG sources
2. **SSM**: Pool will auto-refill, wait or reduce consumption
3. Increase target pool size in configuration

## Performance Impact

### HSM Mode
- **Latency**: ~1-5ms per entropy request (network + decryption)
- **Throughput**: 10,000+ requests/second
- **CPU**: Minimal (AES-NI acceleration)

### SSM Mode
- **Latency**: ~50-200µs per entropy request (in-memory)
- **Throughput**: 50,000+ requests/second
- **CPU**: Moderate (jitter collection + hashing)

## Migration Guide

### From Mock Keys to Vault

**Before**:
```rust
let mock_key = vec![0xAA; 64];
```

**After**:
```rust
use crate::unified_vault::unified_vault;

let vault = unified_vault();
let entropy = vault.get_falcon_entropy()?;
let (public_key, private_key) = pqcrypto_falcon::falcon1024::keypair();
```

### From Separate Vaults to Unified

**Before**:
```rust
use crate::quantum_vault::quantum_vault;
let vault = quantum_vault();
```

**After**:
```rust
use crate::unified_vault::unified_vault;
let vault = unified_vault();
// Same API, auto-selects backend
```

## Examples

### Basic Usage
```rust
use crate::unified_vault::unified_vault;

fn generate_signing_key() -> Result<(), String> {
    let vault = unified_vault();
    let entropy = vault.get_falcon_entropy()?;

    // Use entropy for key generation
    let (pubkey, privkey) = pqcrypto_falcon::falcon1024::keypair();

    Ok(())
}
```

### Custom Configuration
```rust
use crate::unified_vault::{UnifiedVault, UnifiedVaultConfig, VaultBackend};
use crate::software_entropy_vault::SoftwareVaultConfig;

fn setup_custom_vault() -> Result<UnifiedVault, String> {
    let mut software_config = SoftwareVaultConfig::default();
    software_config.min_quality = 85;  // Higher quality
    software_config.target_pool_size = 16384;  // Larger pool

    let config = UnifiedVaultConfig {
        preferred_backend: VaultBackend::SSM,
        hsm_endpoint: None,
        software_config,
        allow_fallback: false,
    };

    UnifiedVault::new(config)
}
```

### Monitoring
```rust
use crate::unified_vault::unified_vault;
use log::info;

fn monitor_vault_health() {
    let vault = unified_vault();
    let stats = vault.get_stats();

    match stats {
        UnifiedVaultStats::HSM { backend, stats } => {
            info!("HSM Vault: {} segments, avg quality: {:.1}",
                  stats.segment_count, stats.average_quality);
        }
        UnifiedVaultStats::SSM { backend, stats } => {
            info!("SSM Vault: {} bytes available, {} collected total",
                  stats.pool_size, stats.total_collected);
        }
    }
}
```

## FAQ

**Q: Can I switch between HSM and SSM at runtime?**
A: No, the vault backend is selected at startup. Restart the node to change backends.

**Q: Is SSM secure enough for mainnet?**
A: SSM provides cryptographically secure entropy suitable for most use cases. For maximum security and true quantum entropy, use HSM.

**Q: What happens if HSM fails during operation?**
A: With fallback enabled, the system logs a warning and continues using SSM. Monitor logs for HSM failures.

**Q: How much entropy do I need?**
A: Each block consensus requires ~32 bytes. Each Falcon signature requires ~40 bytes. Plan for peak transaction load.

**Q: Can I use multiple HSMs?**
A: Not currently. For high availability, use HSM with SSM fallback.

## Support

For issues or questions:
- GitHub Issues: https://github.com/QuantumVerseProtocols/quantumharmony/issues
- Crypto4A HSM: https://www.crypto4a.com/
- QuantumHarmony Docs: https://docs.quantumharmony.io/
