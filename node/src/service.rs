//! Service and ServiceFactory implementation. Specialized wrapper over substrate service.

use std::{net::SocketAddr, sync::Arc, time::Duration};

// Substrate
use sc_client_api::Backend;
use sc_executor::NativeExecutionDispatch;
use sc_service::{error::Error as ServiceError, Configuration, PartialComponents, TaskManager};
use sc_telemetry::{Telemetry, TelemetryHandle, TelemetryWorker};
use sc_transaction_pool_api::OffchainTransactionPoolFactory;
use sp_api::ConstructRuntimeApi;
// QUANTUM: Using SPHINCS+ instead of sr25519
use sp_consensus_aura::sphincs::AuthorityPair as AuraPair;
// Runtime
use quantumharmony_runtime::opaque::Block;
// Parallel processing
use crate::segmented_pool::SegmentedTransactionPool;
use crate::parallel_proposer::{ParallelProposerConfig, ParallelBlockStats};

use crate::client::{FullBackend, FullClient, RuntimeApiCollection};
pub use crate::client::{Client, TemplateRuntimeExecutor};

type BasicImportQueue = sc_consensus::DefaultImportQueue<Block>;
type FullPool = sc_transaction_pool::TransactionPoolWrapper<Block, FullClient<quantumharmony_runtime::RuntimeApi, TemplateRuntimeExecutor>>;
type FullSelectChain = sc_consensus::LongestChain<FullBackend, Block>;

/// PQTG configuration for quantum device entropy collection
#[derive(Clone, Debug)]
pub struct PqtgConfiguration {
    /// PQTG endpoint URL
    pub endpoint: String,
    /// QKD mode (disabled, optional, required)
    pub qkd_mode: String,
    /// Specific devices to use (comma-separated), or None for auto-discovery
    pub devices: Option<String>,
    /// Threshold K for Shamir secret sharing
    pub threshold_k: usize,
}

/// Creates a new partial node with Aura consensus (no GRANDPA, no Frontier)
pub fn new_partial<RuntimeApi, Executor>(
    config: &Configuration,
) -> Result<
    PartialComponents<
        FullClient<RuntimeApi, Executor>,
        FullBackend,
        FullSelectChain,
        BasicImportQueue,
        sc_transaction_pool::TransactionPoolWrapper<Block, FullClient<RuntimeApi, Executor>>,
        Option<Telemetry>,
    >,
    ServiceError,
>
where
    RuntimeApi: ConstructRuntimeApi<Block, FullClient<RuntimeApi, Executor>>,
    RuntimeApi: Send + Sync + 'static,
    RuntimeApi::RuntimeApi: RuntimeApiCollection,
    Executor: NativeExecutionDispatch + 'static,
{
    let telemetry = config
        .telemetry_endpoints
        .clone()
        .filter(|x| !x.is_empty())
        .map(|endpoints| -> Result<_, sc_telemetry::Error> {
            let worker = TelemetryWorker::new(16)?;
            let telemetry = worker.handle().new_telemetry(endpoints);
            Ok((worker, telemetry))
        })
        .transpose()?;

    let executor = sc_service::new_native_or_wasm_executor(config);

    let (client, backend, keystore_container, task_manager) =
        sc_service::new_full_parts::<Block, RuntimeApi, _>(
            config,
            telemetry.as_ref().map(|(_, telemetry)| telemetry.handle()),
            executor,
        )?;
    let client = Arc::new(client);

    let telemetry = telemetry.map(|(worker, telemetry)| {
        task_manager
            .spawn_handle()
            .spawn("telemetry", None, worker.run());
        telemetry
    });

    let select_chain = sc_consensus::LongestChain::new(backend.clone());

    // Build Aura import queue (no GRANDPA, no Frontier)
    // Note: We use the same Aura import queue for both validators and non-validators.
    // The "SelectNextSome polled after terminated" crash was caused by CLI --bootnodes
    // arguments, not by the Aura import queue itself. With bootnodes in the chain spec
    // instead of CLI, both validators and sync nodes work correctly.
    eprintln!("🔧 [IMPORT] Using Aura verification import queue (role: {:?})", config.role);

    let slot_duration = sc_consensus_aura::slot_duration(&*client)?;

    let create_inherent_data_providers = move |_, ()| async move {
        let timestamp = sp_timestamp::InherentDataProvider::from_system_time();
        let slot =
            sp_consensus_aura::inherents::InherentDataProvider::from_timestamp_and_slot_duration(
                *timestamp,
                slot_duration,
            );
        Ok((slot, timestamp))
    };

    let import_queue = sc_consensus_aura::import_queue::<AuraPair, _, _, _, _, _>(
        sc_consensus_aura::ImportQueueParams {
            block_import: client.clone(),
            justification_import: None,
            client: client.clone(),
            create_inherent_data_providers,
            spawner: &task_manager.spawn_essential_handle(),
            registry: config.prometheus_registry(),
            check_for_equivocation: Default::default(),
            telemetry: telemetry.as_ref().map(|x| x.handle()),
            compatibility_mode: sc_consensus_aura::CompatibilityMode::None,
        },
    )
    .map_err::<ServiceError, _>(Into::into)?;

    let transaction_pool = Arc::new(sc_transaction_pool::Builder::new(
        task_manager.spawn_essential_handle(),
        client.clone(),
        config.role.is_authority().into(),
    )
    .with_options(config.transaction_pool.clone())
    .build());

    Ok(PartialComponents {
        client,
        backend,
        keystore_container,
        task_manager,
        select_chain,
        import_queue,
        transaction_pool,
        other: telemetry,
    })
}

/// Load or generate a PQC (Falcon-1024) identity for transport-layer authentication.
///
/// The identity is persisted to `<base-path>/<chain-id>/network/pqc_transport_identity.json`
/// as a JSON file with hex-encoded Falcon-1024 keypair bytes. On first run, a new keypair
/// is generated and saved. On subsequent runs, the existing keypair is loaded.
///
/// This identity is used by `TransportConfig::PostQuantum` to replace Noise (Ed25519)
/// with Kyber-1024 key encapsulation + Falcon-1024 authentication.
#[cfg(feature = "pqc-transport")]
fn load_or_generate_pqc_identity(
    config: &Configuration,
) -> Result<sc_network::pqc_authenticator::PqcIdentity, ServiceError> {
    use pqcrypto_falcon::falcon1024;
    use pqcrypto_traits::sign::{PublicKey as SignPublicKey, SecretKey as SignSecretKey};

    let key_path = config.base_path.config_dir(config.chain_spec.id())
        .join("network")
        .join("pqc_transport_identity.json");

    if key_path.exists() {
        // Load existing Falcon-1024 keypair
        let contents = std::fs::read_to_string(&key_path)
            .map_err(|e| ServiceError::Other(format!(
                "Failed to read PQC transport identity from {}: {}", key_path.display(), e
            )))?;

        let json: serde_json::Value = serde_json::from_str(&contents)
            .map_err(|e| ServiceError::Other(format!(
                "Failed to parse PQC transport identity: {}", e
            )))?;

        let pk_hex = json["falcon_public_key"].as_str()
            .ok_or_else(|| ServiceError::Other(
                "Missing falcon_public_key in PQC transport identity file".into()
            ))?;
        let sk_hex = json["falcon_secret_key"].as_str()
            .ok_or_else(|| ServiceError::Other(
                "Missing falcon_secret_key in PQC transport identity file".into()
            ))?;

        let pk_bytes = hex::decode(pk_hex.trim_start_matches("0x"))
            .map_err(|e| ServiceError::Other(format!("Invalid PQC public key hex: {}", e)))?;
        let sk_bytes = hex::decode(sk_hex.trim_start_matches("0x"))
            .map_err(|e| ServiceError::Other(format!("Invalid PQC secret key hex: {}", e)))?;

        let pk = falcon1024::PublicKey::from_bytes(&pk_bytes)
            .map_err(|_| ServiceError::Other("Invalid Falcon-1024 public key bytes".into()))?;
        let sk = falcon1024::SecretKey::from_bytes(&sk_bytes)
            .map_err(|_| ServiceError::Other("Invalid Falcon-1024 secret key bytes".into()))?;

        let identity = sc_network::pqc_authenticator::PqcIdentity::from_keypair(pk, sk);
        eprintln!("🔐 [PQC-TRANSPORT] Loaded existing identity from {}", key_path.display());
        eprintln!("🔑 [PQC-TRANSPORT] PeerId: {}", identity.peer_id());
        Ok(identity)
    } else {
        // Generate new Falcon-1024 keypair
        let (pk, sk) = falcon1024::keypair();

        // Save to disk before wrapping in PqcIdentity (secret_key field is private)
        if let Some(parent) = key_path.parent() {
            std::fs::create_dir_all(parent)
                .map_err(|e| ServiceError::Other(format!(
                    "Failed to create PQC key directory {}: {}", parent.display(), e
                )))?;
        }

        let key_json = serde_json::json!({
            "falcon_public_key": format!("0x{}", hex::encode(pk.as_bytes())),
            "falcon_secret_key": format!("0x{}", hex::encode(sk.as_bytes())),
        });

        std::fs::write(&key_path, serde_json::to_string_pretty(&key_json).unwrap())
            .map_err(|e| ServiceError::Other(format!(
                "Failed to save PQC transport identity to {}: {}", key_path.display(), e
            )))?;

        // Set restrictive permissions on the key file (owner read/write only)
        #[cfg(unix)]
        {
            use std::os::unix::fs::PermissionsExt;
            let _ = std::fs::set_permissions(&key_path, std::fs::Permissions::from_mode(0o600));
        }

        let identity = sc_network::pqc_authenticator::PqcIdentity::from_keypair(pk, sk);
        eprintln!("🔐 [PQC-TRANSPORT] Generated new Falcon-1024 identity");
        eprintln!("🔑 [PQC-TRANSPORT] PeerId: {}", identity.peer_id());
        eprintln!("💾 [PQC-TRANSPORT] Saved to {}", key_path.display());
        Ok(identity)
    }
}

/// Builds a new service for a full node with Aura consensus (no GRANDPA, no Frontier)
async fn new_full(
    config: Configuration,
    pqtg_config: Option<PqtgConfiguration>,
) -> Result<TaskManager, ServiceError>
{
    let PartialComponents {
        client,
        backend,
        mut task_manager,
        import_queue,
        keystore_container,
        select_chain,
        transaction_pool,
        other: mut telemetry,
    } = new_partial::<quantumharmony_runtime::RuntimeApi, TemplateRuntimeExecutor>(&config)?;

    // QUANTUM: SPHINCS+ keystore initialization for ALL chain types
    //
    // ARCHITECTURE:
    // - Production (ChainType::Live): Keys MUST be pre-installed in keystore directory
    //   Format: filename = "61757261<64-byte-public-hex>", contents = "0x<128-byte-secret-hex>"
    //   The 128-byte secret key is directly restored via from_secret() - NO cache needed!
    //
    // - Development (ChainType::Development | Local): Auto-insert test keys if none found
    //   Uses cache-based approach for reproducibility with hardcoded test_accounts.rs keys
    //
    use sc_chain_spec::ChainType;
    use sp_keystore::Keystore;
    use sp_application_crypto::key_types;

    let keystore = keystore_container.keystore();
    let aura_keytype = key_types::AURA;
    let chain_type = config.chain_spec.chain_type();

    // Check if keystore already has AURA keys loaded from disk
    let existing_keys = keystore.sphincs_public_keys(aura_keytype);

    eprintln!("🔑 [SERVICE] Chain type: {:?}", chain_type);
    eprintln!("🔑 [SERVICE] Keystore SPHINCS+ keys found: {}", existing_keys.len());

    // PRODUCTION KEY LOADING: Check for VALIDATOR_KEY_FILE environment variable
    // This allows validators to use secure, unique keys instead of hardcoded test keys
    if let Ok(key_file_path) = std::env::var("VALIDATOR_KEY_FILE") {
        eprintln!("🔐 [SERVICE] VALIDATOR_KEY_FILE detected: {}", key_file_path);
        eprintln!("🔐 [SERVICE] Loading SPHINCS+ key from file (production mode)...");

        match load_validator_key_from_file(&key_file_path) {
            Ok((secret_hex, public_hex)) => {
                // Decode hex strings
                let secret_bytes = hex::decode(secret_hex.trim_start_matches("0x"))
                    .expect("Invalid hex in secret_key");
                let public_bytes = hex::decode(public_hex.trim_start_matches("0x"))
                    .expect("Invalid hex in public_key");

                // =======================================================================
                // CRITICAL FIX: Pre-populate SPHINCS+ cache for production keys
                // =======================================================================
                // The SPHINCS+ implementation uses a cache to ensure consistent keypairs.
                // Without this, has_keys() returns false even when keys exist in keystore.
                // Extract seed (first 48 bytes) from 128-byte secret for cache population.
                {
                    use sp_core::sphincs::Pair as SphincsPair;

                    let seed: [u8; 48] = secret_bytes[..48].try_into()
                        .expect("Secret key must have at least 48 bytes for seed");
                    let public_arr: [u8; 64] = public_bytes[..64].try_into()
                        .expect("Public key must be 64 bytes");
                    let secret_arr: [u8; 128] = secret_bytes[..128].try_into()
                        .expect("Secret key must be 128 bytes");

                    SphincsPair::insert_hardcoded_keypair(&seed, &public_arr, &secret_arr);
                    eprintln!("✅ [SERVICE] Pre-populated SPHINCS+ cache with production key");
                }

                // Insert into keystore using 128-byte secret as SURI
                let suri = format!("0x{}", hex::encode(&secret_bytes));

                match keystore.insert(aura_keytype, &suri, &public_bytes) {
                    Ok(()) => {
                        eprintln!("✅ [SERVICE] Loaded validator key from file successfully");
                        eprintln!("🔑 [SERVICE] Public key: 0x{}...{}",
                            hex::encode(&public_bytes[..8]),
                            hex::encode(&public_bytes[56..64]));
                    },
                    Err(e) => {
                        eprintln!("❌ [SERVICE] Failed to insert key from file: {:?}", e);
                        return Err(ServiceError::Other(format!("Failed to load validator key: {:?}", e)));
                    }
                }
            },
            Err(e) => {
                eprintln!("❌ [SERVICE] Failed to read key file: {}", e);
                return Err(ServiceError::Other(format!("Failed to read validator key file: {}", e)));
            }
        }
    } else if matches!(chain_type, ChainType::Development | ChainType::Local) {
        // =======================================================================
        // DEVELOPMENT/LOCAL MODE - REQUIRES VALIDATOR_KEY_FILE
        // =======================================================================
        //
        // For security, secret keys are no longer stored in source code.
        // Development mode now requires explicit key configuration.
        //
        // To run a dev validator:
        // 1. Generate a keypair: ./target/release/quantumharmony-node key generate --scheme sphincs
        // 2. Set VALIDATOR_KEY_FILE=/path/to/key.json
        // 3. Start the node
        //
        // Or use an existing keystore with keys pre-installed.
        //
        eprintln!("🔐 [SERVICE] Development/Local chain detected");

        if existing_keys.is_empty() {
            eprintln!("⚠️  [SERVICE] No SPHINCS+ keys found in keystore.");
            eprintln!("⚠️  [SERVICE] For development mode, you must provide keys via:");
            eprintln!("    1. VALIDATOR_KEY_FILE environment variable, or");
            eprintln!("    2. Pre-install keys in the keystore directory");
            eprintln!("");
            eprintln!("    See: docs/VALIDATOR_SETUP.md for instructions");
            // Don't fail - allow full nodes without validator keys
        } else {
            eprintln!("✅ [SERVICE] Found {} SPHINCS+ key(s) in keystore", existing_keys.len());
        }
    } else if !existing_keys.is_empty() {
        // =======================================================================
        // CRITICAL FIX: Pre-populate SPHINCS+ cache for existing keystore keys
        // =======================================================================
        // Keys exist in keystore files but the SPHINCS+ cache is NOT populated.
        // We must read the secrets from keystore files and populate the cache.
        eprintln!("🔐 [SERVICE] PRODUCTION: Found {} SPHINCS+ key(s) in keystore", existing_keys.len());

        if let Some(keystore_path) = config.keystore.path() {
            use sp_core::sphincs::Pair as SphincsPair;
            use std::fs::File;
            use std::io::Read;

            for (i, public_key) in existing_keys.iter().enumerate() {
                let public_bytes: &[u8] = public_key.as_ref();

                // Construct keystore filename: 61757261<public-key-hex>
                // 61757261 = "aura" key type in hex
                let key_type_hex = "61757261";
                let public_hex = hex::encode(public_bytes);
                let filename = format!("{}{}", key_type_hex, public_hex);
                let key_path = keystore_path.join(&filename);

                eprintln!("   Key {}: 0x{}...{}", i + 1,
                    hex::encode(&public_bytes[..8]),
                    hex::encode(&public_bytes[56..64]));
                eprintln!("   📂 Reading from: {}", key_path.display());

                match File::open(&key_path) {
                    Ok(mut file) => {
                        let mut contents = String::new();
                        if let Err(e) = file.read_to_string(&mut contents) {
                            eprintln!("   ❌ Failed to read keystore file: {}", e);
                            continue;
                        }

                        // Parse JSON string (keystore stores secret as quoted hex string)
                        let secret_hex: String = match serde_json::from_str(&contents) {
                            Ok(s) => s,
                            Err(e) => {
                                eprintln!("   ❌ Failed to parse keystore JSON: {}", e);
                                continue;
                            }
                        };

                        // Decode secret from hex
                        let secret_bytes = match hex::decode(secret_hex.trim_start_matches("0x")) {
                            Ok(b) => b,
                            Err(e) => {
                                eprintln!("   ❌ Failed to decode secret hex: {}", e);
                                continue;
                            }
                        };

                        if secret_bytes.len() != 128 {
                            eprintln!("   ❌ Invalid secret key length: {} (expected 128)", secret_bytes.len());
                            continue;
                        }

                        // Pre-populate SPHINCS+ cache
                        let seed: [u8; 48] = secret_bytes[..48].try_into()
                            .expect("Secret key must have at least 48 bytes for seed");
                        let public_arr: [u8; 64] = public_bytes[..64].try_into()
                            .expect("Public key must be 64 bytes");
                        let secret_arr: [u8; 128] = secret_bytes[..128].try_into()
                            .expect("Secret key must be 128 bytes");

                        SphincsPair::insert_hardcoded_keypair(&seed, &public_arr, &secret_arr);
                        eprintln!("   ✅ Pre-populated SPHINCS+ cache for key {}", i + 1);
                    },
                    Err(e) => {
                        eprintln!("   ❌ Failed to open keystore file: {}", e);
                    }
                }
            }
        } else {
            eprintln!("   ⚠️  Keystore is in-memory, cannot read secrets from disk");
        }
    } else {
        // Production chain (ChainType::Live) with no keys - this is an error!
        eprintln!("❌ [SERVICE] PRODUCTION MODE: No SPHINCS+ keys found in keystore!");
        eprintln!("❌ [SERVICE] You must pre-install keys before starting a validator.");
        eprintln!("");
        eprintln!("   To create a keystore file:");
        eprintln!("   1. Create file: <base-path>/keystore/61757261<public-key-hex>");
        eprintln!("   2. Contents: \"0x<128-byte-secret-key-hex>\"");
        eprintln!("");
        eprintln!("   Example:");
        eprintln!("   Filename: 61757261<your-64-byte-public-key>");
        eprintln!("   Contents: \"0x<your-128-byte-secret-key>\"");
        eprintln!("");
        eprintln!("   Generate keys with: ./quantumharmony-node key generate --scheme sphincs");
    }

    let mut net_config: sc_network::config::FullNetworkConfiguration<
        Block,
        <Block as sp_runtime::traits::Block>::Hash,
        sc_network::NetworkWorker<Block, <Block as sp_runtime::traits::Block>::Hash>,
    > = sc_network::config::FullNetworkConfiguration::new(
        &config.network,
        config.prometheus_config.as_ref().map(|cfg| cfg.registry.clone()),
    );

    // Enable discovery and allow non-reserved peers for local testnet
    eprintln!("🔧 [NETWORK] Configuring network for multi-validator setup");
    eprintln!("🔧 [NETWORK] Chain type: {:?}", config.chain_spec.chain_type());
    eprintln!("🔧 [NETWORK] Role: {:?}", config.role);

    // CRITICAL FIX 1: Enable peer slots for ALL chain types including Live
    // Validators default to 0 out_peers for security, but testnets need peer connections
    // This was the ROOT CAUSE of 0 peers - Live chains weren't getting peer slot configuration
    net_config.network_config.default_peers_set.out_peers = 25;
    net_config.network_config.default_peers_set.in_peers = 25;
    eprintln!("✅ [NETWORK] Enabled peer slots: 25 in / 25 out");

    // Enable networking for ALL chain types (including Live for testnet deployments)
    // This is necessary because testnet validators run on VMs that may have private IPs
    net_config.network_config.allow_non_globals_in_dht = true;
    eprintln!("✅ [NETWORK] Enabled non-global IPs in DHT");

    // Configure transport layer — PQC (Kyber-1024 + Falcon-1024) when feature is enabled,
    // otherwise fall back to classical Noise (Ed25519).
    #[cfg(feature = "pqc-transport")]
    {
        let pqc_identity = load_or_generate_pqc_identity(&config)?;
        net_config.network_config.pqc_identity = Some(pqc_identity);
        net_config.network_config.transport = sc_network::config::TransportConfig::PostQuantum {
            enable_mdns: true,
            allow_private_ip: true,
        };
        eprintln!("🔐 [NETWORK] PQC transport enabled (Kyber-1024 + Falcon-1024)");
        eprintln!("✅ [NETWORK] Enabled mDNS and private IP addresses (post-quantum mode)");
    }
    #[cfg(not(feature = "pqc-transport"))]
    {
        net_config.network_config.transport = sc_network::config::TransportConfig::Normal {
            enable_mdns: true,
            allow_private_ip: true,
        };
        eprintln!("✅ [NETWORK] Enabled mDNS and private IP addresses (classical mode)");
    }

    // Handle public address configuration
    if let Some(listen_addr) = config.network.listen_addresses.first() {
        let addr_str = listen_addr.to_string();

        // Extract port number
        let port = addr_str.split("/tcp/").nth(1)
            .and_then(|s| s.parse::<u16>().ok())
            .unwrap_or(30333);

        if addr_str.contains("127.0.0.1") {
            // Localhost NAT Bridge: Create virtual addresses for local testing
            let virtual_host_id = (port - 30333) + 1;
            let virtual_ip = format!("192.168.1.{}", virtual_host_id);
            let virtual_addr = format!("/ip4/{}/tcp/{}", virtual_ip, port);
            if let Ok(parsed_addr) = virtual_addr.parse() {
                net_config.network_config.public_addresses.push(parsed_addr);
                eprintln!("✅ [NAT-BRIDGE] Localhost detected - created virtual address: {}", virtual_addr);
            }
        } else if addr_str.contains("0.0.0.0") || addr_str.contains("::") {
            // Listen on all interfaces - mDNS will handle discovery
            eprintln!("✅ [NETWORK] Listening on all interfaces (port {})", port);
        } else {
            // Specific IP address, use it directly
            net_config.network_config.public_addresses.push(listen_addr.clone());
            eprintln!("✅ [NETWORK] Set public address: {:?}", listen_addr);
        }
    }

    // PHASE 7A: Set up Coherence Vote Gossip Protocol
    eprintln!("🔧 [NETWORK] Setting up Coherence vote gossip protocol");
    let (coherence_protocol_config, coherence_notification_service) =
        crate::coherence_gossip::coherence_peers_set_config();
    net_config.add_notification_protocol(coherence_protocol_config);
    eprintln!("✅ [NETWORK] Coherence protocol added to network config");

    // PHASE 8: Set up Quantum P2P Key Exchange Protocol
    eprintln!("🔧 [NETWORK] Setting up Quantum P2P key exchange protocol");
    let (quantum_keyex_protocol_config, quantum_keyex_notification_service) =
        crate::quantum_p2p::quantum_keyex_peers_set_config();
    net_config.add_notification_protocol(quantum_keyex_protocol_config);
    eprintln!("✅ [NETWORK] Quantum P2P protocol added to network config");

    let metrics = sc_network::config::NotificationMetrics::new(
        config.prometheus_config.as_ref().map(|cfg| &cfg.registry),
    );

    let (network, system_rpc_tx, tx_handler_controller, sync_service) =
        sc_service::build_network(sc_service::BuildNetworkParams {
            config: &config,
            net_config,
            client: client.clone(),
            transaction_pool: transaction_pool.clone(),
            spawn_handle: task_manager.spawn_handle(),
            import_queue,
            block_announce_validator_builder: None,
            warp_sync_config: None,
            block_relay: None,
            metrics,
        })?;

    if config.offchain_worker.enabled {
        use futures::FutureExt;

        let offchain_workers = sc_offchain::OffchainWorkers::new(sc_offchain::OffchainWorkerOptions {
            runtime_api_provider: client.clone(),
            is_validator: config.role.is_authority(),
            keystore: Some(keystore_container.keystore()),
            offchain_db: backend.offchain_storage(),
            transaction_pool: Some(OffchainTransactionPoolFactory::new(
                transaction_pool.clone(),
            )),
            network_provider: Arc::new(network.clone()),
            enable_http_requests: true,
            custom_extensions: |_| vec![],
        })?;

        task_manager.spawn_handle().spawn(
            "offchain-workers-runner",
            "offchain-worker",
            offchain_workers.run(client.clone(), task_manager.spawn_handle()).boxed(),
        );
    }

    // ============================================================================
    // PHASE 8B: Quantum P2P Network Handler
    // ============================================================================
    //
    // Manages post-quantum secure sessions between validators using:
    // - Falcon-1024 for digital signatures
    // - ML-KEM-1024 (Kyber) for key encapsulation
    // - AES-256-GCM for encrypted messaging
    //
    eprintln!("🔧 [QUANTUM-P2P] Initializing Quantum P2P Network Handler");

    // Construct path for persistent Falcon identity key file
    let falcon_key_path = config.base_path.config_dir(config.chain_spec.id())
        .join("network")
        .join("falcon_identity.json");
    let falcon_key_path_str = falcon_key_path.to_string_lossy().to_string();
    eprintln!("🔐 [QUANTUM-P2P] Using persistent key file: {}", falcon_key_path_str);

    match crate::quantum_p2p::QuantumNetworkHandler::new_with_key_file(&falcon_key_path_str) {
        Ok(quantum_handler) => {
            let handler = std::sync::Arc::new(quantum_handler);
            let node_id = handler.node_id();
            eprintln!("✅ [QUANTUM-P2P] Handler initialized with node ID: {:?}", node_id);

            // Clone for the notification handler task
            let handler_for_task = handler.clone();
            let network_for_quantum = network.clone();

            task_manager.spawn_handle().spawn(
                "quantum-p2p-handler",
                Some("quantum"),
                quantum_p2p_handler_task(
                    handler_for_task,
                    quantum_keyex_notification_service,
                    network_for_quantum,
                ),
            );
            eprintln!("✅ [QUANTUM-P2P] Handler task spawned");
        }
        Err(e) => {
            eprintln!("⚠️  [QUANTUM-P2P] Failed to initialize handler: {}", e);
            eprintln!("   Continuing without quantum P2P (classical P2P remains operational)");
        }
    }

    // ============================================================================
    // QSSH Queue Manager & Wallet Server Integration
    // ============================================================================
    //
    // Start QSSH-RPC priority queue servers for each validator and the wallet
    // WebSocket server. This solves the "SelectNextSome polled after terminated"
    // crash by routing all stream consumption through managed queues.
    //
    // Architecture:
    // - Alice QSSH-RPC: port 42
    // - Bob QSSH-RPC: port 43
    // - Charlie QSSH-RPC: port 44
    // - Wallet WebSocket: port 9950
    //
    // Note: Only start queue manager for multi-validator dev3 chain
    if config.chain_spec.id() == "dev3" {
        eprintln!("🔧 [QSSH] Initializing QSSH Queue Manager for multi-validator setup");

        // Create and configure queue manager
        // Use unprivileged ports (>1024) for QSSH-RPC servers
        let mut queue_manager = crate::qssh_queue_manager::QsshQueueManager::new();
        queue_manager.add_validator("alice".to_string(), 9960);
        queue_manager.add_validator("bob".to_string(), 9961);
        queue_manager.add_validator("charlie".to_string(), 9962);

        // Start QSSH-RPC servers for all validators
        match queue_manager.start_all_servers().await {
            Ok(_) => {
                eprintln!("✅ [QSSH] Started QSSH-RPC servers:");
                eprintln!("   - Alice: 127.0.0.1:9960");
                eprintln!("   - Bob: 127.0.0.1:9961");
                eprintln!("   - Charlie: 127.0.0.1:9962");
            }
            Err(e) => {
                eprintln!("⚠️  [QSSH] Failed to start queue manager: {}", e);
                eprintln!("   Continuing without queue management (may crash with multiple validators)");
            }
        }
    } else {
        eprintln!("ℹ️  [QSSH] Single-validator mode detected, skipping queue manager");
        eprintln!("   Chain: {}", config.chain_spec.id());
    }

    // Start wallet WebSocket server with quantum-safe transport
    eprintln!("🔧 [WALLET] Starting wallet WebSocket server on port 9950");

    // Generate dummy Falcon-1024 keypair for POC
    // In production, this should load from a key file
    use pqcrypto_falcon::falcon1024;
    use pqcrypto_traits::sign::PublicKey as _;

    let (falcon_pk, _falcon_sk) = falcon1024::keypair();

    eprintln!("🔑 [WALLET] Generated Falcon-1024 keypair for signature verification");
    eprintln!("   Public key size: {} bytes", falcon_pk.as_bytes().len());

    let wallet_addr: SocketAddr = "127.0.0.1:9950".parse()
        .expect("Invalid wallet server address");

    // Spawn wallet server as background task
    task_manager.spawn_handle().spawn(
        "wallet-websocket-server",
        Some("wallet"),
        async move {
            if let Err(e) = crate::wallet_server::start_wallet_server(wallet_addr, falcon_pk).await {
                eprintln!("❌ [WALLET] Wallet server failed: {}", e);
            }
        },
    );

    eprintln!("✅ [WALLET] Wallet WebSocket server started on 127.0.0.1:9950");
    eprintln!("   Security: Falcon-1024 post-quantum signatures (POC mode)");
    eprintln!("   Connect wallet UI at: http://localhost:8000/quantumharmony-wallet.html");
    // ============================================================================

    let role = config.role.clone();
    let force_authoring = config.force_authoring;
    let backoff_authoring_blocks: Option<()> = None;
    let prometheus_registry = config.prometheus_registry().cloned();

    // Extract node name before config is moved
    let node_name = config.network.node_name.to_lowercase();

    let rpc_extensions_builder = {
        let client = client.clone();
        let pool = transaction_pool.clone();
        let keystore = keystore_container.keystore();

        Box::new(move |_spawn_handle| {
            let deps = crate::rpc::FullDeps {
                client: client.clone(),
                pool: pool.clone(),
                deny_unsafe: sc_rpc_api::DenyUnsafe::No,
                keystore: keystore.clone(),
            };

            crate::rpc::create_full(deps)
        })
    };

    // Clone backend for coherence gadget before moving into spawn_tasks
    let backend_for_gadget = backend.clone();

    let _rpc_handlers = sc_service::spawn_tasks(sc_service::SpawnTasksParams {
        config,
        client: client.clone(),
        backend,
        task_manager: &mut task_manager,
        keystore: keystore_container.keystore(),
        transaction_pool: transaction_pool.clone(),
        rpc_builder: rpc_extensions_builder,
        network: network.clone(),
        system_rpc_tx,
        tx_handler_controller,
        sync_service: sync_service.clone(),
        telemetry: telemetry.as_mut(),
    })?;

    // Spawn Priority Queue RPC server for validators
    // Determine validator name and port from node name
    let priority_queue_port = if node_name.contains("alice") {
        Some((5555, "Alice"))
    } else if node_name.contains("bob") {
        Some((5556, "Bob"))
    } else if node_name.contains("charlie") {
        Some((5557, "Charlie"))
    } else {
        None
    };

    if let Some((port, validator_name)) = priority_queue_port {
        eprintln!("🔮 [PQ-RPC] Starting Priority Queue RPC server for {} on port {}", validator_name, port);

        task_manager.spawn_handle().spawn(
            "priority-queue-rpc",
            None,
            async move {
                if let Err(e) = crate::priority_queue_rpc::run_server(port).await {
                    eprintln!("❌ [PQ-RPC] Priority Queue RPC server for {} failed: {:?}", validator_name, e);
                } else {
                    eprintln!("✅ [PQ-RPC] Priority Queue RPC server for {} stopped gracefully", validator_name);
                }
            },
        );

        eprintln!("✅ [PQ-RPC] Priority Queue RPC task spawned for {} on 127.0.0.1:{}", validator_name, port);
    }

    if role.is_authority() {
        eprintln!("🔧 [SERVICE] Starting Aura consensus setup for AUTHORITY role");
        eprintln!("🔧 [SERVICE] Force authoring: {}", force_authoring);

        let proposer_factory = sc_basic_authorship::ProposerFactory::new(
            task_manager.spawn_handle(),
            client.clone(),
            transaction_pool.clone(),
            prometheus_registry.as_ref(),
            telemetry.as_ref().map(|x| x.handle()),
        );
        eprintln!("🔧 [SERVICE] Proposer factory created");

        let slot_duration = sc_consensus_aura::slot_duration(&*client)?;
        eprintln!("🔧 [SERVICE] Slot duration: {:?}", slot_duration);

        let create_inherent_data_providers = move |_, ()| async move {
            let timestamp = sp_timestamp::InherentDataProvider::from_system_time();
            let slot = sp_consensus_aura::inherents::InherentDataProvider::from_timestamp_and_slot_duration(
                *timestamp,
                slot_duration,
            );
            Ok((slot, timestamp))
        };

        // DEBUG: Check has_keys before starting Aura
        eprintln!("🔧 [SERVICE] About to call start_aura with SPHINCS+ (AuraPair)...");
        {
            use sp_keystore::Keystore;
            use sp_application_crypto::key_types;
            let ks = keystore_container.keystore();
            let existing = ks.sphincs_public_keys(key_types::AURA);
            eprintln!("🔍 [DEBUG] Pre-Aura keystore check:");
            eprintln!("   SPHINCS+ keys in keystore: {}", existing.len());
            for (i, key) in existing.iter().enumerate() {
                let key_bytes: &[u8] = key.as_ref();
                eprintln!("   Key {}: 0x{}...{} ({} bytes)", i + 1,
                    hex::encode(&key_bytes[..8]),
                    hex::encode(&key_bytes[key_bytes.len()-8..]),
                    key_bytes.len());
                // Check has_keys for this specific key
                let has = ks.has_keys(&[(key_bytes.to_vec(), key_types::AURA)]);
                eprintln!("   has_keys result: {}", has);
            }
        }
        let aura_result = sc_consensus_aura::start_aura::<AuraPair, Block, _, _, _, _, _, _, _, _, _>(
            sc_consensus_aura::StartAuraParams {
                slot_duration,
                client: client.clone(),
                select_chain,
                block_import: client.clone(),
                proposer_factory,
                sync_oracle: sync_service.clone(),
                justification_sync_link: sync_service.clone(),
                create_inherent_data_providers,
                force_authoring,
                backoff_authoring_blocks,
                keystore: keystore_container.keystore(),
                block_proposal_slot_portion: sc_consensus_aura::SlotProportion::new(2f32 / 3f32),
                max_block_proposal_slot_portion: None,
                telemetry: telemetry.as_ref().map(|x| x.handle()),
                compatibility_mode: sc_consensus_aura::CompatibilityMode::None,
            },
        );

        match aura_result {
            Ok(aura) => {
                eprintln!("✅ [SERVICE] start_aura succeeded! Spawning Aura task...");
                // The AURA authoring task is considered essential
                task_manager
                    .spawn_essential_handle()
                    .spawn_blocking("aura", Some("block-authoring"), aura);
                eprintln!("✅ [SERVICE] Aura task spawned successfully");
            },
            Err(e) => {
                eprintln!("❌ [SERVICE] start_aura FAILED with error: {:?}", e);
                eprintln!("❌ [SERVICE] Error type: {}", std::any::type_name_of_val(&e));
                return Err(e.into());
            }
        }

        // Start Quantum Coherence Finality Gadget (GRANDPA equivalent)
        eprintln!("🔮 [SERVICE] Starting Quantum Coherence Finality Gadget...");

        // Initialize PQTG client if configuration provided
        let pqtg_client = if let Some(pqtg_cfg) = pqtg_config {
            eprintln!("🔧 [SERVICE] Initializing PQTG client with endpoint: {}", pqtg_cfg.endpoint);
            eprintln!("🔧 [SERVICE] QKD mode: {}", pqtg_cfg.qkd_mode);

            // Parse QKD mode
            let qkd_mode = crate::pqtg_client::QkdMode::from_str(&pqtg_cfg.qkd_mode)
                .map_err(|e| ServiceError::Other(e))?;

            // Build PQTG client configuration
            let mut pqtg_builder = crate::pqtg_client::PqtgClientBuilder::new()
                .pqtg_endpoint(pqtg_cfg.endpoint.clone())
                .qkd_mode(qkd_mode)
                .threshold_k(pqtg_cfg.threshold_k);

            // Track whether we need auto-discovery
            let needs_auto_discovery = pqtg_cfg.devices.is_none();

            // If specific devices specified, parse and add them
            if let Some(devices_str) = pqtg_cfg.devices {
                eprintln!("🔧 [SERVICE] Using specified devices: {}", devices_str);
                for device_str in devices_str.split(',') {
                    let device_type = crate::pqtg_client::DeviceType::from_str(device_str.trim())
                        .map_err(|e| ServiceError::Other(e))?;

                    // Create device config (endpoint will be set by auto-discovery or manually)
                    let device_config = crate::pqtg_client::DeviceConfig {
                        device_type: device_type.clone(),
                        device_id: format!("{}-01", device_type.as_str()),
                        pqtg_endpoint: format!("{}/devices/{}", pqtg_cfg.endpoint, device_type.as_str()),
                        qber_threshold: 0.10,
                        enabled: true,
                    };
                    pqtg_builder = pqtg_builder.add_device(device_config);
                }
            } else {
                eprintln!("🔧 [SERVICE] Will auto-discover devices from PQTG");
            }

            // Build the client
            let mut pqtg_client = pqtg_builder.build()
                .map_err(|e| ServiceError::Other(e))?;

            // Auto-discover devices if none were manually specified
            if needs_auto_discovery {
                eprintln!("🔍 [SERVICE] Auto-discovering devices...");
                // Note: This is async, but we're in an async context
                // We'll need to spawn this as a task or block on it
                // For now, we'll just create the client and let it discover devices later
                // NOTE: Device auto-discovery runs lazily on first entropy request; background spawn deferred
            }

            Some(Arc::new(pqtg_client))
        } else {
            eprintln!("ℹ️  [SERVICE] PQTG client disabled - using mock device shares");
            None
        };

        let coherence_gadget = crate::coherence_gadget::CoherenceGadget::new(
            client.clone(),
            network.clone(),
            backend_for_gadget.clone(),
            transaction_pool.clone(),
            coherence_notification_service,
            pqtg_client,
            keystore_container.keystore(),
            sync_service.clone(),
        );

        task_manager
            .spawn_handle()
            .spawn(
                "quantum-coherence-finality",
                Some("finality"),
                async move {
                    if let Err(e) = coherence_gadget.run().await {
                        eprintln!("❌ [COHERENCE] Gadget failed: {}", e);
                    }
                },
            );
        eprintln!("✅ [SERVICE] Quantum Coherence Finality Gadget spawned");

        // ============================================================================
        // PARALLEL SEGMENT PROCESSING MONITOR
        // ============================================================================
        //
        // Wraps the transaction pool with segment tracking for parallel processing
        // capability. Reports segment distribution statistics periodically.
        //
        eprintln!("🔧 [SERVICE] Initializing Parallel Segment Processing Monitor");

        // Create segmented pool wrapper for tracking
        let segmented_pool = Arc::new(SegmentedTransactionPool::new(transaction_pool.clone()));
        let segmented_pool_monitor = segmented_pool.clone();

        // Configure parallel processing parameters
        let parallel_config = ParallelProposerConfig::default();
        eprintln!("📊 [PARALLEL] Config: {} parallel segments, {} max TXs/segment",
            parallel_config.parallel_segments,
            parallel_config.max_txs_per_segment);

        // Spawn segment monitor task
        task_manager.spawn_handle().spawn(
            "segment-monitor",
            Some("parallel-processing"),
            segment_monitor_task(segmented_pool_monitor, parallel_config),
        );
        eprintln!("✅ [SERVICE] Parallel Segment Monitor spawned");
    } else {
        eprintln!("ℹ️  [SERVICE] Not an authority role, skipping Aura setup");

        // SYNC NODE: Need to receive justifications to track finality AND update Substrate finalized head
        eprintln!("🔮 [SERVICE] Starting Justification Sync for non-validator node...");

        // Shared pending justifications map - stores justifications for blocks not yet imported
        // Key: block_number, Value: (block_hash, encoded_justification)
        use std::collections::HashMap;
        type PendingJustifications = std::sync::Arc<
            std::sync::Mutex<HashMap<u32, (sp_core::H256, Vec<u8>)>>
        >;
        let pending_justifications: PendingJustifications = std::sync::Arc::new(
            std::sync::Mutex::new(HashMap::new())
        );

        // Task 1: Receive justifications from gossip and queue if block not yet imported
        let client_for_sync = client.clone();
        let pending_for_receiver = pending_justifications.clone();
        let mut notification_service_for_sync = coherence_notification_service;

        task_manager
            .spawn_handle()
            .spawn(
                "coherence-justification-receiver",
                Some("finality"),
                async move {
                    use scale_codec::Decode;
                    use crate::coherence_gossip::GossipMessage;
                    use crate::coherence_justification::COHERENCE_ENGINE_ID;
                    use sc_network::service::traits::NotificationEvent;
                    use sc_client_api::backend::Finalizer;
                    use sp_blockchain::HeaderBackend;

                    eprintln!("📡 [SYNC] Justification receiver task started for non-validator node");

                    loop {
                        let event = match notification_service_for_sync.next_event().await {
                            Some(e) => e,
                            None => {
                                eprintln!("🔌 [SYNC] Notification service closed");
                                break;
                            }
                        };

                        if let NotificationEvent::NotificationReceived { peer, notification } = event {
                            // Try to decode as gossip message
                            if let Ok(message) = GossipMessage::<Block>::decode(&mut &notification[..]) {
                                // Only handle justifications - ignore votes
                                if let GossipMessage::Justification { block_hash, block_number, encoded_justification } = message {
                                    log::info!(
                                        "📨 [SYNC] Received justification for block #{} from {:?}",
                                        block_number, peer
                                    );

                                    // Check if already finalized
                                    let finalized_number = client_for_sync.info().finalized_number;
                                    if block_number <= finalized_number {
                                        log::debug!("⏭️  [SYNC] Block #{} already finalized", block_number);
                                        continue;
                                    }

                                    // Try to apply the justification immediately
                                    let substrate_justification = (COHERENCE_ENGINE_ID, encoded_justification.clone());
                                    match client_for_sync.finalize_block(block_hash, Some(substrate_justification), true) {
                                        Ok(()) => {
                                            log::info!(
                                                "🎉 [SYNC] Block #{} finalized via received justification!",
                                                block_number
                                            );
                                        },
                                        Err(e) => {
                                            // Block not yet imported - queue the justification for later
                                            let err_str = format!("{:?}", e);
                                            if err_str.contains("UnknownBlock") || err_str.contains("not found") {
                                                log::info!(
                                                    "📥 [SYNC] Block #{} not imported yet, queuing justification for later",
                                                    block_number
                                                );
                                                if let Ok(mut pending) = pending_for_receiver.lock() {
                                                    pending.insert(block_number, (block_hash, encoded_justification));
                                                    // Keep queue manageable - remove very old entries
                                                    if pending.len() > 100 {
                                                        let min_keep = block_number.saturating_sub(50);
                                                        pending.retain(|&k, _| k >= min_keep);
                                                    }
                                                }
                                            } else {
                                                log::warn!("❌ [SYNC] Failed to finalize block #{}: {:?}", block_number, e);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                },
            );
        eprintln!("✅ [SERVICE] Justification Receiver spawned");

        // Task 2: Listen for block imports and apply pending justifications
        let client_for_import = client.clone();
        let pending_for_import = pending_justifications.clone();
        // Import BlockchainEvents trait to get access to import_notification_stream
        use sc_client_api::BlockchainEvents;
        let mut import_stream = client.import_notification_stream();

        task_manager
            .spawn_handle()
            .spawn(
                "coherence-justification-applier",
                Some("finality"),
                async move {
                    use futures::StreamExt;
                    use crate::coherence_justification::COHERENCE_ENGINE_ID;
                    use sc_client_api::backend::Finalizer;
                    use sp_blockchain::HeaderBackend;
                    use sp_runtime::traits::Header as HeaderT;

                    eprintln!("📡 [SYNC] Justification applier task started - watching for block imports");

                    while let Some(notification) = import_stream.next().await {
                        let block_number = *notification.header.number();

                        // Check if we have a pending justification for this block
                        let pending_entry = {
                            if let Ok(mut pending) = pending_for_import.lock() {
                                pending.remove(&block_number)
                            } else {
                                None
                            }
                        };

                        if let Some((block_hash, encoded_justification)) = pending_entry {
                            log::info!(
                                "📤 [SYNC] Block #{} imported, applying queued justification",
                                block_number
                            );

                            // Verify hash matches
                            if notification.hash != block_hash {
                                log::warn!(
                                    "⚠️  [SYNC] Block #{} hash mismatch! Expected {:?}, got {:?}",
                                    block_number, block_hash, notification.hash
                                );
                                continue;
                            }

                            // Check if already finalized (might have been finalized by another path)
                            let finalized_number = client_for_import.info().finalized_number;
                            if block_number <= finalized_number {
                                log::debug!("⏭️  [SYNC] Block #{} already finalized", block_number);
                                continue;
                            }

                            // Apply the justification
                            let substrate_justification = (COHERENCE_ENGINE_ID, encoded_justification);
                            match client_for_import.finalize_block(block_hash, Some(substrate_justification), true) {
                                Ok(()) => {
                                    log::info!(
                                        "🎉 [SYNC] Block #{} finalized via queued justification!",
                                        block_number
                                    );
                                },
                                Err(e) => {
                                    log::warn!("❌ [SYNC] Failed to finalize queued block #{}: {:?}", block_number, e);
                                }
                            }
                        }
                    }

                    eprintln!("🔌 [SYNC] Import notification stream closed");
                },
            );
        eprintln!("✅ [SERVICE] Justification Applier spawned for non-validator");
    }

    // Network is started automatically by build_network
    Ok(task_manager)
}

/// Build the full node service for the QuantumHarmony runtime
pub async fn build_full(
    config: Configuration,
    pqtg_config: Option<PqtgConfiguration>,
) -> Result<TaskManager, ServiceError> {
    new_full(config, pqtg_config).await
}

/// Quantum P2P handler task
///
/// Processes incoming notification messages and manages quantum key exchange sessions
async fn quantum_p2p_handler_task(
    handler: std::sync::Arc<crate::quantum_p2p::QuantumNetworkHandler>,
    mut notification_service: Box<dyn sc_network::service::traits::NotificationService>,
    _network: std::sync::Arc<dyn sc_network::service::traits::NetworkService>,
) {
    use scale_codec::{Decode, Encode};

    eprintln!("🔧 [QUANTUM-P2P] Handler task started, waiting for events...");

    // Get our announce message to send to new peers
    let announce_message = match handler.get_announce_message() {
        Ok(msg) => msg.encode(),
        Err(e) => {
            eprintln!("❌ [QUANTUM-P2P] Failed to create announce message: {}", e);
            return;
        }
    };

    loop {
        let event = match notification_service.next_event().await {
            Some(e) => e,
            None => {
                eprintln!("🔌 [QUANTUM-P2P] Notification service closed");
                break;
            }
        };

        match event {
            sc_network::service::traits::NotificationEvent::ValidateInboundSubstream {
                peer,
                handshake: _,
                result_tx
            } => {
                // Accept all inbound connections for key exchange
                let _ = result_tx.send(sc_network::service::traits::ValidationResult::Accept);
                eprintln!("🔗 [QUANTUM-P2P] Accepted substream from {:?}", peer);
            }

            sc_network::service::traits::NotificationEvent::NotificationStreamOpened {
                peer,
                handshake: _,
                negotiated_fallback: _,
                direction: _,
            } => {
                eprintln!("📡 [QUANTUM-P2P] Stream opened with {:?}", peer);
                handler.on_peer_connected(peer);

                // Send our announce message (send_sync_notification returns ())
                notification_service.send_sync_notification(&peer, announce_message.clone());
                eprintln!("📤 [QUANTUM-P2P] Sent announce to {:?}", peer);
            }

            sc_network::service::traits::NotificationEvent::NotificationStreamClosed { peer } => {
                eprintln!("🔌 [QUANTUM-P2P] Stream closed with {:?}", peer);
                handler.on_peer_disconnected(peer);
            }

            sc_network::service::traits::NotificationEvent::NotificationReceived { peer, notification } => {
                // Decode and process the message
                match crate::quantum_p2p::QuantumKeyExchangeMessage::decode(&mut &notification[..]) {
                    Ok(message) => {
                        eprintln!("📥 [QUANTUM-P2P] Received message from {:?}: {:?}", peer, std::mem::discriminant(&message));

                        // Process the message and potentially send a response
                        if let Some(response) = handler.handle_message(peer, message) {
                            let response_bytes = response.encode();
                            notification_service.send_sync_notification(&peer, response_bytes);
                            eprintln!("📤 [QUANTUM-P2P] Sent response to {:?}", peer);
                        }

                        // Log session status
                        let session_count = handler.active_session_count();
                        eprintln!("🔐 [QUANTUM-P2P] Active quantum sessions: {}", session_count);
                    }
                    Err(e) => {
                        eprintln!("⚠️  [QUANTUM-P2P] Failed to decode message from {:?}: {:?}", peer, e);
                    }
                }
            }
        }
    }
}

/// Load validator SPHINCS+ key from a JSON key file
///
/// Expected JSON format (from sphincs-keygen tool):
/// ```json
/// {
///   "name": "validator-1",
///   "public_key": "0x...",
///   "secret_key": "0x...",
///   "ss58_address": "5...",
///   "account_id": "0x..."
/// }
/// ```
///
/// Returns (secret_key_hex, public_key_hex) tuple
fn load_validator_key_from_file(path: &str) -> Result<(String, String), String> {
    use std::fs;

    // Read the file
    let content = fs::read_to_string(path)
        .map_err(|e| format!("Failed to read key file '{}': {}", path, e))?;

    // Parse as JSON
    let json: serde_json::Value = serde_json::from_str(&content)
        .map_err(|e| format!("Failed to parse key file as JSON: {}", e))?;

    // Extract secret_key and public_key
    let secret_key = json.get("secret_key")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "Missing 'secret_key' field in key file".to_string())?
        .to_string();

    let public_key = json.get("public_key")
        .and_then(|v| v.as_str())
        .ok_or_else(|| "Missing 'public_key' field in key file".to_string())?
        .to_string();

    // Validate key lengths (SPHINCS+ keys)
    let secret_bytes = hex::decode(secret_key.trim_start_matches("0x"))
        .map_err(|e| format!("Invalid hex in secret_key: {}", e))?;
    let public_bytes = hex::decode(public_key.trim_start_matches("0x"))
        .map_err(|e| format!("Invalid hex in public_key: {}", e))?;

    // SPHINCS+-SHAKE-256s: 64-byte public key, 128-byte secret key
    if public_bytes.len() != 64 {
        return Err(format!("Invalid public key length: expected 64 bytes, got {}", public_bytes.len()));
    }
    if secret_bytes.len() != 128 {
        return Err(format!("Invalid secret key length: expected 128 bytes, got {}", secret_bytes.len()));
    }

    // Log key info (without exposing secret)
    if let Some(name) = json.get("name").and_then(|v| v.as_str()) {
        eprintln!("📋 [SERVICE] Key file: name={}", name);
    }
    if let Some(ss58) = json.get("ss58_address").and_then(|v| v.as_str()) {
        eprintln!("📋 [SERVICE] Key file: ss58={}", ss58);
    }

    Ok((secret_key, public_key))
}

/// Segment monitor task for parallel processing statistics
///
/// Periodically reports segment load distribution and theoretical TPS estimates
/// based on the parallel processing configuration.
async fn segment_monitor_task<P>(
    segmented_pool: Arc<SegmentedTransactionPool<P, Block>>,
    config: ParallelProposerConfig,
)
where
    P: sc_transaction_pool_api::TransactionPool<Block = Block> + 'static,
{
    use tokio::time::{interval, Duration as TokioDuration};

    eprintln!("📊 [SEGMENT-MONITOR] Starting segment distribution monitor");
    eprintln!("📊 [SEGMENT-MONITOR] Reporting every 30 seconds");

    let mut report_interval = interval(TokioDuration::from_secs(30));

    loop {
        report_interval.tick().await;

        // Get current load distribution
        let loads = segmented_pool.get_load_distribution();
        let active_segments = segmented_pool.get_active_segments();

        // Calculate statistics
        let total_pending: u64 = loads.iter().map(|(_, load)| load).sum();
        let active_count = active_segments.len() as u32;

        if total_pending > 0 || active_count > 0 {
            // Calculate stats for parallel speedup estimation
            let stats = ParallelBlockStats::from_loads(&loads, config.parallel_segments as u32);

            eprintln!("📊 [SEGMENT-MONITOR] ════════════════════════════════════");
            eprintln!("📊 [SEGMENT-MONITOR] Parallel Processing Status:");
            eprintln!("📊 [SEGMENT-MONITOR]   Active segments: {}/512", active_count);
            eprintln!("📊 [SEGMENT-MONITOR]   Total pending TXs: {}", total_pending);
            eprintln!("📊 [SEGMENT-MONITOR]   Speedup factor: {:.2}x", stats.speedup_factor);
            eprintln!("📊 [SEGMENT-MONITOR]   Theoretical TPS: {:.1}",
                crate::parallel_proposer::calculate_theoretical_tps(
                    0.5, // base TPS per segment
                    active_count,
                    config.parallel_segments as u32
                ));
            eprintln!("📊 [SEGMENT-MONITOR] ════════════════════════════════════");

            // Log top 5 busiest segments
            let mut sorted_loads: Vec<_> = loads.iter()
                .filter(|(_, load)| *load > 0)
                .collect();
            sorted_loads.sort_by(|a, b| b.1.cmp(&a.1));

            if !sorted_loads.is_empty() {
                eprintln!("📊 [SEGMENT-MONITOR] Top segments by load:");
                for (i, (seg_id, load)) in sorted_loads.iter().take(5).enumerate() {
                    eprintln!("📊 [SEGMENT-MONITOR]   {}. Segment {}: {} TXs", i + 1, seg_id, load);
                }
            }
        }
    }
}
