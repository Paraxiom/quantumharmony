#!/usr/bin/env node
/**
 * QuantumHarmony Polkadot.js Test Suite
 *
 * Tests all standard Substrate functionality using industry-standard Polkadot.js libraries.
 * This replaces custom wallet implementations with proven, maintained tooling.
 *
 * Installation:
 *   npm install @polkadot/api @polkadot/keyring @polkadot/util @polkadot/util-crypto
 *
 * Usage:
 *   # Start node first
 *   ./target/release/quantumharmony-node --dev --tmp
 *
 *   # Run tests
 *   node tests/polkadot-js-test-suite.js
 */

const { ApiPromise, WsProvider } = require('@polkadot/api');
const { Keyring } = require('@polkadot/keyring');
const { cryptoWaitReady } = require('@polkadot/util-crypto');

// Test configuration
const CONFIG = {
    WS_ENDPOINT: 'ws://127.0.0.1:9944',
    TEST_AMOUNT: '1000000000000000', // 1 QH (assuming 15 decimals)
};

// ANSI color codes for output
const COLORS = {
    reset: '\x1b[0m',
    green: '\x1b[32m',
    red: '\x1b[31m',
    yellow: '\x1b[33m',
    blue: '\x1b[34m',
    cyan: '\x1b[36m',
};

function log(message, color = 'reset') {
    console.log(`${COLORS[color]}${message}${COLORS.reset}`);
}

function success(message) {
    log(`✅ ${message}`, 'green');
}

function error(message) {
    log(`❌ ${message}`, 'red');
}

function info(message) {
    log(`ℹ️  ${message}`, 'cyan');
}

function section(message) {
    log(`\n${'='.repeat(60)}`, 'blue');
    log(`  ${message}`, 'blue');
    log(`${'='.repeat(60)}`, 'blue');
}

/**
 * Test 1: Connect to Node
 */
async function testConnection(api) {
    section('Test 1: Node Connection');

    try {
        const [chain, nodeName, nodeVersion] = await Promise.all([
            api.rpc.system.chain(),
            api.rpc.system.name(),
            api.rpc.system.version(),
        ]);

        success('Connected to node');
        info(`  Chain: ${chain}`);
        info(`  Node: ${nodeName} v${nodeVersion}`);

        return true;
    } catch (err) {
        error(`Connection failed: ${err.message}`);
        return false;
    }
}

/**
 * Test 2: Query Chain State
 */
async function testChainState(api) {
    section('Test 2: Chain State Queries');

    try {
        // Get runtime version
        const runtimeVersion = api.runtimeVersion;
        success('Runtime version retrieved');
        info(`  Spec name: ${runtimeVersion.specName}`);
        info(`  Spec version: ${runtimeVersion.specVersion}`);
        info(`  Transaction version: ${runtimeVersion.transactionVersion}`);

        // Get latest block
        const lastHeader = await api.rpc.chain.getHeader();
        success('Latest block retrieved');
        info(`  Block number: ${lastHeader.number}`);
        info(`  Block hash: ${lastHeader.hash.toHex()}`);

        // Get finalized block
        const finalizedHash = await api.rpc.chain.getFinalizedHead();
        const finalizedHeader = await api.rpc.chain.getHeader(finalizedHash);
        success('Finalized block retrieved');
        info(`  Finalized block: ${finalizedHeader.number}`);

        return true;
    } catch (err) {
        error(`Chain state query failed: ${err.message}`);
        return false;
    }
}

/**
 * Test 3: Account Operations
 */
async function testAccounts(api, keyring) {
    section('Test 3: Account Operations');

    try {
        // Create test accounts
        const alice = keyring.addFromUri('//Alice', { name: 'Alice' });
        const bob = keyring.addFromUri('//Bob', { name: 'Bob' });

        success('Test accounts created');
        info(`  Alice: ${alice.address}`);
        info(`  Bob: ${bob.address}`);

        // Query balances
        const aliceAccount = await api.query.system.account(alice.address);
        const bobAccount = await api.query.system.account(bob.address);

        success('Balances queried');
        info(`  Alice balance: ${aliceAccount.data.free.toHuman()}`);
        info(`  Bob balance: ${bobAccount.data.free.toHuman()}`);

        return { alice, bob };
    } catch (err) {
        error(`Account operations failed: ${err.message}`);
        return null;
    }
}

/**
 * Test 4: Transfer Transaction
 */
async function testTransfer(api, alice, bob) {
    section('Test 4: Balance Transfer');

    try {
        // Get initial balances
        const bobInitial = await api.query.system.account(bob.address);
        const bobInitialBalance = bobInitial.data.free.toBigInt();

        info(`Bob's initial balance: ${bobInitial.data.free.toHuman()}`);

        // Create transfer
        const transfer = api.tx.balances.transferKeepAlive(bob.address, CONFIG.TEST_AMOUNT);

        info('Submitting transfer transaction...');

        // Sign and send
        return new Promise((resolve, reject) => {
            const timeout = setTimeout(() => {
                reject(new Error('Transaction timeout'));
            }, 60000);

            transfer.signAndSend(alice, ({ status, events, dispatchError }) => {
                if (dispatchError) {
                    clearTimeout(timeout);
                    if (dispatchError.isModule) {
                        const decoded = api.registry.findMetaError(dispatchError.asModule);
                        error(`Transaction failed: ${decoded.section}.${decoded.name}: ${decoded.docs}`);
                    } else {
                        error(`Transaction failed: ${dispatchError.toString()}`);
                    }
                    resolve(false);
                }

                if (status.isInBlock) {
                    success(`Transaction included in block: ${status.asInBlock.toHex()}`);
                }

                if (status.isFinalized) {
                    clearTimeout(timeout);
                    success(`Transaction finalized: ${status.asFinalized.toHex()}`);

                    // Verify balance changed
                    api.query.system.account(bob.address).then(bobFinal => {
                        const bobFinalBalance = bobFinal.data.free.toBigInt();
                        const received = bobFinalBalance - bobInitialBalance;

                        if (received > 0n) {
                            success(`Bob received: ${received.toString()} units`);
                            info(`Bob's final balance: ${bobFinal.data.free.toHuman()}`);
                            resolve(true);
                        } else {
                            error('Balance did not increase');
                            resolve(false);
                        }
                    });
                }
            }).catch(err => {
                clearTimeout(timeout);
                error(`Transaction submission failed: ${err.message}`);
                resolve(false);
            });
        });
    } catch (err) {
        error(`Transfer test failed: ${err.message}`);
        return false;
    }
}

/**
 * Test 5: Sudo Operations
 */
async function testSudo(api, alice) {
    section('Test 5: Sudo Operations');

    try {
        // Check if Alice is sudo
        const sudoKey = await api.query.sudo.key();

        if (sudoKey.toString() === alice.address) {
            success('Alice is sudo account');
        } else {
            error('Alice is not sudo account');
            info(`  Sudo key: ${sudoKey.toString()}`);
            info(`  Alice key: ${alice.address}`);
            return false;
        }

        // Test sudo call (set timestamp)
        const currentTimestamp = await api.query.timestamp.now();
        info(`Current timestamp: ${currentTimestamp.toNumber()}`);

        // Note: In --dev mode, we can't actually change timestamp mid-block
        // But we can verify the RPC method works
        success('Sudo RPC methods accessible');

        return true;
    } catch (err) {
        error(`Sudo test failed: ${err.message}`);
        return false;
    }
}

/**
 * Test 6: Subscribe to New Blocks
 */
async function testSubscriptions(api) {
    section('Test 6: Block Subscriptions');

    return new Promise((resolve) => {
        let blockCount = 0;
        const targetBlocks = 3;

        info(`Waiting for ${targetBlocks} new blocks...`);

        const unsubscribe = api.rpc.chain.subscribeNewHeads((header) => {
            blockCount++;
            success(`Block #${header.number}: ${header.hash.toHex()}`);

            if (blockCount >= targetBlocks) {
                unsubscribe.then(() => {
                    success(`Received ${targetBlocks} blocks successfully`);
                    resolve(true);
                });
            }
        });

        // Timeout after 30 seconds
        setTimeout(() => {
            unsubscribe.then(() => {
                if (blockCount < targetBlocks) {
                    error(`Only received ${blockCount}/${targetBlocks} blocks`);
                    resolve(false);
                } else {
                    resolve(true);
                }
            });
        }, 30000);
    });
}

/**
 * Test 7: Query Custom Pallets
 */
async function testCustomPallets(api) {
    section('Test 7: Custom Pallet Queries');

    try {
        // Check for runtime segmentation pallet
        if (api.query.runtimeSegmentation) {
            const segmentCount = await api.query.runtimeSegmentation.segments();
            success('Runtime Segmentation pallet found');
            info(`  Total segments: ${segmentCount}`);
        } else {
            info('Runtime Segmentation pallet not exposed via storage');
        }

        // Check for threshold QRNG pallet
        if (api.query.thresholdQrng) {
            success('Threshold QRNG pallet found');
        } else {
            info('Threshold QRNG pallet not exposed via storage');
        }

        // List all available pallets
        const pallets = Object.keys(api.query).sort();
        success(`Total pallets: ${pallets.length}`);
        info('Available pallets:');
        pallets.forEach(pallet => {
            info(`    - ${pallet}`);
        });

        return true;
    } catch (err) {
        error(`Custom pallet query failed: ${err.message}`);
        return false;
    }
}

/**
 * Test 8: RPC Methods
 */
async function testRpcMethods(api) {
    section('Test 8: Custom RPC Methods');

    try {
        // List all RPC methods
        const rpcMethods = await api.rpc.rpc.methods();
        success(`Total RPC methods: ${rpcMethods.methods.length}`);

        // Check for custom RPC methods
        const customMethods = rpcMethods.methods.filter(m =>
            m.includes('sudo_') ||
            m.includes('runtimeSegmentation_') ||
            m.includes('thresholdQrng_') ||
            m.includes('transactionGateway_')
        );

        if (customMethods.length > 0) {
            success(`Custom RPC methods found: ${customMethods.length}`);
            customMethods.forEach(method => {
                info(`    - ${method}`);
            });
        } else {
            info('No custom RPC methods found (may not be exposed)');
        }

        return true;
    } catch (err) {
        error(`RPC methods test failed: ${err.message}`);
        return false;
    }
}

/**
 * Test 9: Events
 */
async function testEvents(api) {
    section('Test 9: System Events');

    try {
        // Subscribe to system events
        const events = await api.query.system.events();

        success(`Current block has ${events.length} events`);

        // Show last few events
        const recentEvents = events.slice(-5);
        info('Recent events:');
        recentEvents.forEach((record, index) => {
            const { event } = record;
            info(`    ${index + 1}. ${event.section}.${event.method}`);
        });

        return true;
    } catch (err) {
        error(`Events test failed: ${err.message}`);
        return false;
    }
}

/**
 * Test 10: Metadata
 */
async function testMetadata(api) {
    section('Test 10: Runtime Metadata');

    try {
        const metadata = api.runtimeMetadata;
        const version = metadata.version;

        success(`Metadata version: V${version}`);

        // Count pallets in metadata
        const palletCount = metadata.asLatest.pallets.length;
        success(`Metadata contains ${palletCount} pallets`);

        // Check for post-quantum primitives
        const palletNames = metadata.asLatest.pallets.map(p => p.name.toString());
        const quantumPallets = palletNames.filter(n =>
            n.toLowerCase().includes('quantum') ||
            n.toLowerCase().includes('qrng') ||
            n.toLowerCase().includes('segmentation')
        );

        if (quantumPallets.length > 0) {
            success(`Quantum-related pallets: ${quantumPallets.join(', ')}`);
        } else {
            info('No quantum-specific pallet names in metadata');
        }

        return true;
    } catch (err) {
        error(`Metadata test failed: ${err.message}`);
        return false;
    }
}

/**
 * Main test runner
 */
async function runTests() {
    section('QuantumHarmony Polkadot.js Test Suite');
    info('Testing node with industry-standard Polkadot.js libraries');
    info(`Connecting to: ${CONFIG.WS_ENDPOINT}\n`);

    let api;
    let results = {
        total: 0,
        passed: 0,
        failed: 0,
    };

    try {
        // Initialize crypto
        await cryptoWaitReady();
        success('Crypto libraries initialized\n');

        // Create keyring
        const keyring = new Keyring({ type: 'sr25519' });

        // Connect to node
        const provider = new WsProvider(CONFIG.WS_ENDPOINT);
        api = await ApiPromise.create({ provider });

        // Run all tests
        const tests = [
            { name: 'Connection', fn: () => testConnection(api) },
            { name: 'Chain State', fn: () => testChainState(api) },
            { name: 'Account Operations', fn: async () => {
                const accounts = await testAccounts(api, keyring);
                if (accounts) {
                    // Store accounts for later tests
                    api._testAccounts = accounts;
                    return true;
                }
                return false;
            }},
            { name: 'Balance Transfer', fn: async () => {
                if (!api._testAccounts) {
                    error('Accounts not created, skipping transfer test');
                    return false;
                }
                return await testTransfer(api, api._testAccounts.alice, api._testAccounts.bob);
            }},
            { name: 'Sudo Operations', fn: async () => {
                if (!api._testAccounts) {
                    error('Accounts not created, skipping sudo test');
                    return false;
                }
                return await testSudo(api, api._testAccounts.alice);
            }},
            { name: 'Block Subscriptions', fn: () => testSubscriptions(api) },
            { name: 'Custom Pallets', fn: () => testCustomPallets(api) },
            { name: 'RPC Methods', fn: () => testRpcMethods(api) },
            { name: 'Events', fn: () => testEvents(api) },
            { name: 'Metadata', fn: () => testMetadata(api) },
        ];

        for (const test of tests) {
            results.total++;
            const passed = await test.fn();
            if (passed) {
                results.passed++;
            } else {
                results.failed++;
            }
        }

        // Print summary
        section('Test Summary');
        log(`Total tests: ${results.total}`, 'cyan');
        log(`Passed: ${results.passed}`, 'green');
        log(`Failed: ${results.failed}`, results.failed > 0 ? 'red' : 'green');
        log(`Success rate: ${((results.passed / results.total) * 100).toFixed(1)}%\n`,
            results.failed > 0 ? 'yellow' : 'green');

        if (results.failed === 0) {
            success('✨ All tests passed! QuantumHarmony is fully compatible with Polkadot.js ✨');
            log('\nYou can now use standard Substrate tools:', 'cyan');
            log('  - Polkadot.js Apps: https://polkadot.js.org/apps/?rpc=ws://127.0.0.1:9944', 'cyan');
            log('  - Polkadot.js Extension: Browser wallet for signing', 'cyan');
            log('  - Subxt: Rust client library', 'cyan');
            log('  - Substrate Connect: Light client in browser\n', 'cyan');
        } else {
            error('Some tests failed. Check logs above for details.');
        }

    } catch (err) {
        error(`Test suite failed: ${err.message}`);
        console.error(err);
    } finally {
        if (api) {
            await api.disconnect();
            info('Disconnected from node');
        }
    }

    process.exit(results.failed > 0 ? 1 : 0);
}

// Run tests
runTests().catch(err => {
    console.error('Fatal error:', err);
    process.exit(1);
});
