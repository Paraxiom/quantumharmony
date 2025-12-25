#!/usr/bin/env node

/**
 * Drista Wallet - P2P Connection
 * Connects to KIRQ blockchain through P2P relay
 */

const { ApiPromise, WsProvider } = require('@polkadot/api');
const { Keyring } = require('@polkadot/keyring');

// The P2P relay exposes blockchain locally
const BLOCKCHAIN_URL = 'ws://localhost:9944';

async function connectViaP2P() {
    console.log('═══════════════════════════════════════════════════════════');
    console.log('   Drista Wallet - P2P Connection');
    console.log('═══════════════════════════════════════════════════════════');

    console.log('\nConnecting to KIRQ via P2P relay...');
    console.log('Route: Work Mac → Lab (P2P) → KIRQ Network');

    try {
        const provider = new WsProvider(BLOCKCHAIN_URL);
        const api = await ApiPromise.create({ provider });

        const [chain, nodeName, nodeVersion] = await Promise.all([
            api.rpc.system.chain(),
            api.rpc.system.name(),
            api.rpc.system.version()
        ]);

        console.log('\n✓ Connected via P2P!');
        console.log('  Chain:', chain.toString());
        console.log('  Node:', nodeName.toString());
        console.log('  Version:', nodeVersion.toString());

        // Get network info
        const [peers, health] = await Promise.all([
            api.rpc.system.peers(),
            api.rpc.system.health()
        ]);

        console.log('\nNetwork Status:');
        console.log('  Peers:', peers.length);
        console.log('  Syncing:', health.isSyncing.toString());

        // Initialize keyring
        const keyring = new Keyring({ type: 'sr25519' });
        const alice = keyring.addFromUri('//Alice');
        const bob = keyring.addFromUri('//Bob');

        // Check balances
        const [aliceAccount, bobAccount] = await Promise.all([
            api.query.system.account(alice.address),
            api.query.system.account(bob.address)
        ]);

        console.log('\nAccounts:');
        console.log('  Alice:', alice.address);
        console.log('    Balance:', aliceAccount.data.free.toHuman());
        console.log('  Bob:', bob.address);
        console.log('    Balance:', bobAccount.data.free.toHuman());

        // Subscribe to new blocks
        console.log('\nListening for new blocks...');
        const unsubscribe = await api.rpc.chain.subscribeNewHeads((header) => {
            console.log(`  Block #${header.number}: ${header.hash}`);
        });

        // Keep running
        process.on('SIGINT', async () => {
            console.log('\nDisconnecting...');
            unsubscribe();
            await api.disconnect();
            process.exit(0);
        });

    } catch (error) {
        console.error('\n✗ Connection failed:', error.message);
        console.log('\nTroubleshooting:');
        console.log('1. Ensure P2P relay is running: ./start-p2p-relay.sh');
        console.log('2. Check your Lab Machine is accessible via VPN');
        console.log('3. Verify KIRQ blockchain is running on Lab network');
        process.exit(1);
    }
}

// Run
connectViaP2P().catch(console.error);