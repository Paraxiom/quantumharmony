#!/usr/bin/env node

const { ApiPromise, WsProvider } = require('@polkadot/api');

async function checkKeystore() {
    const provider = new WsProvider('ws://127.0.0.1:9944');
    const api = await ApiPromise.create({ provider });

    console.log('✅ Connected to node');

    // Check what keys are in the keystore
    try {
        const hasKeys = await api.rpc('author_hasKey',
            '0x2067791579b4b7b59ebf4cc30406a89347f2a3bf608348bf5384cb7be33772127100000000000000000000000000000000000000000000000000000000000000',
            '0x61757261'  // "aura"
        );
        console.log('Has key for public [32, 103, 21...]:', hasKeys.toHuman());
    } catch (e) {
        console.error('Error checking key:', e.message);
    }

    // Check authorities from Session pallet
    try {
        const validators = await api.query.session.validators();
        console.log('\n📋 Session validators:');
        validators.forEach((v, i) => {
            console.log(`  ${i + 1}. ${v.toHex()}`);
        });
    } catch (e) {
        console.error('Error querying validators:', e.message);
    }

    // Check Aura authorities
    try {
        const authorities = await api.query.aura.authorities();
        console.log('\n📋 Aura authorities:');
        authorities.forEach((auth, i) => {
            const hex = auth.toHex();
            console.log(`  ${i + 1}. ${hex} (${hex.length - 2} hex chars = ${(hex.length - 2) / 2} bytes)`);
        });
    } catch (e) {
        console.error('Error querying Aura authorities:', e.message);
    }

    await api.disconnect();
}

checkKeystore().catch(console.error);
