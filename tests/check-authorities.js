#!/usr/bin/env node
/**
 * Check Aura authorities configuration
 */

const { ApiPromise, WsProvider } = require('@polkadot/api');

async function checkAuthorities() {
    console.log('🔍 Checking Aura authorities configuration...\n');

    try {
        const provider = new WsProvider('ws://127.0.0.1:9944');
        const api = await ApiPromise.create({ provider });

        // Check Aura authorities
        console.log('📋 Querying Aura authorities...');
        const authorities = await api.query.aura.authorities();
        console.log(`✅ Aura authorities count: ${authorities.length}`);

        if (authorities.length === 0) {
            console.log('❌ NO AUTHORITIES! This is why blocks are not being produced!');
        } else {
            console.log('✅ Authorities configured:');
            authorities.forEach((auth, i) => {
                console.log(`   ${i + 1}. ${auth.toString()}`);
            });
        }

        // Check Session keys
        console.log('\n📋 Querying Session validators...');
        const validators = await api.query.session.validators();
        console.log(`✅ Session validators count: ${validators.length}`);
        validators.forEach((val, i) => {
            console.log(`   ${i + 1}. ${val.toString()}`);
        });

        // Check Session keys for first validator
        if (validators.length > 0) {
            console.log('\n📋 Checking session keys for first validator...');
            const firstValidator = validators[0];
            const keys = await api.query.session.nextKeys(firstValidator);
            console.log(`Session keys for ${firstValidator.toString()}:`);
            console.log(keys.toHuman());
        }

        // Check current session
        console.log('\n📋 Current session info...');
        const currentIndex = await api.query.session.currentIndex();
        console.log(`Current session index: ${currentIndex}`);

        await api.disconnect();

    } catch (err) {
        console.error('❌ Error:', err.message);
        process.exit(1);
    }
}

checkAuthorities();
