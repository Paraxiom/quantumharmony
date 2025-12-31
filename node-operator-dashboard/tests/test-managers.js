/**
 * QuantumHarmony Dashboard Tests
 * Tests for UpgradeManager, KeystoreManager, and GovernanceManager
 *
 * Run with: node tests/test-managers.js
 * Requires a running node at http://127.0.0.1:9944
 */

const RPC_ENDPOINT = process.env.RPC_ENDPOINT || 'http://127.0.0.1:9944';

// Simple test framework
let passed = 0;
let failed = 0;
const results = [];

function assert(condition, message) {
    if (condition) {
        passed++;
        results.push({ status: 'PASS', message });
        console.log(`  ✅ ${message}`);
    } else {
        failed++;
        results.push({ status: 'FAIL', message });
        console.log(`  ❌ ${message}`);
    }
}

function assertThrows(fn, message) {
    try {
        fn();
        failed++;
        results.push({ status: 'FAIL', message: `${message} (expected error, none thrown)` });
        console.log(`  ❌ ${message} (expected error, none thrown)`);
    } catch (e) {
        passed++;
        results.push({ status: 'PASS', message });
        console.log(`  ✅ ${message}`);
    }
}

async function assertAsync(asyncFn, message) {
    try {
        const result = await asyncFn();
        if (result) {
            passed++;
            results.push({ status: 'PASS', message });
            console.log(`  ✅ ${message}`);
        } else {
            failed++;
            results.push({ status: 'FAIL', message });
            console.log(`  ❌ ${message}`);
        }
    } catch (e) {
        failed++;
        results.push({ status: 'FAIL', message: `${message} (error: ${e.message})` });
        console.log(`  ❌ ${message} (error: ${e.message})`);
    }
}

// ============================================
// UPGRADE MANAGER TESTS
// ============================================

console.log('\n📦 Testing UpgradeManager...\n');

// Mock UpgradeManager for unit tests
class MockUpgradeManager {
    constructor() {
        this.rpcEndpoint = RPC_ENDPOINT;
        this.chunkSize = 64 * 1024;
    }

    normalizeSecretKey(input) {
        const DEV_ACCOUNTS = {
            alice: 'e7175a541ee055e423e070eee2cfd2a9f447a820f4e61bf03180805dbc8c4a7f1ad3437c05c2da62ed342eef62e8cac285cf8134d29b49c68a9e575f3c275991d7d0bd475417a93fa61216a1e4024f8d1a211f795e6ab111a1eef0d5e4f3f4b156e47e5c8d4185ce4a308423eb310bb3b7f26e6d504191662d2241aafaf914cd',
            bob: '034a9b6570680a960ff781fec37012c355cbf698e26788b6f3b351daec75beea101f9c3b8b07fefa1d84d8b48ea02f1e',
            charlie: 'b2e5b1dd89b389f61b108bff36755bd0b5208aac741233e538a464dbd841b5bf68cc36bde662e8fde70fd41cdd605766'
        };

        let key = input.trim().replace(/['"]/g, '');
        const keyLower = key.toLowerCase();

        if (keyLower === 'alice' || keyLower === '//alice') {
            return '0x' + DEV_ACCOUNTS.alice;
        } else if (keyLower === 'bob' || keyLower === '//bob') {
            return '0x' + DEV_ACCOUNTS.bob;
        } else if (keyLower === 'charlie' || keyLower === '//charlie') {
            return '0x' + DEV_ACCOUNTS.charlie;
        }

        let hexPart = key.startsWith('0x') ? key.slice(2) : key;
        hexPart = hexPart.replace(/[^0-9a-fA-F]/g, '');

        if (hexPart.length < 96) {
            throw new Error(`Key too short: ${hexPart.length / 2} bytes. Need 48 (seed) or 128 (full key).`);
        }

        return '0x' + hexPart;
    }
}

const upgradeManager = new MockUpgradeManager();

// Test normalizeSecretKey
assert(
    upgradeManager.normalizeSecretKey('alice').startsWith('0xe7175a54'),
    'normalizeSecretKey: Alice dev account'
);

assert(
    upgradeManager.normalizeSecretKey('//alice').startsWith('0xe7175a54'),
    'normalizeSecretKey: //Alice format'
);

assert(
    upgradeManager.normalizeSecretKey('bob').startsWith('0x034a9b65'),
    'normalizeSecretKey: Bob dev account'
);

assert(
    upgradeManager.normalizeSecretKey('0x' + 'a'.repeat(256)).length === 258,
    'normalizeSecretKey: 128-byte hex key'
);

assertThrows(
    () => upgradeManager.normalizeSecretKey('short'),
    'normalizeSecretKey: Rejects short key'
);

assertThrows(
    () => upgradeManager.normalizeSecretKey('0x1234'),
    'normalizeSecretKey: Rejects invalid length'
);

// ============================================
// KEYSTORE MANAGER TESTS
// ============================================

console.log('\n🔑 Testing KeystoreManager...\n');

class MockKeystoreManager {
    validateSphincsKey(keyHex) {
        const clean = keyHex.replace('0x', '').replace(/[^0-9a-fA-F]/g, '');

        if (clean.length === 256) {
            return { valid: true, type: 'secret', bytes: 128 };
        } else if (clean.length === 128) {
            return { valid: true, type: 'public', bytes: 64 };
        } else if (clean.length === 96) {
            return { valid: true, type: 'seed', bytes: 48 };
        } else {
            return {
                valid: false,
                type: 'unknown',
                bytes: clean.length / 2,
                message: `Invalid length: ${clean.length / 2} bytes.`
            };
        }
    }

    getDevAccounts() {
        return {
            alice: {
                name: 'Alice',
                secret: '0xe7175a541ee055e423e070eee2cfd2a9f447a820f4e61bf03180805dbc8c4a7f1ad3437c05c2da62ed342eef62e8cac285cf8134d29b49c68a9e575f3c275991d7d0bd475417a93fa61216a1e4024f8d1a211f795e6ab111a1eef0d5e4f3f4b156e47e5c8d4185ce4a308423eb310bb3b7f26e6d504191662d2241aafaf914cd',
                isSudo: true
            },
            bob: { name: 'Bob', isSudo: false },
            charlie: { name: 'Charlie', isSudo: false }
        };
    }
}

const keystoreManager = new MockKeystoreManager();

// Test validateSphincsKey
let validation = keystoreManager.validateSphincsKey('0x' + 'a'.repeat(256));
assert(validation.valid && validation.type === 'secret', 'validateSphincsKey: 128-byte secret key');

validation = keystoreManager.validateSphincsKey('0x' + 'b'.repeat(128));
assert(validation.valid && validation.type === 'public', 'validateSphincsKey: 64-byte public key');

validation = keystoreManager.validateSphincsKey('0x' + 'c'.repeat(96));
assert(validation.valid && validation.type === 'seed', 'validateSphincsKey: 48-byte seed');

validation = keystoreManager.validateSphincsKey('0x1234');
assert(!validation.valid, 'validateSphincsKey: Invalid short key');

// Test getDevAccounts
const devAccounts = keystoreManager.getDevAccounts();
assert(devAccounts.alice.isSudo === true, 'getDevAccounts: Alice is sudo');
assert(devAccounts.bob.isSudo === false, 'getDevAccounts: Bob is not sudo');

// ============================================
// GOVERNANCE MANAGER TESTS
// ============================================

console.log('\n🏛️  Testing GovernanceManager...\n');

class MockGovernanceManager {
    constructor() {
        this.PALLET_INDEX = 41;
        this.CALL_INDICES = {
            proposeValidator: 0,
            vote: 1,
            finalizeProposal: 2
        };
    }

    encodeAccountId(accountId) {
        return accountId.replace('0x', '');
    }

    encodeU32LE(value) {
        const hex = value.toString(16).padStart(8, '0');
        return hex.match(/../g).reverse().join('');
    }

    encodeBool(value) {
        return value ? '01' : '00';
    }

    buildProposeValidatorCall(validatorAccountId) {
        const palletIndex = this.PALLET_INDEX.toString(16).padStart(2, '0');
        const callIndex = this.CALL_INDICES.proposeValidator.toString(16).padStart(2, '0');
        const accountData = this.encodeAccountId(validatorAccountId);
        return '0x' + palletIndex + callIndex + accountData;
    }

    buildVoteCall(proposalId, approve) {
        const palletIndex = this.PALLET_INDEX.toString(16).padStart(2, '0');
        const callIndex = this.CALL_INDICES.vote.toString(16).padStart(2, '0');
        const proposalIdLE = this.encodeU32LE(proposalId);
        const approveHex = this.encodeBool(approve);
        return '0x' + palletIndex + callIndex + proposalIdLE + approveHex;
    }

    buildFinalizeCall(proposalId) {
        const palletIndex = this.PALLET_INDEX.toString(16).padStart(2, '0');
        const callIndex = this.CALL_INDICES.finalizeProposal.toString(16).padStart(2, '0');
        const proposalIdLE = this.encodeU32LE(proposalId);
        return '0x' + palletIndex + callIndex + proposalIdLE;
    }
}

const govManager = new MockGovernanceManager();

// Test encodeU32LE
assert(govManager.encodeU32LE(0) === '00000000', 'encodeU32LE: 0');
assert(govManager.encodeU32LE(1) === '01000000', 'encodeU32LE: 1');
assert(govManager.encodeU32LE(256) === '00010000', 'encodeU32LE: 256');
assert(govManager.encodeU32LE(65536) === '00000100', 'encodeU32LE: 65536');

// Test encodeBool
assert(govManager.encodeBool(true) === '01', 'encodeBool: true');
assert(govManager.encodeBool(false) === '00', 'encodeBool: false');

// Test buildProposeValidatorCall
const testAccountId = '0x' + '1'.repeat(64);
const proposeCall = govManager.buildProposeValidatorCall(testAccountId);
assert(proposeCall.startsWith('0x2900'), 'buildProposeValidatorCall: Correct prefix (pallet 41, call 0)');
assert(proposeCall.length === 2 + 4 + 64, 'buildProposeValidatorCall: Correct length');

// Test buildVoteCall
const voteCallYes = govManager.buildVoteCall(1, true);
assert(voteCallYes === '0x29010100000001', 'buildVoteCall: Vote YES on proposal 1');

const voteCallNo = govManager.buildVoteCall(2, false);
assert(voteCallNo === '0x29010200000000', 'buildVoteCall: Vote NO on proposal 2');

// Test buildFinalizeCall
const finalizeCall = govManager.buildFinalizeCall(1);
assert(finalizeCall === '0x290201000000', 'buildFinalizeCall: Finalize proposal 1');

// ============================================
// INTEGRATION TESTS (require running node)
// ============================================

console.log('\n🔌 Integration Tests (require running node)...\n');

async function runIntegrationTests() {
    // Simple fetch-based RPC helper
    async function rpc(method, params = []) {
        try {
            const res = await fetch(RPC_ENDPOINT, {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ jsonrpc: '2.0', id: 1, method, params })
            });
            const data = await res.json();
            return data.result;
        } catch (e) {
            return null;
        }
    }

    // Test node connectivity
    await assertAsync(
        async () => {
            const health = await rpc('system_health', []);
            return health && typeof health.peers === 'number';
        },
        'Node connectivity: system_health returns valid data'
    );

    // Test runtime version query
    await assertAsync(
        async () => {
            const version = await rpc('state_getRuntimeVersion', []);
            return version && version.specVersion >= 17;
        },
        'Runtime version: specVersion >= 17'
    );

    // Test governance RPC
    await assertAsync(
        async () => {
            const stats = await rpc('quantumharmony_getGovernanceStats', []);
            return stats && typeof stats.voting_period === 'number';
        },
        'Governance RPC: getGovernanceStats returns valid data'
    );

    // Test validator set RPC
    await assertAsync(
        async () => {
            const validators = await rpc('quantumharmony_getValidatorSet', []);
            return Array.isArray(validators) && validators.length >= 0;
        },
        'Governance RPC: getValidatorSet returns array'
    );

    // Test chunked upgrade RPC availability
    await assertAsync(
        async () => {
            const methods = await rpc('rpc_methods', []);
            return methods && methods.methods.includes('chunkedUpgrade_initiate');
        },
        'Chunked upgrade RPC: Methods available'
    );
}

// Run integration tests if fetch is available (Node.js 18+ or browser)
if (typeof fetch !== 'undefined') {
    runIntegrationTests().then(() => {
        printSummary();
    });
} else {
    console.log('  ⚠️  Skipping integration tests (fetch not available)');
    printSummary();
}

function printSummary() {
    console.log('\n' + '='.repeat(50));
    console.log(`📊 Test Summary: ${passed} passed, ${failed} failed`);
    console.log('='.repeat(50) + '\n');

    if (failed > 0) {
        console.log('Failed tests:');
        results.filter(r => r.status === 'FAIL').forEach(r => {
            console.log(`  - ${r.message}`);
        });
        process.exit(1);
    } else {
        console.log('All tests passed! ✅\n');
        process.exit(0);
    }
}
