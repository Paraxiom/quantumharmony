/**
 * QuantumHarmony Keystore Manager
 * Handles key management via RPC methods
 */

class KeystoreManager {
    constructor(rpcEndpoint = 'http://127.0.0.1:9944') {
        this.rpcEndpoint = rpcEndpoint;
        this.cachedKeys = [];
    }

    async rpc(method, params = []) {
        const res = await fetch(this.rpcEndpoint, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({ jsonrpc: '2.0', id: Date.now(), method, params })
        });
        const data = await res.json();
        if (data.error) {
            throw new Error(data.error.message || JSON.stringify(data.error));
        }
        return data.result;
    }

    /**
     * Check if node has keys in keystore
     * Uses author_hasKey RPC
     */
    async hasKey(publicKey, keyType = 'aura') {
        try {
            const result = await this.rpc('author_hasKey', [publicKey, keyType]);
            return result === true;
        } catch (e) {
            console.error('hasKey error:', e);
            return false;
        }
    }

    /**
     * Check if node has any session keys
     */
    async hasSessionKeys(keys) {
        try {
            const result = await this.rpc('author_hasSessionKeys', [keys]);
            return result === true;
        } catch (e) {
            console.error('hasSessionKeys error:', e);
            return false;
        }
    }

    /**
     * Insert a key into the keystore
     * Uses author_insertKey RPC
     * @param {string} keyType - Key type (e.g., 'aura', 'gran')
     * @param {string} suri - Secret URI (seed phrase or hex)
     * @param {string} publicKey - Public key (hex)
     */
    async insertKey(keyType, suri, publicKey) {
        try {
            await this.rpc('author_insertKey', [keyType, suri, publicKey]);
            return { success: true, message: 'Key inserted successfully' };
        } catch (e) {
            return { success: false, message: e.message };
        }
    }

    /**
     * Rotate session keys
     * Generates new session keys and returns the encoded public keys
     */
    async rotateKeys() {
        try {
            const result = await this.rpc('author_rotateKeys', []);
            return { success: true, keys: result };
        } catch (e) {
            return { success: false, message: e.message };
        }
    }

    /**
     * Get pending extrinsics count (as a health indicator)
     */
    async getPendingExtrinsics() {
        try {
            const result = await this.rpc('author_pendingExtrinsics', []);
            return result.length;
        } catch (e) {
            return -1;
        }
    }

    /**
     * Derive account ID from SPHINCS+ public key
     * Uses Keccak-256 hash (matching the runtime implementation)
     */
    deriveAccountId(publicKeyHex) {
        // This would need a keccak256 implementation
        // For now, return the first 32 bytes as a placeholder
        const clean = publicKeyHex.replace('0x', '');
        return '0x' + clean.substring(0, 64);
    }

    /**
     * Validate SPHINCS+ key format
     */
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
                message: `Invalid length: ${clean.length / 2} bytes. Expected 128 (secret), 64 (public), or 48 (seed).`
            };
        }
    }

    /**
     * Get dev account info
     */
    getDevAccounts() {
        return {
            alice: {
                name: 'Alice',
                secret: '0xe7175a541ee055e423e070eee2cfd2a9f447a820f4e61bf03180805dbc8c4a7f1ad3437c05c2da62ed342eef62e8cac285cf8134d29b49c68a9e575f3c275991d7d0bd475417a93fa61216a1e4024f8d1a211f795e6ab111a1eef0d5e4f3f4b156e47e5c8d4185ce4a308423eb310bb3b7f26e6d504191662d2241aafaf914cd',
                public: '0xd7d0bd475417a93fa61216a1e4024f8d1a211f795e6ab111a1eef0d5e4f3f4b156e47e5c8d4185ce4a308423eb310bb3b7f26e6d504191662d2241aafaf914cd',
                accountId: '0xe40ec85c92436dda3961649a53a4d2e41b15748c8f9f7f5b8d37e6e90f187700',
                isSudo: true
            },
            bob: {
                name: 'Bob',
                seed: '0x034a9b6570680a960ff781fec37012c355cbf698e26788b6f3b351daec75beea101f9c3b8b07fefa1d84d8b48ea02f1e',
                isSudo: false
            },
            charlie: {
                name: 'Charlie',
                seed: '0xb2e5b1dd89b389f61b108bff36755bd0b5208aac741233e538a464dbd841b5bf68cc36bde662e8fde70fd41cdd605766',
                isSudo: false
            }
        };
    }

    /**
     * Check if a key matches the sudo account
     */
    async isSudoKey(publicKeyHex) {
        const sudoAccountId = '0xe40ec85c92436dda3961649a53a4d2e41b15748c8f9f7f5b8d37e6e90f187700';
        // Query the sudo.key storage to verify
        try {
            const sudoKey = await this.rpc('state_getStorage', [
                '0x5c0d1176a568c1f92944340dbfed9e9c530ebca703c85910e7164cb7d1c9e47b' // twox128("Sudo") + twox128("Key")
            ]);
            return sudoKey === publicKeyHex || sudoKey?.includes(publicKeyHex.replace('0x', ''));
        } catch (e) {
            // Fallback to known sudo account
            const derived = this.deriveAccountId(publicKeyHex);
            return derived === sudoAccountId;
        }
    }
}

// Export for use in browser and Node.js
if (typeof module !== 'undefined' && module.exports) {
    module.exports = { KeystoreManager };
}
if (typeof window !== 'undefined') {
    window.KeystoreManager = KeystoreManager;
}
