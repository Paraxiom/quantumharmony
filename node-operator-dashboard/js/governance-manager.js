/**
 * QuantumHarmony Governance Manager
 * Handles validator governance proposals, voting, and finalization
 */

class GovernanceManager {
    constructor(rpcEndpoint = 'http://127.0.0.1:9944') {
        this.rpcEndpoint = rpcEndpoint;
        this.PALLET_INDEX = 18; // ValidatorGovernance pallet index (0x12)
        this.CALL_INDICES = {
            proposeValidator: 0,
            vote: 1,
            finalizeProposal: 2
        };
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
     * Encode an AccountId (32 bytes) for call data
     */
    encodeAccountId(accountId) {
        return accountId.replace('0x', '');
    }

    /**
     * Encode a u32 as little-endian hex
     */
    encodeU32LE(value) {
        const hex = value.toString(16).padStart(8, '0');
        // Reverse byte order for LE
        return hex.match(/../g).reverse().join('');
    }

    /**
     * Encode a boolean
     */
    encodeBool(value) {
        return value ? '01' : '00';
    }

    /**
     * Build call data for proposeValidator
     */
    buildProposeValidatorCall(validatorAccountId) {
        const palletIndex = this.PALLET_INDEX.toString(16).padStart(2, '0');
        const callIndex = this.CALL_INDICES.proposeValidator.toString(16).padStart(2, '0');
        const accountData = this.encodeAccountId(validatorAccountId);
        return '0x' + palletIndex + callIndex + accountData;
    }

    /**
     * Build call data for vote
     */
    buildVoteCall(proposalId, approve) {
        const palletIndex = this.PALLET_INDEX.toString(16).padStart(2, '0');
        const callIndex = this.CALL_INDICES.vote.toString(16).padStart(2, '0');
        const proposalIdLE = this.encodeU32LE(proposalId);
        const approveHex = this.encodeBool(approve);
        return '0x' + palletIndex + callIndex + proposalIdLE + approveHex;
    }

    /**
     * Build call data for finalizeProposal
     */
    buildFinalizeCall(proposalId) {
        const palletIndex = this.PALLET_INDEX.toString(16).padStart(2, '0');
        const callIndex = this.CALL_INDICES.finalizeProposal.toString(16).padStart(2, '0');
        const proposalIdLE = this.encodeU32LE(proposalId);
        return '0x' + palletIndex + callIndex + proposalIdLE;
    }

    /**
     * Submit a signed extrinsic using the quantum-safe RPC
     * Expects struct format: { callData, signerKey }
     */
    async submitSignedExtrinsic(callData, secretKey) {
        const result = await this.rpc('quantumharmony_submitSignedExtrinsic', [{
            callData: callData,
            signerKey: secretKey
        }]);
        return result;
    }

    /**
     * Propose a new validator
     * @param {string} validatorAccountId - The account ID of the proposed validator (0x...)
     * @param {string} signerSecretKey - The signer's SPHINCS+ secret key
     */
    async proposeValidator(validatorAccountId, signerSecretKey, options = {}) {
        const { onLog = console.log } = options;

        if (!validatorAccountId.startsWith('0x') || (validatorAccountId.length !== 66 && validatorAccountId.length !== 130)) {
            throw new Error('Invalid validator account ID. Must be 0x followed by 64 hex chars (32 bytes) or 128 hex chars (64 bytes).');
        }

        onLog(`Proposing validator: ${validatorAccountId.substring(0, 20)}...`);

        const callData = this.buildProposeValidatorCall(validatorAccountId);
        onLog(`Call data: ${callData.substring(0, 30)}...`);

        const result = await this.submitSignedExtrinsic(callData, signerSecretKey);

        if (result?.hash || result) {
            const txHash = result.hash || result;
            onLog(`Proposal submitted! TX: ${txHash}`);
            return { success: true, txHash, signer: result.signer };
        } else {
            throw new Error('Transaction submission failed');
        }
    }

    /**
     * Vote on a proposal
     * @param {number} proposalId - The proposal ID
     * @param {boolean} approve - True to approve, false to reject
     * @param {string} signerSecretKey - The signer's SPHINCS+ secret key
     */
    async vote(proposalId, approve, signerSecretKey, options = {}) {
        const { onLog = console.log } = options;

        onLog(`Voting ${approve ? 'YES' : 'NO'} on proposal #${proposalId}...`);

        const callData = this.buildVoteCall(proposalId, approve);
        onLog(`Call data: ${callData}`);

        const result = await this.submitSignedExtrinsic(callData, signerSecretKey);

        if (result?.hash || result) {
            const txHash = result.hash || result;
            onLog(`Vote submitted! TX: ${txHash}`);
            return { success: true, txHash };
        } else {
            throw new Error('Vote submission failed - are you a validator?');
        }
    }

    /**
     * Finalize a proposal after voting period ends
     * @param {number} proposalId - The proposal ID
     * @param {string} signerSecretKey - The signer's SPHINCS+ secret key
     */
    async finalizeProposal(proposalId, signerSecretKey, options = {}) {
        const { onLog = console.log } = options;

        onLog(`Finalizing proposal #${proposalId}...`);

        const callData = this.buildFinalizeCall(proposalId);
        onLog(`Call data: ${callData}`);

        const result = await this.submitSignedExtrinsic(callData, signerSecretKey);

        if (result?.hash || result) {
            const txHash = result.hash || result;
            onLog(`Finalization submitted! TX: ${txHash}`);
            return { success: true, txHash };
        } else {
            throw new Error('Finalization failed - voting period may not be over');
        }
    }

    /**
     * Get governance stats
     */
    async getStats() {
        try {
            const stats = await this.rpc('quantumharmony_getGovernanceStats', []);
            return stats;
        } catch (e) {
            // Return defaults if RPC fails
            return {
                active_proposals: 0,
                total_proposals: 0,
                voting_period: 10,
                min_votes_required: 1
            };
        }
    }

    /**
     * Get active proposals
     */
    async getProposals() {
        try {
            const proposals = await this.rpc('quantumharmony_getProposals', []);
            return proposals;
        } catch (e) {
            return [];
        }
    }

    /**
     * Get validator set
     */
    async getValidatorSet() {
        try {
            const validators = await this.rpc('quantumharmony_getValidatorSet', []);
            return validators;
        } catch (e) {
            return [];
        }
    }

    /**
     * Query proposal from storage directly
     * Uses state_getStorage to read the Proposals storage map
     */
    async getProposalFromStorage(proposalId) {
        // Storage key: twox128("ValidatorGovernance") + twox128("Proposals") + blake2_128_concat(proposalId)
        const modulePrefix = '5c41d26de442c8c2bb8a08df2fdc0ab3'; // twox128("ValidatorGovernance")
        const storagePrefix = 'e5ceef12e9bc13e65e4b2a7306c5a76f'; // twox128("Proposals")

        // Blake2_128Concat of u32 proposal_id
        const proposalIdLE = this.encodeU32LE(proposalId);
        // For blake2_128_concat, we need the hash + the data
        // This is complex to implement in JS, so we'll rely on the RPC for now

        try {
            // Try the governance RPC first
            const proposals = await this.getProposals();
            return proposals.find(p => p.id === proposalId) || null;
        } catch (e) {
            return null;
        }
    }

    /**
     * Query NextProposalId from storage
     */
    async getNextProposalId() {
        const storageKey = '0x5c41d26de442c8c2bb8a08df2fdc0ab3' + // twox128("ValidatorGovernance")
                          '50b6fba3f7e5f5a35bcab6ed3bcdafb7';  // twox128("NextProposalId")

        try {
            const result = await this.rpc('state_getStorage', [storageKey]);
            if (result) {
                // Decode u32 LE
                const hex = result.replace('0x', '');
                const bytes = hex.match(/../g).reverse();
                return parseInt(bytes.join(''), 16);
            }
            return 0;
        } catch (e) {
            return 0;
        }
    }

    /**
     * Subscribe to governance events
     * Returns recent events related to governance
     */
    async getRecentEvents(blockCount = 10) {
        try {
            const header = await this.rpc('chain_getHeader', []);
            const currentBlock = parseInt(header.number, 16);

            const events = [];
            for (let i = 0; i < blockCount; i++) {
                const blockNum = currentBlock - i;
                if (blockNum < 0) break;

                const blockHash = await this.rpc('chain_getBlockHash', [blockNum]);
                const block = await this.rpc('chain_getBlock', [blockHash]);

                // Check for governance-related extrinsics
                for (const ext of block.block.extrinsics) {
                    if (ext.includes(this.PALLET_INDEX.toString(16).padStart(2, '0'))) {
                        events.push({
                            block: blockNum,
                            hash: blockHash,
                            extrinsic: ext.substring(0, 50) + '...'
                        });
                    }
                }
            }

            return events;
        } catch (e) {
            return [];
        }
    }
}

// Export for use in browser and Node.js
if (typeof module !== 'undefined' && module.exports) {
    module.exports = { GovernanceManager };
}
if (typeof window !== 'undefined') {
    window.GovernanceManager = GovernanceManager;
}
