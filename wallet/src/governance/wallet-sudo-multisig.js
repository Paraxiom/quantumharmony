#!/usr/bin/env node

const { ApiPromise, WsProvider } = require('@polkadot/api');
const { Keyring } = require('@polkadot/keyring');
const { cryptoWaitReady, encodeMultiAddress } = require('@polkadot/util-crypto');
const chalk = require('chalk');
const fs = require('fs').promises;
const path = require('path');
const readline = require('readline');

// Sudo operations
class SudoManager {
  constructor(api) {
    this.api = api;
  }

  async getSudoKey() {
    try {
      const key = await this.api.query.sudo.key();
      return key.toString();
    } catch (e) {
      throw new Error('Sudo pallet not available');
    }
  }

  async executeCall(sudoAccount, call) {
    const sudoCall = this.api.tx.sudo.sudo(call);
    return await sudoCall.signAndSend(sudoAccount);
  }

  async executeUncheckedWeight(sudoAccount, call, weight = { refTime: 1_000_000_000, proofSize: 0 }) {
    const sudoCall = this.api.tx.sudo.sudoUncheckedWeight(call, weight);
    return await sudoCall.signAndSend(sudoAccount);
  }

  async setKey(sudoAccount, newKey) {
    const call = this.api.tx.sudo.setKey(newKey);
    return await this.executeCall(sudoAccount, call);
  }

  async submitRuntimeUpgrade(sudoAccount, wasmPath) {
    const wasm = await fs.readFile(wasmPath);
    const call = this.api.tx.system.setCode(wasm);
    
    console.log(chalk.yellow(`Runtime upgrade size: ${wasm.length} bytes`));
    
    return await this.executeUncheckedWeight(sudoAccount, call, {
      refTime: 2_000_000_000,
      proofSize: wasm.length
    });
  }
}

// Multisig operations
class MultisigManager {
  constructor(api) {
    this.api = api;
  }

  createMultisigAddress(addresses, threshold) {
    return encodeMultiAddress(addresses, threshold);
  }

  async proposeCall(signerAccount, otherSigners, threshold, call, timepoint = null) {
    const callHash = call.method.hash;
    const multisigCall = this.api.tx.multisig.asMulti(
      threshold,
      otherSigners,
      timepoint,
      call,
      0
    );
    
    return {
      hash: await multisigCall.signAndSend(signerAccount),
      callHash: callHash.toHex()
    };
  }

  async approveCall(signerAccount, otherSigners, threshold, callHash, timepoint, maxWeight) {
    const approveCall = this.api.tx.multisig.approveAsMulti(
      threshold,
      otherSigners,
      timepoint,
      callHash,
      maxWeight
    );
    
    return await approveCall.signAndSend(signerAccount);
  }

  async cancelCall(signerAccount, otherSigners, threshold, timepoint, callHash) {
    const cancelCall = this.api.tx.multisig.cancelAsMulti(
      threshold,
      otherSigners,
      timepoint,
      callHash
    );
    
    return await cancelCall.signAndSend(signerAccount);
  }

  async getMultisigInfo(multisigAddress, callHash) {
    const info = await this.api.query.multisig.multisigs(multisigAddress, callHash);
    return info.toHuman();
  }
}

// Enhanced wallet with sudo and multisig
class QuantumWalletEnhanced {
  constructor() {
    this.api = null;
    this.keyring = null;
    this.sudo = null;
    this.multisig = null;
  }

  async connect(endpoint = 'ws://localhost:9944') {
    console.log(chalk.cyan('🔗 Connecting to Quantum Harmony blockchain...'));
    
    const provider = new WsProvider(endpoint);
    this.api = await ApiPromise.create({ provider });
    await cryptoWaitReady();
    
    this.keyring = new Keyring({ type: 'sr25519' });
    this.sudo = new SudoManager(this.api);
    this.multisig = new MultisigManager(this.api);
    
    const chain = await this.api.rpc.system.chain();
    console.log(chalk.green(`✅ Connected to ${chain}`));
    
    // Check if sudo is available
    try {
      const sudoKey = await this.sudo.getSudoKey();
      console.log(chalk.yellow(`🔑 Sudo key: ${sudoKey}`));
    } catch (e) {
      console.log(chalk.red('❌ Sudo pallet not available'));
    }
    
    // Check if multisig is available
    if (this.api.tx.multisig) {
      console.log(chalk.green('✅ Multisig pallet available'));
    } else {
      console.log(chalk.red('❌ Multisig pallet not available'));
    }
  }

  async loadAccount(seedOrMnemonic) {
    if (seedOrMnemonic.includes(' ')) {
      return this.keyring.addFromMnemonic(seedOrMnemonic);
    } else {
      return this.keyring.addFromUri(seedOrMnemonic);
    }
  }

  async testSudoOperations() {
    console.log(chalk.yellow('\n🧪 Testing Sudo Operations\n'));
    
    const alice = this.keyring.addFromUri('//Alice');
    
    try {
      // Check sudo key
      const sudoKey = await this.sudo.getSudoKey();
      console.log(chalk.green(`✅ Current sudo key: ${sudoKey}`));
      
      if (sudoKey === alice.address) {
        console.log(chalk.green('✅ Alice has sudo access'));
        
        // Test a simple sudo call (force transfer)
        const bob = this.keyring.addFromUri('//Bob');
        const charlie = this.keyring.addFromUri('//Charlie');
        
        const forceTransfer = this.api.tx.balances.forceTransfer(
          bob.address,
          charlie.address,
          1_000_000_000_000n
        );
        
        console.log(chalk.cyan('📤 Executing sudo force transfer...'));
        const hash = await this.sudo.executeCall(alice, forceTransfer);
        console.log(chalk.green(`✅ Sudo call executed: ${hash.toHex()}`));
      } else {
        console.log(chalk.yellow('⚠️  Alice is not the sudo key'));
      }
    } catch (error) {
      console.log(chalk.red(`❌ Sudo test failed: ${error.message}`));
    }
  }

  async testMultisigOperations() {
    console.log(chalk.yellow('\n🧪 Testing Multisig Operations\n'));
    
    const alice = this.keyring.addFromUri('//Alice');
    const bob = this.keyring.addFromUri('//Bob');
    const charlie = this.keyring.addFromUri('//Charlie');
    
    try {
      // Create 2-of-3 multisig
      const threshold = 2;
      const signers = [alice.address, bob.address, charlie.address];
      const multisigAddress = this.multisig.createMultisigAddress(signers, threshold);
      
      console.log(chalk.green(`✅ Created 2-of-3 multisig: ${multisigAddress}`));
      
      // Fund the multisig
      console.log(chalk.cyan('💰 Funding multisig account...'));
      const fundTx = this.api.tx.balances.transferAllowDeath(
        multisigAddress,
        10_000_000_000_000n
      );
      await fundTx.signAndSend(alice);
      
      // Create a transfer from multisig
      const dave = this.keyring.addFromUri('//Dave');
      const multisigTransfer = this.api.tx.balances.transferAllowDeath(
        dave.address,
        1_000_000_000_000n
      );
      
      // Alice proposes
      console.log(chalk.cyan('📝 Alice proposing multisig transfer...'));
      const otherSigners = [bob.address, charlie.address].sort();
      const { hash, callHash } = await this.multisig.proposeCall(
        alice,
        otherSigners,
        threshold,
        multisigTransfer
      );
      
      console.log(chalk.green(`✅ Proposal submitted: ${hash}`));
      console.log(chalk.gray(`   Call hash: ${callHash}`));
      
      // Get timepoint from events
      const events = await new Promise((resolve) => {
        this.api.query.system.events((events) => {
          const multisigEvent = events.find(({ event }) => 
            this.api.events.multisig.NewMultisig.is(event)
          );
          if (multisigEvent) {
            resolve(multisigEvent);
          }
        });
      });
      
      const timepoint = {
        height: events.event.data[3].toNumber(),
        index: events.event.data[4].toNumber()
      };
      
      console.log(chalk.gray(`   Timepoint: ${JSON.stringify(timepoint)}`));
      
      // Bob approves and executes
      console.log(chalk.cyan('✅ Bob approving and executing...'));
      const approveHash = await this.multisig.approveCall(
        bob,
        [alice.address, charlie.address].sort(),
        threshold,
        callHash,
        timepoint,
        { refTime: 1_000_000_000, proofSize: 0 }
      );
      
      console.log(chalk.green(`✅ Multisig executed: ${approveHash}`));
      
    } catch (error) {
      console.log(chalk.red(`❌ Multisig test failed: ${error.message}`));
    }
  }

  async prepareRuntimeUpgrade(wasmPath) {
    console.log(chalk.yellow('\n🚀 Preparing Runtime Upgrade\n'));
    
    const alice = this.keyring.addFromUri('//Alice');
    
    try {
      // Check if Alice has sudo
      const sudoKey = await this.sudo.getSudoKey();
      if (sudoKey !== alice.address) {
        throw new Error('Alice is not the sudo key');
      }
      
      // Submit runtime upgrade
      console.log(chalk.cyan('📤 Submitting runtime upgrade...'));
      const hash = await this.sudo.submitRuntimeUpgrade(alice, wasmPath);
      console.log(chalk.green(`✅ Runtime upgrade submitted: ${hash.toHex()}`));
      
      // Monitor for upgrade
      console.log(chalk.cyan('⏳ Waiting for runtime upgrade...'));
      
      const unsubscribe = await this.api.rpc.state.subscribeRuntimeVersion((version) => {
        console.log(chalk.green(`✅ Runtime upgraded to version: ${version.specVersion.toNumber()}`));
        unsubscribe();
      });
      
    } catch (error) {
      console.log(chalk.red(`❌ Runtime upgrade failed: ${error.message}`));
    }
  }

  async disconnect() {
    if (this.api) {
      await this.api.disconnect();
    }
  }
}

// CLI Interface
async function main() {
  const wallet = new QuantumWalletEnhanced();
  
  try {
    await wallet.connect();
    
    const rl = readline.createInterface({
      input: process.stdin,
      output: process.stdout
    });
    
    const question = (query) => new Promise((resolve) => rl.question(query, resolve));
    
    while (true) {
      console.log(chalk.yellow('\n📋 Quantum Wallet - Sudo & Multisig Menu'));
      console.log('1. Test sudo operations');
      console.log('2. Test multisig operations');
      console.log('3. Check sudo key');
      console.log('4. Create multisig address');
      console.log('5. Prepare runtime upgrade');
      console.log('6. Exit');
      
      const choice = await question('\nSelect option: ');
      
      switch (choice) {
        case '1':
          await wallet.testSudoOperations();
          break;
          
        case '2':
          await wallet.testMultisigOperations();
          break;
          
        case '3':
          try {
            const key = await wallet.sudo.getSudoKey();
            console.log(chalk.green(`\nSudo key: ${key}`));
          } catch (e) {
            console.log(chalk.red('\nSudo pallet not available'));
          }
          break;
          
        case '4':
          const addresses = await question('Enter addresses (comma-separated): ');
          const threshold = await question('Enter threshold: ');
          const multisig = wallet.multisig.createMultisigAddress(
            addresses.split(',').map(a => a.trim()),
            parseInt(threshold)
          );
          console.log(chalk.green(`\nMultisig address: ${multisig}`));
          break;
          
        case '5':
          const wasmPath = await question('Enter WASM file path: ');
          await wallet.prepareRuntimeUpgrade(wasmPath);
          break;
          
        case '6':
          rl.close();
          await wallet.disconnect();
          return;
          
        default:
          console.log(chalk.red('Invalid option'));
      }
    }
  } catch (error) {
    console.error(chalk.red('Error:'), error.message);
  }
}

// Export for use as module
module.exports = { SudoManager, MultisigManager, QuantumWalletEnhanced };

// Run if called directly
if (require.main === module) {
  main().catch(console.error);
}