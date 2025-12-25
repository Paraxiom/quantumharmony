#!/usr/bin/env node

// Simple wallet server for Drista
// Run with: node wallet-server.js
// Then open browser to: http://localhost:3000

const http = require('http');
const { ApiPromise, WsProvider } = require('@polkadot/api');
const { Keyring } = require('@polkadot/keyring');
const { cryptoWaitReady } = require('@polkadot/util-crypto');

const KIRQ_ENDPOINT = 'ws://192.168.0.154:9944';
let api = null;
let keyring = null;

// Initialize connection
async function init() {
    console.log('Connecting to KIRQ VM at 192.168.0.154...');
    await cryptoWaitReady();

    const provider = new WsProvider(KIRQ_ENDPOINT);
    api = await ApiPromise.create({ provider });

    keyring = new Keyring({ type: 'sr25519' });

    const chain = await api.rpc.system.chain();
    console.log('Connected to:', chain.toString());
}

// HTML interface
const html = `<!DOCTYPE html>
<html>
<head>
    <title>Drista Wallet</title>
    <style>
        body {
            background: #0a0a0a;
            color: #0ff;
            font-family: 'Courier New', monospace;
            padding: 20px;
        }
        .container {
            max-width: 800px;
            margin: 0 auto;
            background: rgba(0,0,0,0.9);
            padding: 30px;
            border: 1px solid #0ff;
            border-radius: 10px;
        }
        h1 { text-align: center; color: #0ff; }
        button {
            background: #0066aa;
            color: white;
            border: 1px solid #0ff;
            padding: 10px 20px;
            margin: 5px;
            cursor: pointer;
            border-radius: 5px;
        }
        button:hover { background: #0088cc; }
        .info-box {
            background: rgba(0,50,50,0.3);
            padding: 15px;
            margin: 10px 0;
            border-radius: 5px;
        }
        #result {
            background: black;
            color: #0f0;
            padding: 10px;
            margin: 10px 0;
            min-height: 100px;
            border: 1px solid #0f0;
            font-family: monospace;
            white-space: pre;
        }
    </style>
</head>
<body>
    <div class="container">
        <h1>🔐 Drista Quantum Wallet</h1>

        <div class="info-box">
            <h3>Quick Actions</h3>
            <button onclick="getStatus()">📊 Get Status</button>
            <button onclick="getBalances()">💰 Get Balances</button>
            <button onclick="transfer()">💸 Transfer 1 UNIT</button>
            <button onclick="checkSudo()">🔑 Check Sudo</button>
            <button onclick="getRuntimeInfo()">ℹ️ Runtime Info</button>
        </div>

        <div class="info-box">
            <h3>Result:</h3>
            <div id="result">Click a button to perform an action...</div>
        </div>
    </div>

    <script>
        async function apiCall(action) {
            const result = document.getElementById('result');
            result.textContent = 'Loading...';

            try {
                const response = await fetch('/api/' + action);
                const data = await response.json();
                result.textContent = JSON.stringify(data, null, 2);
            } catch (error) {
                result.textContent = 'Error: ' + error.message;
            }
        }

        function getStatus() { apiCall('status'); }
        function getBalances() { apiCall('balances'); }
        function transfer() { apiCall('transfer'); }
        function checkSudo() { apiCall('sudo'); }
        function getRuntimeInfo() { apiCall('runtime'); }
    </script>
</body>
</html>`;

// API handlers
async function handleAPI(action) {
    if (!api) {
        return { error: 'Not connected to blockchain' };
    }

    const alice = keyring.addFromUri('//Alice');
    const bob = keyring.addFromUri('//Bob');

    switch(action) {
        case 'status':
            const [chain, nodeName, nodeVersion] = await Promise.all([
                api.rpc.system.chain(),
                api.rpc.system.name(),
                api.rpc.system.version()
            ]);
            const header = await api.rpc.chain.getHeader();
            return {
                chain: chain.toString(),
                node: nodeName.toString(),
                version: nodeVersion.toString(),
                block: header.number.toHuman()
            };

        case 'balances':
            const [aliceAccount, bobAccount] = await Promise.all([
                api.query.system.account(alice.address),
                api.query.system.account(bob.address)
            ]);
            return {
                alice: {
                    address: alice.address,
                    balance: aliceAccount.data.free.toHuman()
                },
                bob: {
                    address: bob.address,
                    balance: bobAccount.data.free.toHuman()
                }
            };

        case 'transfer':
            const transfer = api.tx.balances.transferKeepAlive(bob.address, 1000000000000);

            return new Promise((resolve) => {
                transfer.signAndSend(alice, ({ status }) => {
                    if (status.isInBlock) {
                        console.log('Transfer in block:', status.asInBlock.toString());
                    }
                    if (status.isFinalized) {
                        resolve({
                            success: true,
                            message: 'Transfer of 1 UNIT from Alice to Bob completed',
                            block: status.asFinalized.toString()
                        });
                    }
                });
            });

        case 'sudo':
            try {
                const sudoKey = await api.query.sudo.key();
                return {
                    sudoKey: sudoKey.toString(),
                    aliceAddress: alice.address,
                    hasSudo: sudoKey.toString() === alice.address
                };
            } catch (e) {
                return { error: 'Sudo pallet not available' };
            }

        case 'runtime':
            const version = await api.rpc.state.getRuntimeVersion();
            return {
                specName: version.specName.toString(),
                specVersion: version.specVersion.toNumber(),
                implVersion: version.implVersion.toNumber()
            };

        default:
            return { error: 'Unknown action' };
    }
}

// Create server
const server = http.createServer(async (req, res) => {
    // CORS headers
    res.setHeader('Access-Control-Allow-Origin', '*');

    if (req.url === '/') {
        res.writeHead(200, { 'Content-Type': 'text/html' });
        res.end(html);
    } else if (req.url.startsWith('/api/')) {
        const action = req.url.replace('/api/', '');

        try {
            const result = await handleAPI(action);
            res.writeHead(200, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify(result));
        } catch (error) {
            res.writeHead(500, { 'Content-Type': 'application/json' });
            res.end(JSON.stringify({ error: error.message }));
        }
    } else {
        res.writeHead(404);
        res.end('Not found');
    }
});

// Start server
async function start() {
    try {
        await init();

        server.listen(3000, () => {
            console.log('');
            console.log('═══════════════════════════════════════════════════════════');
            console.log('   Drista Wallet Server Running');
            console.log('═══════════════════════════════════════════════════════════');
            console.log('');
            console.log('   Open your browser to: http://localhost:3000');
            console.log('');
            console.log('   Connected to KIRQ VM at 192.168.0.154');
            console.log('');
            console.log('   Press Ctrl+C to stop');
            console.log('═══════════════════════════════════════════════════════════');
        });
    } catch (error) {
        console.error('Failed to start:', error);
        process.exit(1);
    }
}

start();