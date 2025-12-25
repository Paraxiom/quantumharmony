/**
 * QuantumHarmony Wallet - Popup Script
 *
 * Handles wallet UI, key management, and signing requests.
 * Keys are stored encrypted in browser storage.
 */

// State
let currentAccount = null;
let isUnlocked = false;
let pendingRequests = [];

// Initialize
document.addEventListener('DOMContentLoaded', async () => {
  await checkWalletState();
});

// Check if wallet exists and its state
async function checkWalletState() {
  const data = await chrome.storage.local.get(['accounts', 'isUnlocked', 'currentAccount']);

  if (!data.accounts || Object.keys(data.accounts).length === 0) {
    showView('setup');
  } else if (!data.isUnlocked) {
    showView('unlock');
  } else {
    currentAccount = data.currentAccount;
    showView('main');
    await loadAccountInfo();
    await checkPendingRequests();
  }
}

// Show specific view
function showView(view) {
  document.getElementById('setupView').classList.add('hidden');
  document.getElementById('unlockView').classList.add('hidden');
  document.getElementById('mainView').classList.add('hidden');

  document.getElementById(view + 'View').classList.remove('hidden');
}

// Tab switching
function showTab(tab) {
  document.querySelectorAll('.tab').forEach(t => t.classList.remove('active'));
  event.target.classList.add('active');

  document.getElementById('importTab').classList.add('hidden');
  document.getElementById('createTab').classList.add('hidden');
  document.getElementById(tab + 'Tab').classList.remove('hidden');
}

// Import existing key
async function importKey() {
  const name = document.getElementById('importName').value.trim();
  const key = document.getElementById('importKey').value.trim();
  const password = document.getElementById('importPassword').value;
  const confirmPassword = document.getElementById('importPasswordConfirm').value;

  // Validate
  if (!name) {
    alert('Please enter an account name');
    return;
  }

  if (!key.startsWith('0x') || key.length !== 258) {
    alert('Invalid key format. Expected 128-byte SPHINCS+ key (0x + 256 hex chars)');
    return;
  }

  if (password.length < 8) {
    alert('Password must be at least 8 characters');
    return;
  }

  if (password !== confirmPassword) {
    alert('Passwords do not match');
    return;
  }

  // Derive address from key (simplified - in production use proper derivation)
  const address = await deriveAddress(key);

  // Encrypt key with password
  const encryptedKey = await encryptKey(key, password);

  // Store account
  const accounts = (await chrome.storage.local.get('accounts')).accounts || {};
  accounts[address] = {
    name: name,
    address: address,
    encryptedKey: encryptedKey,
    createdAt: Date.now()
  };

  await chrome.storage.local.set({
    accounts: accounts,
    currentAccount: address,
    isUnlocked: true
  });

  // Store decrypted key in session (memory only)
  await chrome.storage.session.set({
    decryptedKey: key
  });

  currentAccount = address;
  showView('main');
  await loadAccountInfo();
}

// Create new key (placeholder - requires native binary)
async function createKey() {
  alert('Key generation requires the QuantumHarmony node binary.\n\nFor testing, please use the Import tab with a test key.');
}

// Unlock wallet
async function unlock() {
  const password = document.getElementById('unlockPassword').value;

  const data = await chrome.storage.local.get(['accounts', 'currentAccount']);
  const account = data.accounts[data.currentAccount];

  if (!account) {
    alert('No account found');
    return;
  }

  try {
    const decryptedKey = await decryptKey(account.encryptedKey, password);

    // Store in session
    await chrome.storage.session.set({ decryptedKey: decryptedKey });
    await chrome.storage.local.set({ isUnlocked: true });

    currentAccount = data.currentAccount;
    showView('main');
    await loadAccountInfo();
  } catch (e) {
    alert('Incorrect password');
  }
}

// Lock wallet
async function lock() {
  await chrome.storage.session.remove('decryptedKey');
  await chrome.storage.local.set({ isUnlocked: false });
  isUnlocked = false;
  showView('unlock');
}

// Load account info
async function loadAccountInfo() {
  const data = await chrome.storage.local.get(['accounts', 'currentAccount']);
  const account = data.accounts[data.currentAccount];

  if (account) {
    document.getElementById('accountName').textContent = account.name;
    document.getElementById('accountAddress').textContent =
      account.address.slice(0, 8) + '...' + account.address.slice(-4);
  }

  await refreshBalance();
}

// Refresh balance
async function refreshBalance() {
  const balanceEl = document.getElementById('accountBalance');
  balanceEl.textContent = 'Loading...';

  try {
    const response = await fetch(`http://YOUR_NODE_IP:8080/balance?address=${currentAccount}`);
    const data = await response.json();
    balanceEl.textContent = data.balance || '0 QMHY';
  } catch (e) {
    balanceEl.textContent = 'Error';
  }
}

// Connect to current site
async function connect() {
  // Get current tab
  const [tab] = await chrome.tabs.query({ active: true, currentWindow: true });

  // Send connection message to content script
  chrome.tabs.sendMessage(tab.id, {
    type: 'QUANTUM_WALLET_CONNECT',
    address: currentAccount
  });

  document.getElementById('connectionStatus').textContent = 'Connected';
  document.getElementById('connectionStatus').className = 'status status-connected';
}

// Check for pending signing requests
async function checkPendingRequests() {
  const data = await chrome.storage.local.get('pendingRequests');
  pendingRequests = data.pendingRequests || [];

  if (pendingRequests.length > 0) {
    showPendingRequest(pendingRequests[0]);
  }
}

// Show pending request
function showPendingRequest(request) {
  const details = document.getElementById('requestDetails');
  details.innerHTML = `
    <div><strong>Type:</strong> ${request.type}</div>
    <div><strong>From:</strong> ${request.origin}</div>
    <div style="font-size: 10px; margin-top: 5px; word-break: break-all;">
      <strong>Data:</strong> ${JSON.stringify(request.data).slice(0, 100)}...
    </div>
  `;
  document.getElementById('pendingRequest').classList.remove('hidden');
}

// Approve request
async function approveRequest() {
  if (pendingRequests.length === 0) return;

  const request = pendingRequests[0];
  const sessionData = await chrome.storage.session.get('decryptedKey');
  const key = sessionData.decryptedKey;

  if (!key) {
    alert('Wallet is locked');
    return;
  }

  // Sign the request (simplified - in production use proper SPHINCS+ signing)
  const signature = await signData(request.data, key);

  // Send response back
  chrome.runtime.sendMessage({
    type: 'SIGNING_RESPONSE',
    requestId: request.id,
    signature: signature,
    address: currentAccount
  });

  // Remove from pending
  pendingRequests.shift();
  await chrome.storage.local.set({ pendingRequests: pendingRequests });

  document.getElementById('pendingRequest').classList.add('hidden');
}

// Reject request
async function rejectRequest() {
  if (pendingRequests.length === 0) return;

  const request = pendingRequests[0];

  chrome.runtime.sendMessage({
    type: 'SIGNING_RESPONSE',
    requestId: request.id,
    error: 'User rejected'
  });

  pendingRequests.shift();
  await chrome.storage.local.set({ pendingRequests: pendingRequests });
  document.getElementById('pendingRequest').classList.add('hidden');
}

// ============================================================
// CRYPTO UTILITIES
// ============================================================

// Derive address from key (simplified)
async function deriveAddress(secretKey) {
  // In production: properly derive SS58 address from SPHINCS+ public key
  // For now: use a hash-based derivation for testing

  const keyBytes = hexToBytes(secretKey.slice(2));

  // Public key is last 64 bytes of 128-byte secret
  const publicKey = keyBytes.slice(64);

  // Hash public key to get account ID
  const hashBuffer = await crypto.subtle.digest('SHA-256', publicKey);
  const hashArray = new Uint8Array(hashBuffer);

  // Convert to SS58 (simplified - just base58 with prefix)
  // In production: use proper SS58 encoding
  const address = '5' + bytesToBase58(hashArray).slice(0, 46);

  return address;
}

// Encrypt key with password
async function encryptKey(key, password) {
  const encoder = new TextEncoder();
  const keyData = encoder.encode(key);

  // Derive encryption key from password
  const passwordKey = await crypto.subtle.importKey(
    'raw',
    encoder.encode(password),
    'PBKDF2',
    false,
    ['deriveBits', 'deriveKey']
  );

  const salt = crypto.getRandomValues(new Uint8Array(16));

  const aesKey = await crypto.subtle.deriveKey(
    {
      name: 'PBKDF2',
      salt: salt,
      iterations: 100000,
      hash: 'SHA-256'
    },
    passwordKey,
    { name: 'AES-GCM', length: 256 },
    false,
    ['encrypt']
  );

  const iv = crypto.getRandomValues(new Uint8Array(12));
  const encrypted = await crypto.subtle.encrypt(
    { name: 'AES-GCM', iv: iv },
    aesKey,
    keyData
  );

  // Combine salt + iv + encrypted
  const result = new Uint8Array(salt.length + iv.length + encrypted.byteLength);
  result.set(salt, 0);
  result.set(iv, salt.length);
  result.set(new Uint8Array(encrypted), salt.length + iv.length);

  return bytesToHex(result);
}

// Decrypt key with password
async function decryptKey(encryptedHex, password) {
  const encoder = new TextEncoder();
  const data = hexToBytes(encryptedHex);

  const salt = data.slice(0, 16);
  const iv = data.slice(16, 28);
  const encrypted = data.slice(28);

  const passwordKey = await crypto.subtle.importKey(
    'raw',
    encoder.encode(password),
    'PBKDF2',
    false,
    ['deriveBits', 'deriveKey']
  );

  const aesKey = await crypto.subtle.deriveKey(
    {
      name: 'PBKDF2',
      salt: salt,
      iterations: 100000,
      hash: 'SHA-256'
    },
    passwordKey,
    { name: 'AES-GCM', length: 256 },
    false,
    ['decrypt']
  );

  const decrypted = await crypto.subtle.decrypt(
    { name: 'AES-GCM', iv: iv },
    aesKey,
    encrypted
  );

  return new TextDecoder().decode(decrypted);
}

// Sign data (placeholder - real SPHINCS+ signing would need WASM)
async function signData(data, key) {
  // In production: use SPHINCS+ WASM module for actual signing
  // For now: return a placeholder that the server can recognize

  const encoder = new TextEncoder();
  const dataBytes = encoder.encode(JSON.stringify(data));

  // Create a deterministic "signature" for testing
  const combined = new Uint8Array(dataBytes.length + 32);
  combined.set(dataBytes, 0);
  combined.set(hexToBytes(key.slice(2, 66)), dataBytes.length);

  const hash = await crypto.subtle.digest('SHA-256', combined);
  return '0x' + bytesToHex(new Uint8Array(hash));
}

// Utility: hex to bytes
function hexToBytes(hex) {
  const bytes = new Uint8Array(hex.length / 2);
  for (let i = 0; i < hex.length; i += 2) {
    bytes[i / 2] = parseInt(hex.substr(i, 2), 16);
  }
  return bytes;
}

// Utility: bytes to hex
function bytesToHex(bytes) {
  return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
}

// Utility: bytes to base58 (simplified)
function bytesToBase58(bytes) {
  const ALPHABET = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz';
  let num = BigInt('0x' + bytesToHex(bytes));
  let result = '';
  while (num > 0) {
    result = ALPHABET[Number(num % 58n)] + result;
    num = num / 58n;
  }
  return result;
}
