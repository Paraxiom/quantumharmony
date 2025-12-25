/**
 * QuantumHarmony Wallet - Background Service Worker
 *
 * Handles communication between content scripts and popup.
 * Manages signing requests queue.
 */

// Listen for messages from content scripts
chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  console.log('[QH Wallet] Background received:', message.type);

  switch (message.type) {
    case 'SIGNING_REQUEST':
      handleSigningRequest(message, sender);
      break;

    case 'SIGNING_RESPONSE':
      handleSigningResponse(message);
      break;

    case 'CHECK_CONNECTION':
      checkConnection(sendResponse);
      return true; // Will respond async

    default:
      console.log('[QH Wallet] Unknown message type:', message.type);
  }
});

// Handle signing request from dApp
async function handleSigningRequest(message, sender) {
  const request = {
    id: Date.now().toString(),
    type: message.requestType || 'sign',
    origin: sender.origin || sender.tab?.url || 'unknown',
    data: message.data,
    tabId: sender.tab?.id,
    timestamp: Date.now()
  };

  // Add to pending requests
  const data = await chrome.storage.local.get('pendingRequests');
  const requests = data.pendingRequests || [];
  requests.push(request);
  await chrome.storage.local.set({ pendingRequests: requests });

  // Open popup to handle request
  chrome.action.openPopup();

  // Store callback for later
  pendingCallbacks[request.id] = {
    tabId: sender.tab?.id,
    frameId: sender.frameId
  };
}

// Handle signing response from popup
function handleSigningResponse(message) {
  const callback = pendingCallbacks[message.requestId];

  if (callback && callback.tabId) {
    chrome.tabs.sendMessage(callback.tabId, {
      type: 'QUANTUM_WALLET_RESPONSE',
      requestId: message.requestId,
      signature: message.signature,
      address: message.address,
      error: message.error
    });
  }

  delete pendingCallbacks[message.requestId];
}

// Check if wallet is connected
async function checkConnection(sendResponse) {
  const data = await chrome.storage.local.get(['isUnlocked', 'currentAccount']);

  sendResponse({
    connected: !!data.isUnlocked,
    address: data.currentAccount || null
  });
}

// Store pending callbacks
const pendingCallbacks = {};

// Listen for extension install
chrome.runtime.onInstalled.addListener((details) => {
  if (details.reason === 'install') {
    console.log('[QH Wallet] Extension installed');

    // Initialize storage
    chrome.storage.local.set({
      accounts: {},
      pendingRequests: [],
      isUnlocked: false
    });
  }
});

// Clean up old pending requests on startup
chrome.runtime.onStartup.addListener(async () => {
  const data = await chrome.storage.local.get('pendingRequests');
  const requests = data.pendingRequests || [];

  // Remove requests older than 1 hour
  const cutoff = Date.now() - 3600000;
  const filtered = requests.filter(r => r.timestamp > cutoff);

  await chrome.storage.local.set({ pendingRequests: filtered });

  // Lock wallet on browser restart
  await chrome.storage.local.set({ isUnlocked: false });
});
