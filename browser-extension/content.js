/**
 * QuantumHarmony Wallet - Content Script
 *
 * Injected into web pages to enable wallet interaction.
 * Provides window.quantumHarmony API similar to window.ethereum.
 */

// Inject the provider API into the page
const script = document.createElement('script');
script.textContent = `
(function() {
  // QuantumHarmony Provider API
  window.quantumHarmony = {
    isQuantumHarmony: true,
    isConnected: false,
    selectedAddress: null,

    // Request connection (like eth_requestAccounts)
    async connect() {
      return new Promise((resolve, reject) => {
        window.postMessage({
          type: 'QUANTUM_CONNECT_REQUEST',
          id: Date.now()
        }, '*');

        const handler = (event) => {
          if (event.data.type === 'QUANTUM_CONNECT_RESPONSE') {
            window.removeEventListener('message', handler);
            if (event.data.error) {
              reject(new Error(event.data.error));
            } else {
              window.quantumHarmony.isConnected = true;
              window.quantumHarmony.selectedAddress = event.data.address;
              resolve(event.data.address);
            }
          }
        };
        window.addEventListener('message', handler);
      });
    },

    // Get current account
    async getAccount() {
      return this.selectedAddress;
    },

    // Sign a message
    async signMessage(message) {
      return this.sign({ type: 'message', data: message });
    },

    // Sign login challenge
    async signLogin(challenge) {
      return this.sign({ type: 'login', data: challenge });
    },

    // Sign transaction
    async signTransaction(tx) {
      return this.sign({ type: 'transaction', data: tx });
    },

    // Generic sign request
    async sign(request) {
      return new Promise((resolve, reject) => {
        const id = Date.now();
        window.postMessage({
          type: 'QUANTUM_SIGN_REQUEST',
          id: id,
          request: request
        }, '*');

        const handler = (event) => {
          if (event.data.type === 'QUANTUM_SIGN_RESPONSE' && event.data.id === id) {
            window.removeEventListener('message', handler);
            if (event.data.error) {
              reject(new Error(event.data.error));
            } else {
              resolve({
                signature: event.data.signature,
                address: event.data.address
              });
            }
          }
        };
        window.addEventListener('message', handler);

        // Timeout after 5 minutes
        setTimeout(() => {
          window.removeEventListener('message', handler);
          reject(new Error('Request timed out'));
        }, 300000);
      });
    },

    // Listen for account changes
    on(event, callback) {
      if (event === 'accountsChanged') {
        window.addEventListener('message', (e) => {
          if (e.data.type === 'QUANTUM_ACCOUNTS_CHANGED') {
            callback([e.data.address]);
          }
        });
      }
    }
  };

  // Dispatch event to signal wallet is available
  window.dispatchEvent(new Event('quantumHarmonyReady'));
  console.log('[QuantumHarmony] Wallet provider injected');
})();
`;
document.documentElement.appendChild(script);
script.remove();

// Listen for messages from the page
window.addEventListener('message', async (event) => {
  if (event.source !== window) return;

  switch (event.data.type) {
    case 'QUANTUM_CONNECT_REQUEST':
      handleConnectRequest(event.data);
      break;

    case 'QUANTUM_SIGN_REQUEST':
      handleSignRequest(event.data);
      break;
  }
});

// Handle connection request
async function handleConnectRequest(data) {
  try {
    const response = await chrome.runtime.sendMessage({ type: 'CHECK_CONNECTION' });

    if (response.connected) {
      window.postMessage({
        type: 'QUANTUM_CONNECT_RESPONSE',
        address: response.address
      }, '*');
    } else {
      // Trigger popup to unlock/connect
      chrome.runtime.sendMessage({
        type: 'SIGNING_REQUEST',
        requestType: 'connect',
        data: { origin: window.location.origin }
      });
    }
  } catch (e) {
    window.postMessage({
      type: 'QUANTUM_CONNECT_RESPONSE',
      error: 'Wallet not available'
    }, '*');
  }
}

// Handle sign request
async function handleSignRequest(data) {
  try {
    chrome.runtime.sendMessage({
      type: 'SIGNING_REQUEST',
      requestType: data.request.type,
      data: data.request.data
    });

    // Response will come back via QUANTUM_WALLET_RESPONSE
  } catch (e) {
    window.postMessage({
      type: 'QUANTUM_SIGN_RESPONSE',
      id: data.id,
      error: e.message
    }, '*');
  }
}

// Listen for responses from background
chrome.runtime.onMessage.addListener((message) => {
  if (message.type === 'QUANTUM_WALLET_CONNECT') {
    window.postMessage({
      type: 'QUANTUM_CONNECT_RESPONSE',
      address: message.address
    }, '*');

    // Also notify of account change
    window.postMessage({
      type: 'QUANTUM_ACCOUNTS_CHANGED',
      address: message.address
    }, '*');
  }

  if (message.type === 'QUANTUM_WALLET_RESPONSE') {
    window.postMessage({
      type: 'QUANTUM_SIGN_RESPONSE',
      id: message.requestId,
      signature: message.signature,
      address: message.address,
      error: message.error
    }, '*');
  }
});

console.log('[QuantumHarmony] Content script loaded');
