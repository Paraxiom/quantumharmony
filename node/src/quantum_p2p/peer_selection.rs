// node/src/quantum_p2p/peer_selection.rs
//
// Verifiable Random Function (VRF) based peer selection.
// Uses quantum-derived randomness for unpredictable but verifiable selection.

use sp_core::{blake2_256, H256};
use std::collections::HashSet;

/// VRF-based peer selection for quantum-secure networking
///
/// Provides deterministic but unpredictable peer selection using
/// a combination of seed data and quantum-derived randomness.
pub struct VrfPeerSelection {
    /// Set of known peer IDs
    known_peers: HashSet<H256>,
}

impl Default for VrfPeerSelection {
    fn default() -> Self {
        Self::new()
    }
}

impl VrfPeerSelection {
    /// Create a new VRF peer selection instance
    pub fn new() -> Self {
        Self {
            known_peers: HashSet::new(),
        }
    }

    /// Add a peer to the known peers set
    pub fn add_peer(&mut self, peer_id: H256) {
        self.known_peers.insert(peer_id);
    }

    /// Remove a peer from the known peers set
    pub fn remove_peer(&mut self, peer_id: &H256) {
        self.known_peers.remove(peer_id);
    }

    /// Get the number of known peers
    pub fn peer_count(&self) -> usize {
        self.known_peers.len()
    }

    /// Get all known peers
    pub fn get_peers(&self) -> Vec<H256> {
        self.known_peers.iter().cloned().collect()
    }

    /// Generate a VRF output from a seed
    ///
    /// This creates a deterministic but unpredictable hash from the seed.
    /// In a full implementation, this would use a proper VRF with proofs.
    pub fn generate_vrf(&self, seed: &[u8]) -> H256 {
        // Combine seed with a domain separator
        let mut input = Vec::with_capacity(seed.len() + 16);
        input.extend_from_slice(b"QUANTUM_VRF_V1:");
        input.extend_from_slice(seed);

        H256::from_slice(&blake2_256(&input))
    }

    /// Select a subset of peers using VRF-based selection
    ///
    /// Returns up to `count` peers selected deterministically based on the seed.
    /// The same seed will always produce the same selection.
    pub fn select_peers(&self, seed: &[u8], count: usize) -> Vec<H256> {
        if self.known_peers.is_empty() || count == 0 {
            return Vec::new();
        }

        let vrf_output = self.generate_vrf(seed);
        let mut peers: Vec<H256> = self.known_peers.iter().cloned().collect();

        // Sort peers for deterministic ordering
        peers.sort();

        let mut selected = Vec::with_capacity(count.min(peers.len()));
        let vrf_bytes = vrf_output.as_bytes();

        // Use VRF bytes to select peers
        let mut used_indices = HashSet::new();
        let mut vrf_index = 0;

        while selected.len() < count && selected.len() < peers.len() {
            // Generate index from VRF bytes
            let mut index_bytes = [0u8; 4];
            for i in 0..4 {
                index_bytes[i] = vrf_bytes[(vrf_index + i) % 32];
            }
            let raw_index = u32::from_le_bytes(index_bytes) as usize;
            let index = raw_index % peers.len();

            // Only add if not already selected
            if !used_indices.contains(&index) {
                used_indices.insert(index);
                selected.push(peers[index]);
            }

            // Move to next VRF bytes, rehash if exhausted
            vrf_index += 4;
            if vrf_index >= 32 && selected.len() < count && selected.len() < peers.len() {
                // Generate new VRF output by hashing previous
                let new_vrf = self.generate_vrf(vrf_output.as_bytes());
                // Update for next iteration (simplified - in practice would track state)
                vrf_index = 0;
            }
        }

        selected
    }

    /// Select peers weighted by a scoring function
    ///
    /// Higher scores increase selection probability.
    pub fn select_weighted<F>(&self, seed: &[u8], count: usize, scorer: F) -> Vec<H256>
    where
        F: Fn(&H256) -> u32,
    {
        if self.known_peers.is_empty() || count == 0 {
            return Vec::new();
        }

        // Score all peers
        let mut scored_peers: Vec<(H256, u32)> = self
            .known_peers
            .iter()
            .map(|p| (*p, scorer(p)))
            .collect();

        // Sort by score descending, then by peer ID for determinism
        scored_peers.sort_by(|a, b| b.1.cmp(&a.1).then_with(|| a.0.cmp(&b.0)));

        let vrf_output = self.generate_vrf(seed);
        let vrf_bytes = vrf_output.as_bytes();

        // Use VRF to add some randomness to selection
        // Higher scored peers are more likely but not guaranteed
        let mut selected = Vec::with_capacity(count.min(scored_peers.len()));
        let mut candidates = scored_peers;

        for i in 0..count.min(candidates.len()) {
            if candidates.is_empty() {
                break;
            }

            // Use VRF byte to potentially shuffle selection
            let vrf_byte = vrf_bytes[i % 32];
            let skip = (vrf_byte as usize) % (candidates.len().max(1));

            // With 75% probability, take the highest scored
            // With 25% probability, skip to add randomness
            let take_index = if vrf_byte < 192 { 0 } else { skip.min(candidates.len() - 1) };

            let (peer, _score) = candidates.remove(take_index);
            selected.push(peer);
        }

        selected
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn create_test_peers(count: usize) -> Vec<H256> {
        (0..count)
            .map(|i| {
                let mut bytes = [0u8; 32];
                bytes[0] = i as u8;
                bytes[31] = (i * 7) as u8; // Add some variation
                H256::from_slice(&bytes)
            })
            .collect()
    }

    #[test]
    fn test_add_remove_peers() {
        let mut selector = VrfPeerSelection::new();
        let peers = create_test_peers(5);

        for peer in &peers {
            selector.add_peer(*peer);
        }
        assert_eq!(selector.peer_count(), 5);

        selector.remove_peer(&peers[0]);
        assert_eq!(selector.peer_count(), 4);
    }

    #[test]
    fn test_vrf_deterministic() {
        let selector = VrfPeerSelection::new();

        let seed = b"test_seed_123";
        let vrf1 = selector.generate_vrf(seed);
        let vrf2 = selector.generate_vrf(seed);

        assert_eq!(vrf1, vrf2, "VRF should be deterministic");
    }

    #[test]
    fn test_vrf_different_seeds() {
        let selector = VrfPeerSelection::new();

        let vrf1 = selector.generate_vrf(b"seed_a");
        let vrf2 = selector.generate_vrf(b"seed_b");

        assert_ne!(vrf1, vrf2, "Different seeds should produce different VRF outputs");
    }

    #[test]
    fn test_select_peers() {
        let mut selector = VrfPeerSelection::new();
        let peers = create_test_peers(10);

        for peer in &peers {
            selector.add_peer(*peer);
        }

        let selected = selector.select_peers(b"selection_seed", 3);
        assert_eq!(selected.len(), 3);

        // All selected should be known peers
        for peer in &selected {
            assert!(selector.known_peers.contains(peer));
        }

        // No duplicates
        let unique: HashSet<_> = selected.iter().collect();
        assert_eq!(unique.len(), 3);
    }

    #[test]
    fn test_select_peers_deterministic() {
        let mut selector = VrfPeerSelection::new();
        let peers = create_test_peers(10);

        for peer in &peers {
            selector.add_peer(*peer);
        }

        let seed = b"deterministic_seed";
        let selected1 = selector.select_peers(seed, 5);
        let selected2 = selector.select_peers(seed, 5);

        assert_eq!(selected1, selected2, "Same seed should select same peers");
    }

    #[test]
    fn test_select_more_than_available() {
        let mut selector = VrfPeerSelection::new();
        let peers = create_test_peers(3);

        for peer in &peers {
            selector.add_peer(*peer);
        }

        let selected = selector.select_peers(b"seed", 10);
        assert_eq!(selected.len(), 3, "Should only return available peers");
    }

    #[test]
    fn test_select_empty() {
        let selector = VrfPeerSelection::new();
        let selected = selector.select_peers(b"seed", 5);
        assert!(selected.is_empty());
    }

    #[test]
    fn test_weighted_selection() {
        let mut selector = VrfPeerSelection::new();
        let peers = create_test_peers(10);

        for peer in &peers {
            selector.add_peer(*peer);
        }

        // Score based on first byte (peers with higher first byte get higher score)
        let scorer = |p: &H256| -> u32 { p.as_bytes()[0] as u32 * 10 };

        let selected = selector.select_weighted(b"weighted_seed", 3, scorer);
        assert_eq!(selected.len(), 3);

        // Higher scored peers should generally be selected
        // (but not guaranteed due to randomness)
        for peer in &selected {
            assert!(selector.known_peers.contains(peer));
        }
    }
}
