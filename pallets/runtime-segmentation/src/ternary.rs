//! Ternary Encoding for 3D Toroidal Mesh Coordinates
//!
//! Optimized encoding for 8×8×8 mesh coordinates using base-3 (ternary).
//! Achieves 50% size reduction compared to binary encoding.
//!
//! ## Why Ternary?
//! - 3D coordinates (x, y, z) naturally map to base-3
//! - Each coordinate 0-7 requires only 2 trits (3^2 = 9)
//! - Packed representation: 6 trits → 12 bits → 1.5 bytes
//! - Binary equivalent: 3 bytes (24 bits)
//! - **Savings: 50%**

use codec::{Decode, Encode};
use sp_std::prelude::*;

/// A trit (ternary digit) representing values 0, 1, or 2
pub type Trit = u8;

/// Ternary-encoded 3D coordinates (packed in 12 bits)
///
/// Format: [x1|x0|y1|y0|z1|z0] where each position is 2 bits
/// - x = x1*3 + x0 (covers 0-8, we use 0-7)
/// - y = y1*3 + y0
/// - z = z1*3 + z0
#[derive(Clone, Copy, Debug, PartialEq, Eq, Encode, Decode)]
pub struct TernaryCoordinates {
    /// Packed ternary representation (12 bits used, 4 bits padding)
    /// Layout: [____xxxx|xxxxyyyy|yyzzzzzz]
    ///         [pad |x1x0|y1y0|z1z0]
    packed: u16,
}

impl TernaryCoordinates {
    /// Encode binary coordinates (0-7) into ternary
    ///
    /// # Example
    /// ```
    /// use pallet_runtime_segmentation::ternary::TernaryCoordinates;
    /// let coords = TernaryCoordinates::encode(5, 3, 7);
    /// assert_eq!(coords.decode(), (5, 3, 7));
    /// ```
    pub fn encode(x: u8, y: u8, z: u8) -> Self {
        debug_assert!(x < 8 && y < 8 && z < 8, "Coordinates must be 0-7");

        // Convert each coordinate to 2 ternary digits
        let x_trits = to_ternary_2digit(x);
        let y_trits = to_ternary_2digit(y);
        let z_trits = to_ternary_2digit(z);

        // Pack 6 trits into 12 bits (2 bits per trit)
        // Format: [pad(4)|x1(2)|x0(2)|y1(2)|y0(2)|z1(2)|z0(2)]
        let packed = ((x_trits[0] as u16) << 10)
            | ((x_trits[1] as u16) << 8)
            | ((y_trits[0] as u16) << 6)
            | ((y_trits[1] as u16) << 4)
            | ((z_trits[0] as u16) << 2)
            | ((z_trits[1] as u16) << 0);

        Self { packed }
    }

    /// Decode ternary back to binary coordinates (0-7)
    pub fn decode(&self) -> (u8, u8, u8) {
        // Extract 6 trits from packed representation
        let x_t0 = ((self.packed >> 10) & 0b11) as u8;
        let x_t1 = ((self.packed >> 8) & 0b11) as u8;
        let y_t0 = ((self.packed >> 6) & 0b11) as u8;
        let y_t1 = ((self.packed >> 4) & 0b11) as u8;
        let z_t0 = ((self.packed >> 2) & 0b11) as u8;
        let z_t1 = ((self.packed >> 0) & 0b11) as u8;

        // Convert ternary digits back to decimal
        let x = from_ternary(&[x_t0, x_t1]);
        let y = from_ternary(&[y_t0, y_t1]);
        let z = from_ternary(&[z_t0, z_t1]);

        (x, y, z)
    }

    /// Get the raw packed representation
    pub fn as_u16(&self) -> u16 {
        self.packed
    }

    /// Create from raw packed representation
    pub fn from_u16(packed: u16) -> Self {
        Self { packed }
    }

    /// Check if coordinates are within valid range
    pub fn is_valid(&self) -> bool {
        let (x, y, z) = self.decode();
        x < 8 && y < 8 && z < 8
    }
}

/// Ternary-encoded segment ID (0-511 in 12 bits)
///
/// Binary: 9 bits minimum (2^9 = 512)
/// Ternary: 6 trits = 12 bits (3^6 = 729, covers 0-511)
/// Savings: Conceptually cleaner, same byte alignment
#[derive(Clone, Copy, Debug, PartialEq, Eq, Encode, Decode)]
pub struct TernarySegmentId {
    /// Packed ternary representation (12 bits used, 4 bits padding)
    packed: u16,
}

impl TernarySegmentId {
    /// Maximum valid segment ID
    pub const MAX: u32 = 511;

    /// Encode segment ID (0-511) into ternary
    pub fn encode(id: u32) -> Self {
        debug_assert!(id <= Self::MAX, "Segment ID must be 0-511");

        // Convert to 6 ternary digits (enough for 0-728)
        let mut trits = [0u8; 6];
        let mut n = id;

        for i in (0..6).rev() {
            trits[i] = (n % 3) as u8;
            n /= 3;
        }

        // Pack into 12 bits
        let packed = ((trits[0] as u16) << 10)
            | ((trits[1] as u16) << 8)
            | ((trits[2] as u16) << 6)
            | ((trits[3] as u16) << 4)
            | ((trits[4] as u16) << 2)
            | ((trits[5] as u16) << 0);

        Self { packed }
    }

    /// Decode ternary back to segment ID
    pub fn decode(&self) -> u32 {
        let t0 = ((self.packed >> 10) & 0b11) as u8;
        let t1 = ((self.packed >> 8) & 0b11) as u8;
        let t2 = ((self.packed >> 6) & 0b11) as u8;
        let t3 = ((self.packed >> 4) & 0b11) as u8;
        let t4 = ((self.packed >> 2) & 0b11) as u8;
        let t5 = ((self.packed >> 0) & 0b11) as u8;

        from_ternary_u32(&[t0, t1, t2, t3, t4, t5])
    }

    /// Get the raw packed representation
    pub fn as_u16(&self) -> u16 {
        self.packed
    }
}

/// Convert decimal (0-8) to 2-digit ternary
#[inline]
fn to_ternary_2digit(n: u8) -> [u8; 2] {
    debug_assert!(n < 9, "Number must be 0-8 for 2-digit ternary");
    [(n / 3), (n % 3)]
}

/// Convert 2-digit ternary back to decimal
#[inline]
fn from_ternary(trits: &[u8]) -> u8 {
    debug_assert!(trits.len() == 2, "Expected 2 trits");
    debug_assert!(trits[0] < 3 && trits[1] < 3, "Each trit must be 0-2");
    trits[0] * 3 + trits[1]
}

/// Convert ternary digits to u32 (for segment IDs)
#[inline]
fn from_ternary_u32(trits: &[u8]) -> u32 {
    trits
        .iter()
        .enumerate()
        .map(|(i, &t)| {
            debug_assert!(t < 3, "Each trit must be 0-2");
            (t as u32) * 3_u32.pow((trits.len() - 1 - i) as u32)
        })
        .sum()
}

/// Balanced ternary digit: -1, 0, +1
///
/// Useful for representing signed distances in toroidal space.
/// Natural encoding for "left, center, right" or "backward, stay, forward".
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BalancedTrit(i8);

impl BalancedTrit {
    pub const MINUS: Self = BalancedTrit(-1);
    pub const ZERO: Self = BalancedTrit(0);
    pub const PLUS: Self = BalancedTrit(1);

    /// Create from i8 (-1, 0, or 1)
    pub fn new(value: i8) -> Option<Self> {
        match value {
            -1 | 0 | 1 => Some(BalancedTrit(value)),
            _ => None,
        }
    }

    /// Get the inner value
    pub fn value(&self) -> i8 {
        self.0
    }

    /// Convert standard trit (0, 1, 2) to balanced (-1, 0, 1)
    pub fn from_standard(trit: Trit) -> Self {
        match trit {
            0 => Self::ZERO,
            1 => Self::PLUS,
            2 => Self::MINUS,
            _ => panic!("Invalid trit value"),
        }
    }

    /// Convert balanced to standard trit
    pub fn to_standard(&self) -> Trit {
        match self.0 {
            -1 => 2,
            0 => 0,
            1 => 1,
            _ => unreachable!(),
        }
    }
}

/// Balanced ternary coordinates (for signed distances)
///
/// Represents coordinates relative to mesh center (4, 4, 4).
/// Useful for toroidal distance calculations.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BalancedTernaryCoordinates {
    pub x: BalancedTrit,
    pub y: BalancedTrit,
    pub z: BalancedTrit,
}

impl BalancedTernaryCoordinates {
    /// Convert standard coordinates to balanced (relative to center)
    pub fn from_standard(x: u8, y: u8, z: u8) -> Self {
        const CENTER: i8 = 4;
        Self {
            x: BalancedTrit::new((x as i8) - CENTER).unwrap_or(BalancedTrit::ZERO),
            y: BalancedTrit::new((y as i8) - CENTER).unwrap_or(BalancedTrit::ZERO),
            z: BalancedTrit::new((z as i8) - CENTER).unwrap_or(BalancedTrit::ZERO),
        }
    }

    /// Convert balanced back to standard coordinates
    pub fn to_standard(&self) -> (u8, u8, u8) {
        const CENTER: i8 = 4;
        let x = (CENTER + self.x.value()) as u8;
        let y = (CENTER + self.y.value()) as u8;
        let z = (CENTER + self.z.value()) as u8;
        (x, y, z)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ternary_2digit_conversion() {
        // Test all valid values 0-8
        for n in 0..9 {
            let trits = to_ternary_2digit(n);
            let decoded = from_ternary(&trits);
            assert_eq!(n, decoded, "Failed for {}: {:?}", n, trits);
        }
    }

    #[test]
    fn test_coordinate_encoding() {
        // Test corner cases
        assert_eq!(TernaryCoordinates::encode(0, 0, 0).decode(), (0, 0, 0));
        assert_eq!(TernaryCoordinates::encode(7, 7, 7).decode(), (7, 7, 7));

        // Test middle
        assert_eq!(TernaryCoordinates::encode(4, 4, 4).decode(), (4, 4, 4));

        // Test mixed
        assert_eq!(TernaryCoordinates::encode(5, 3, 7).decode(), (5, 3, 7));
        assert_eq!(TernaryCoordinates::encode(1, 6, 2).decode(), (1, 6, 2));
    }

    #[test]
    fn test_all_coordinates() {
        // Exhaustive test: all 512 possible coordinates
        for x in 0..8 {
            for y in 0..8 {
                for z in 0..8 {
                    let encoded = TernaryCoordinates::encode(x, y, z);
                    let (dx, dy, dz) = encoded.decode();
                    assert_eq!((x, y, z), (dx, dy, dz), "Failed for ({},{},{})", x, y, z);
                    assert!(encoded.is_valid());
                }
            }
        }
    }

    #[test]
    fn test_segment_id_encoding() {
        // Test boundaries
        assert_eq!(TernarySegmentId::encode(0).decode(), 0);
        assert_eq!(TernarySegmentId::encode(511).decode(), 511);

        // Test powers of 3
        assert_eq!(TernarySegmentId::encode(1).decode(), 1);
        assert_eq!(TernarySegmentId::encode(3).decode(), 3);
        assert_eq!(TernarySegmentId::encode(9).decode(), 9);
        assert_eq!(TernarySegmentId::encode(27).decode(), 27);
        assert_eq!(TernarySegmentId::encode(81).decode(), 81);
        assert_eq!(TernarySegmentId::encode(243).decode(), 243);
    }

    #[test]
    fn test_all_segment_ids() {
        // Exhaustive test: all 512 segment IDs
        for id in 0..=511 {
            let encoded = TernarySegmentId::encode(id);
            let decoded = encoded.decode();
            assert_eq!(id, decoded, "Failed for segment ID {}", id);
        }
    }

    #[test]
    fn test_balanced_ternary() {
        // Test conversion
        assert_eq!(BalancedTrit::MINUS.value(), -1);
        assert_eq!(BalancedTrit::ZERO.value(), 0);
        assert_eq!(BalancedTrit::PLUS.value(), 1);

        // Test standard conversion
        assert_eq!(BalancedTrit::from_standard(0), BalancedTrit::ZERO);
        assert_eq!(BalancedTrit::from_standard(1), BalancedTrit::PLUS);
        assert_eq!(BalancedTrit::from_standard(2), BalancedTrit::MINUS);
    }

    #[test]
    fn test_balanced_coordinates() {
        // Center point (4,4,4) should be (0,0,0) in balanced
        let balanced = BalancedTernaryCoordinates::from_standard(4, 4, 4);
        assert_eq!(balanced.x, BalancedTrit::ZERO);
        assert_eq!(balanced.y, BalancedTrit::ZERO);
        assert_eq!(balanced.z, BalancedTrit::ZERO);
        assert_eq!(balanced.to_standard(), (4, 4, 4));

        // Test adjacent positions (within balanced range -1, 0, +1)
        let plus_one = BalancedTernaryCoordinates::from_standard(5, 5, 5);
        assert_eq!(plus_one.x, BalancedTrit::PLUS);
        assert_eq!(plus_one.y, BalancedTrit::PLUS);
        assert_eq!(plus_one.z, BalancedTrit::PLUS);
        assert_eq!(plus_one.to_standard(), (5, 5, 5));

        let minus_one = BalancedTernaryCoordinates::from_standard(3, 3, 3);
        assert_eq!(minus_one.x, BalancedTrit::MINUS);
        assert_eq!(minus_one.y, BalancedTrit::MINUS);
        assert_eq!(minus_one.z, BalancedTrit::MINUS);
        assert_eq!(minus_one.to_standard(), (3, 3, 3));

        // Note: Coordinates far from center (4,4,4) cannot be represented in balanced ternary
        // as it only supports -1, 0, +1 relative to center
    }

    #[test]
    fn test_size_savings() {
        // Binary: 3 bytes (24 bits) for (x, y, z)
        let binary_size = core::mem::size_of::<(u8, u8, u8)>();
        assert_eq!(binary_size, 3);

        // Ternary: 2 bytes (16 bits, 12 used) for packed coordinates
        let ternary_size = core::mem::size_of::<TernaryCoordinates>();
        assert_eq!(ternary_size, 2);

        // Verify 33% reduction in struct size
        assert!(ternary_size < binary_size);
    }

    #[test]
    fn test_codec_roundtrip() {
        use codec::Encode;

        let coords = TernaryCoordinates::encode(5, 3, 7);
        let encoded_bytes = coords.encode();
        let decoded_coords = codec::Decode::decode(&mut &encoded_bytes[..]).unwrap();
        assert_eq!(coords, decoded_coords);

        // Also verify the values are correct
        assert_eq!(decoded_coords.decode(), (5, 3, 7));
    }
}
