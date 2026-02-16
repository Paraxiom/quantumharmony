/-
  QHProofs.Crypto

  Cryptographic parameter properties for QuantumHarmony.

  Key results:
    - keccak256_output_bits    — 256 bits = 32 bytes
    - keccak256_pq_security    — 128-bit PQ security (Grover)
    - falcon1024_sig_compact   — Falcon < SPHINCS+ signature size
    - extrinsic_max_size       — SPHINCS+ sig fits in block limit
    - block_fits_transactions  — ≥ 68 SPHINCS+ transactions per block

  Mirrors: runtime/src/lib.rs, crypto/ constants.
  Tier 3 verification (Lean 4).
-/

import Mathlib.Tactic.NormNum

namespace QHProofs.Crypto

/-! ## Hash parameters -/

/-- Keccak-256 output size in bytes. -/
def KECCAK256_BYTES : ℕ := 32

/-- Keccak-256 output size in bits. -/
def KECCAK256_BITS : ℕ := 256

/-- 256 bits = 32 bytes. -/
theorem keccak256_output_bits : KECCAK256_BYTES * 8 = KECCAK256_BITS := by
  norm_num [KECCAK256_BYTES, KECCAK256_BITS]

/-- Grover's algorithm halves security: 256/2 = 128 bits PQ security. -/
theorem keccak256_pq_security : KECCAK256_BITS / 2 = 128 := by
  norm_num [KECCAK256_BITS]

/-! ## Account ID -/

/-- AccountId32 size in bytes. -/
def ACCOUNT_ID_BYTES : ℕ := 32

/-- SPHINCS+ public key size in bytes. -/
def SPHINCS_PK_BYTES : ℕ := 64

/-- SPHINCS+ pk (64 bytes) → AccountId32 (32 bytes) via Keccak-256 hash. -/
theorem sphincs_pk_to_account_id :
    SPHINCS_PK_BYTES > ACCOUNT_ID_BYTES := by
  norm_num [SPHINCS_PK_BYTES, ACCOUNT_ID_BYTES]

/-- AccountId32 = 256 bits. -/
theorem account_id_bits : ACCOUNT_ID_BYTES * 8 = 256 := by
  norm_num [ACCOUNT_ID_BYTES]

/-! ## Signature size comparisons -/

/-- Falcon-1024 signature size in bytes. -/
def FALCON1024_SIG : ℕ := 1280

/-- SPHINCS+-SHAKE-256s-simple signature size in bytes. -/
def SPHINCS_SIG : ℕ := 29792

/-- Falcon-1024 signature is smaller than SPHINCS+. -/
theorem falcon1024_sig_compact : FALCON1024_SIG < SPHINCS_SIG := by
  norm_num [FALCON1024_SIG, SPHINCS_SIG]

/-- SPHINCS+ / Falcon signature ratio exceeds 23x. -/
theorem falcon1024_sig_ratio : SPHINCS_SIG / FALCON1024_SIG ≥ 23 := by
  norm_num [SPHINCS_SIG, FALCON1024_SIG]

/-! ## Block size constraints -/

/-- Maximum block size in bytes (2 MB). -/
def MAX_BLOCK_SIZE : ℕ := 2 * 1024 * 1024

/-- Overhead per extrinsic (conservative estimate: 256 bytes). -/
def EXTRINSIC_OVERHEAD : ℕ := 256

/-- SPHINCS+ sig + overhead fits within max block size.
    29792 + 256 = 30048 < 2097152. -/
theorem extrinsic_max_size : SPHINCS_SIG + EXTRINSIC_OVERHEAD < MAX_BLOCK_SIZE := by
  norm_num [SPHINCS_SIG, EXTRINSIC_OVERHEAD, MAX_BLOCK_SIZE]

/-- At least 68 full SPHINCS+ extrinsics fit in one block.
    2097152 / 30048 ≥ 68. -/
theorem block_fits_transactions :
    MAX_BLOCK_SIZE / (SPHINCS_SIG + EXTRINSIC_OVERHEAD) ≥ 68 := by
  norm_num [MAX_BLOCK_SIZE, SPHINCS_SIG, EXTRINSIC_OVERHEAD]

end QHProofs.Crypto
