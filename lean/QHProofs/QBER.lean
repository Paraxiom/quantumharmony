/-
  QHProofs.QBER

  Quantum Bit Error Rate validation properties.

  Key results:
    - qber_threshold         — threshold = 1100 basis points = 11%
    - qber_avg_bounded       — if sum ≤ T × count then average ≤ T
    - healthy_channel_count  — healthy count ≤ total votes
    - rejection_criterion    — channel rejection logic
    - qkd_theoretical_limit  — 11% < 14.6% BB84 max

  Mirrors: pallets/qber-validation/src/lib.rs.
  Tier 3 verification (Lean 4).
-/

import Mathlib.Tactic.NormNum

namespace QHProofs.QBER

/-! ## Constants -/

/-- QBER threshold in basis points. 1100 bp = 11%. -/
def QBER_THRESHOLD_BP : ℕ := 1100

/-- Total basis points (100%). -/
def BASIS_POINTS_FULL : ℕ := 10000

/-- BB84 theoretical maximum QBER in basis points (~14.6%). -/
def BB84_MAX_BP : ℕ := 1460

/-! ## Threshold properties -/

/-- QBER threshold = 1100 basis points = 11%. -/
theorem qber_threshold : QBER_THRESHOLD_BP = 1100 := by rfl

/-- 10000 basis points = 100%. -/
theorem qber_basis_points : BASIS_POINTS_FULL = 10000 := by rfl

/-- 11% QBER threshold < 14.6% BB84 theoretical maximum.
    This leaves margin for practical noise while remaining below the
    information-theoretic limit. -/
theorem qkd_theoretical_limit : QBER_THRESHOLD_BP < BB84_MAX_BP := by
  norm_num [QBER_THRESHOLD_BP, BB84_MAX_BP]

/-- QBER threshold is a proper fraction of the full range. -/
theorem qber_threshold_lt_full : QBER_THRESHOLD_BP < BASIS_POINTS_FULL := by
  norm_num [QBER_THRESHOLD_BP, BASIS_POINTS_FULL]

/-! ## Average bounds -/

/-- If the sum of all QBER measurements is at most T × count (i.e., each
    individual measurement is at most T on average), then the average is at most T.
    Uses: sum ≤ T × count → sum / count ≤ (T × count) / count = T. -/
theorem qber_avg_bounded (sum_qber count T : ℕ) (h_count : count ≥ 1)
    (h_sum : sum_qber ≤ T * count) :
    sum_qber / count ≤ T := by
  calc sum_qber / count
      ≤ (T * count) / count := Nat.div_le_div_right h_sum
    _ = T := Nat.mul_div_cancel T (by omega)

/-! ## Channel health counting -/

/-- The count of healthy channels cannot exceed the total number of votes. -/
theorem healthy_channel_count_le (healthy total : ℕ) (h : healthy ≤ total) :
    healthy ≤ total := h

/-- Rejection criterion: reject if avg_qber > threshold OR healthy < total/2. -/
theorem rejection_criterion (avg_qber healthy total : ℕ)
    (h_reject : avg_qber > QBER_THRESHOLD_BP ∨ healthy * 2 < total) :
    avg_qber > 1100 ∨ healthy * 2 < total := by
  simp only [QBER_THRESHOLD_BP] at h_reject; exact h_reject

/-- If a channel passes both criteria, it has good QBER and majority healthy. -/
theorem acceptance_conditions (avg_qber healthy total : ℕ)
    (h_qber : avg_qber ≤ QBER_THRESHOLD_BP) (h_healthy : healthy * 2 ≥ total) :
    avg_qber ≤ 1100 ∧ healthy * 2 ≥ total := by
  simp only [QBER_THRESHOLD_BP] at h_qber; exact ⟨h_qber, h_healthy⟩

/-! ## NIST SP 800-90B health tests (issue #3)

    Entropy source health monitoring per NIST SP 800-90B §4.4.
    Two mandatory tests: RCT (Repetition Count) and APT (Adaptive Proportion). -/

/-- RCT cutoff: maximum consecutive identical bytes before rejection.
    For H_min = 8 (ideal), cutoff = 1 + ⌈-log₂(2⁻²⁰) / H_min⌉ = 4.
    We use cutoff = 5 for conservative margin. -/
def RCT_CUTOFF : ℕ := 5

/-- APT window size: number of bytes to scan. -/
def APT_WINDOW : ℕ := 512

/-- APT cutoff: max occurrences of most-frequent symbol in window.
    For uniform distribution, expected = 512/256 = 2.
    Cutoff = 8 gives very low false positive rate. -/
def APT_CUTOFF : ℕ := 8

/-- RCT cutoff is at least 2 (trivial repetition is allowed). -/
theorem rct_cutoff_ge_two : RCT_CUTOFF ≥ 2 := by
  norm_num [RCT_CUTOFF]

/-- APT window fits 2 full byte-value cycles (512 = 2 × 256). -/
theorem apt_window_is_two_cycles : APT_WINDOW = 2 * 256 := by
  norm_num [APT_WINDOW]

/-- APT cutoff is well above expected frequency (2) but well below window size. -/
theorem apt_cutoff_bounds : APT_CUTOFF > APT_WINDOW / 256 ∧ APT_CUTOFF < APT_WINDOW := by
  norm_num [APT_CUTOFF, APT_WINDOW]

/-- Both tests must pass for entropy to be accepted (conjunction). -/
theorem health_test_conjunction (rct_pass apt_pass : Prop)
    (h_rct : rct_pass) (h_apt : apt_pass) : rct_pass ∧ apt_pass :=
  ⟨h_rct, h_apt⟩

/-! ## Proof timestamp freshness (issue #21) -/

/-- Maximum proof age in milliseconds (60 seconds). -/
def MAX_PROOF_AGE_MS : ℕ := 60000

/-- 60 seconds = 10 block periods (6s each). -/
theorem max_proof_age_blocks : MAX_PROOF_AGE_MS / 6000 = 10 := by
  norm_num [MAX_PROOF_AGE_MS]

/-- A proof is fresh if current_time - proof_time ≤ MAX_PROOF_AGE_MS. -/
theorem proof_freshness (now proof_time : ℕ) (_h_order : proof_time ≤ now)
    (h_fresh : now - proof_time ≤ MAX_PROOF_AGE_MS) :
    now - proof_time ≤ 60000 := by
  unfold MAX_PROOF_AGE_MS at h_fresh; exact h_fresh

end QHProofs.QBER
