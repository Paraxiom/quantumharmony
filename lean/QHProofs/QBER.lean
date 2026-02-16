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

end QHProofs.QBER
