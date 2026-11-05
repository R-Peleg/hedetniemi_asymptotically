import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

namespace Hedetniemi

/-- The fourth-root error term `x = ((nt+n³)c³)^(1/4)` of Lemma 5. -/
noncomputable def robustError (n c t : ℕ) : ℝ :=
  Real.sqrt (Real.sqrt (((n : ℝ) * t + (n : ℝ) ^ 3) * (c : ℝ) ^ 3))

/-- The defining fourth-power identity for the robust-color error. -/
theorem robustError_pow_four (n c t : ℕ) :
    robustError n c t ^ 4 = ((n : ℝ) * t + (n : ℝ) ^ 3) * (c : ℝ) ^ 3 := by
  unfold robustError
  rw [show ∀ z : ℝ, z ^ 4 = (z ^ 2) ^ 2 by intro z; ring,
    Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt (by positivity)]

theorem robustError_pos {n c t : ℕ} (hn : 0 < n) (hc : 0 < c) :
    0 < robustError n c t := by
  unfold robustError
  apply Real.sqrt_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

/-- The numerical hypothesis in Lemma 5 implies that its error is at most `c/2`. -/
theorem robustError_le_half {n c t : ℕ} (h : 16 * (n * t + n ^ 3) ≤ c) :
    robustError n c t ≤ (c : ℝ) / 2 := by
  have hx : 0 ≤ robustError n c t := Real.sqrt_nonneg _
  apply (pow_le_pow_iff_left₀ hx (by positivity : (0 : ℝ) ≤ (c : ℝ) / 2)
    (by decide : (4 : ℕ) ≠ 0)).mp
  rw [robustError_pow_four]
  have hR : 16 * ((n : ℝ) * t + (n : ℝ) ^ 3) ≤ c := by exact_mod_cast h
  have hm := mul_le_mul_of_nonneg_right hR (show (0 : ℝ) ≤ (c : ℝ) ^ 3 by positivity)
  nlinarith

end Hedetniemi
