import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

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

end Hedetniemi
