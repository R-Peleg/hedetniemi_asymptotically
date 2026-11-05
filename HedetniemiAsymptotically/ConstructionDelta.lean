import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

namespace Hedetniemi

/-- The factor `δ = 1/(81n)` used in the construction. -/
noncomputable def constructionDelta (n : ℕ) : ℝ := 1 / (81 * (n : ℝ))

theorem constructionDelta_pos {n : ℕ} (hn : 0 < n) : 0 < constructionDelta n := by
  unfold constructionDelta
  positivity

theorem mul_constructionDelta {n : ℕ} (hn : 0 < n) :
    (n : ℝ) * constructionDelta n = 1 / 81 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  unfold constructionDelta
  field_simp

theorem constructionDelta_le {n : ℕ} (hn : 4 ≤ n) : constructionDelta n ≤ 1 / 324 := by
  have hnR : (4 : ℝ) ≤ n := by exact_mod_cast hn
  unfold constructionDelta
  apply (div_le_iff₀ (show (0 : ℝ) < 81 * n by positivity)).mpr
  nlinarith

/-- The explicit lower bound supplied by the two-million-vertex construction. -/
theorem constructionDelta_lower_bound {n : ℕ} (hn : 0 < n) (hN : n ≤ 2000000) :
    (1 / 162000000 : ℝ) ≤ constructionDelta n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (n : ℝ) ≤ 2000000 := by exact_mod_cast hN
  unfold constructionDelta
  apply (le_div_iff₀ (show (0 : ℝ) < 81 * n by positivity)).mpr
  nlinarith

end Hedetniemi
