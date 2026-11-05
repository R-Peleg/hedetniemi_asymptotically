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

end Hedetniemi
