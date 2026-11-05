import HedetniemiAsymptotically.CycleTemplates
import Mathlib.Algebra.Group.Fin.Basic

namespace Hedetniemi

/-- The cyclic successor has no fixed point on a cycle of length at least three. -/
theorem cycle_successor_ne {m : ℕ} (i : Fin (m + 3)) : i + 1 ≠ i := by
  intro h
  have hz : (1 : Fin (m + 3)) = 0 :=
    add_left_cancel (show i + 1 = i + 0 by simpa only [add_zero] using h)
  have hv : (1 : ℕ) = 0 := congrArg Fin.val hz
  omega

end Hedetniemi
