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

/-- A cyclic edge enumeration has no repetitions, including reversed edges. -/
theorem cycle_edge_injective {m : ℕ} (σ : Equiv.Perm (Fin (m + 3))) :
    Function.Injective (fun i ↦ s(σ i, σ (i + 1))) := by
  intro i j hij
  rcases Sym2.eq_iff.mp hij with h | h
  · exact σ.injective h.1
  · have hi : i = j + 1 := σ.injective h.1
    have hj : i + 1 = j := σ.injective h.2
    have heq : j + (2 : Fin (m + 3)) = j + 0 := by
      calc
        j + 2 = (j + 1) + 1 := by
          apply Fin.ext
          change (j.val + 2) % (m + 3) =
            ((j.val + 1) % (m + 3) + 1) % (m + 3)
          rw [Nat.mod_add_mod]
        _ = i + 1 := by rw [hi]
        _ = j + 0 := by simpa only [add_zero] using hj
    have hz : (2 : Fin (m + 3)) = 0 := add_left_cancel heq
    have hv : (2 : ℕ) = 0 := congrArg Fin.val hz
    omega

end Hedetniemi
