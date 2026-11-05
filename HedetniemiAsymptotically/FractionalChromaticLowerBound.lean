import HedetniemiAsymptotically.FractionalColoring
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hedetniemi

/-- Double counting the weighted incidences between vertices and
independent sets gives `|V| ≤ k` times the total fractional weight. -/
theorem FractionalColoring.card_le_mul_totalWeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (χ : FractionalColoring G) (k : ℕ)
    (hk : ∀ S : Finset V, G.IsIndepSet (S : Set V) → S.card ≤ k) :
    (Fintype.card V : ℝ) ≤ (k : ℝ) * χ.totalWeight := by
  classical
  calc
    (Fintype.card V : ℝ) = ∑ _v : V, (1 : ℝ) := by simp
    _ ≤ ∑ v, ∑ S ∈ Finset.univ.filter (fun S : Finset V ↦ v ∈ S), χ.weight S :=
      Finset.sum_le_sum (fun v _ ↦ χ.cover v)
    _ = ∑ v, ∑ S : Finset V, if v ∈ S then χ.weight S else 0 := by
      simp only [Finset.sum_filter]
    _ = ∑ S : Finset V, ∑ v, if v ∈ S then χ.weight S else 0 := Finset.sum_comm
    _ = ∑ S : Finset V, (S.card : ℝ) * χ.weight S := by
      apply Finset.sum_congr rfl
      intro S _
      rw [← Finset.sum_filter]
      have heq : Finset.univ.filter (fun v : V ↦ v ∈ S) = S := by ext v; simp
      rw [heq]
      simp
    _ ≤ ∑ S : Finset V, (k : ℝ) * χ.weight S := by
      apply Finset.sum_le_sum
      intro S _
      by_cases hS : G.IsIndepSet (S : Set V)
      · exact mul_le_mul_of_nonneg_right (by exact_mod_cast hk S hS) (χ.nonneg S)
      · rw [χ.independent S hS]
        simp
    _ = (k : ℝ) * χ.totalWeight := by simp only [FractionalColoring.totalWeight, Finset.mul_sum]

end Hedetniemi
