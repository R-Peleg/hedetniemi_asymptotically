import HedetniemiAsymptotically.FractionalColoring

namespace Hedetniemi

/-- Giving each singleton weight one provides a fractional coloring of
every finite simple graph. -/
noncomputable def singletonFractionalColoring {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : FractionalColoring G := by
  classical
  have hnonneg (S : Finset V) : (0 : ℝ) ≤ if S.card = 1 then 1 else 0 := by
    split_ifs <;> norm_num
  refine ⟨fun S ↦ if S.card = 1 then 1 else 0, hnonneg, ?_, ?_⟩
  · intro S hS
    split_ifs with hcard
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hcard
      exact (hS (by simp [SimpleGraph.isIndepSet_iff])).elim
    · rfl
  · intro v
    have hmem : ({v} : Finset V) ∈
        Finset.univ.filter (fun S : Finset V ↦ v ∈ S) := by simp
    simpa using Finset.single_le_sum
      (f := fun S : Finset V ↦ if S.card = 1 then (1 : ℝ) else 0)
      (fun S _ ↦ hnonneg S) hmem

end Hedetniemi
