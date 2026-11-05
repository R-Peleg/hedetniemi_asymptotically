import HedetniemiAsymptotically.SingletonFractionalColoring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

namespace Hedetniemi

/-- The fractional chromatic number is the infimum of total weights of
fractional colorings. Singleton colorings ensure the feasible set is nonempty. -/
noncomputable def fractionalChromaticNumber {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : ℝ :=
  sInf (Set.range (fun χ : FractionalColoring G ↦ χ.totalWeight))

theorem fractionalChromaticNumber_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : 0 ≤ fractionalChromaticNumber G := by
  unfold fractionalChromaticNumber
  have hnonempty : (Set.range (fun χ : FractionalColoring G ↦ χ.totalWeight)).Nonempty :=
    ⟨(singletonFractionalColoring G).totalWeight, ⟨singletonFractionalColoring G, rfl⟩⟩
  apply le_csInf hnonempty
  rintro y ⟨χ, rfl⟩
  exact χ.totalWeight_nonneg

/-- Any feasible fractional coloring bounds the fractional chromatic number above. -/
theorem fractionalChromaticNumber_le_totalWeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (χ : FractionalColoring G) : fractionalChromaticNumber G ≤ χ.totalWeight := by
  unfold fractionalChromaticNumber
  have hb : BddBelow (Set.range (fun ψ : FractionalColoring G ↦ ψ.totalWeight)) := by
    refine ⟨0, ?_⟩
    rintro y ⟨ψ, rfl⟩
    exact ψ.totalWeight_nonneg
  exact csInf_le hb ⟨χ, rfl⟩

theorem fractionalChromaticNumber_le_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) : fractionalChromaticNumber G ≤ Fintype.card V := by
  simpa only [singletonFractionalColoring_totalWeight] using
    fractionalChromaticNumber_le_totalWeight (singletonFractionalColoring G)

end Hedetniemi
