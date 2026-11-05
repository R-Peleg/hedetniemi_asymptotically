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

end Hedetniemi
