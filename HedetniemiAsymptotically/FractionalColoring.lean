import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace Hedetniemi

/-- A fractional coloring assigns nonnegative weights to independent vertex
sets so that every vertex is covered with total weight at least one. -/
structure FractionalColoring {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) where
  weight : Finset V → ℝ
  nonneg : ∀ S, 0 ≤ weight S
  independent : ∀ S : Finset V, ¬ G.IsIndepSet (S : Set V) → weight S = 0
  cover : ∀ v, 1 ≤ ∑ S ∈ Finset.univ.filter (fun S : Finset V ↦ v ∈ S), weight S

/-- The total weight of a fractional coloring. -/
def FractionalColoring.totalWeight {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (χ : FractionalColoring G) : ℝ := ∑ S, χ.weight S

theorem FractionalColoring.totalWeight_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (χ : FractionalColoring G) : 0 ≤ χ.totalWeight :=
  Finset.sum_nonneg (fun S _ ↦ χ.nonneg S)

end Hedetniemi
