import HedetniemiAsymptotically.CyclePlacementProperties
import Mathlib.Combinatorics.SimpleGraph.Basic

namespace Hedetniemi

/-- The canonical cycle placements whose edges are all present in a graph. -/
noncomputable def presentCyclePlacements {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (m : ℕ) : Finset (CyclePlacement V m) := by
  classical
  exact Finset.univ.filter (fun P ↦
    ∀ e ∈ placeCycleEdges P.1.val P.1.property P.2.val, e ∈ G.edgeSet)

@[simp] theorem mem_presentCyclePlacements {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {m : ℕ} (P : CyclePlacement V m) :
    P ∈ presentCyclePlacements G m ↔
      ∀ e ∈ placeCycleEdges P.1.val P.1.property P.2.val, e ∈ G.edgeSet := by
  classical
  simp [presentCyclePlacements]

end Hedetniemi
