import HedetniemiAsymptotically.CyclePlacementProperties
import Mathlib.Combinatorics.SimpleGraph.Basic
import HedetniemiAsymptotically.GraphMeasurability
import HedetniemiAsymptotically.FiniteEventCount

namespace Hedetniemi
open MeasureTheory
open scoped ENNReal

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

/-- The expected number of present placements is the sum of their occurrence probabilities. -/
theorem lintegral_card_presentCyclePlacements {V : Type*} [Fintype V] [LinearOrder V]
    (μ : Measure (SimpleGraph V)) (m : ℕ) :
    ∫⁻ G, ((presentCyclePlacements G m).card : ℝ≥0∞) ∂μ =
      ∑ P : CyclePlacement V m,
        μ {G | ∀ e ∈ placeCycleEdges P.1.val P.1.property P.2.val, e ∈ G.edgeSet} := by
  classical
  unfold presentCyclePlacements
  simpa only [Set.mem_ofPred_eq] using
    (lintegral_card_filter_events μ (Finset.univ : Finset (CyclePlacement V m))
    (fun P ↦ {G | ∀ e ∈ placeCycleEdges P.1.val P.1.property P.2.val, e ∈ G.edgeSet})
    (fun _ _ ↦ .of_discrete))

end Hedetniemi
