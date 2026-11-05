import HedetniemiAsymptotically.BernoulliSetEvents
import HedetniemiAsymptotically.GraphMeasurability
import HedetniemiAsymptotically.IndependentSetEdges
import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs
namespace Hedetniemi
open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal Classical
/-- The probability that all required edges are present. -/
theorem binomialRandom_contains_edges {V : Type*} [Fintype V]
    (p : I) (S : Finset (Sym2 V)) (hS : ∀ e ∈ S, e ∈ Sym2.diagSetᶜ) :
    SimpleGraph.binomialRandom V p {G | (S : Set (Sym2 V)) ⊆ G.edgeSet} =
      (toNNReal p : ℝ≥0∞) ^ S.card := by
  rw [SimpleGraph.binomialRandom_eq_map, Measure.map_apply SimpleGraph.measurable_fromEdgeSet
    MeasurableSet.of_discrete]
  have heq : SimpleGraph.fromEdgeSet ⁻¹' {G | (S : Set (Sym2 V)) ⊆ G.edgeSet} =
      {E | (S : Set (Sym2 V)) ⊆ E} := by
    ext E
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, SimpleGraph.edgeSet_fromEdgeSet]
    constructor
    · exact fun h e he ↦ (h he).1
    · exact fun h e he ↦ ⟨h he, hS e he⟩
  rw [heq]
  exact setBernoulli_contains_finset _ p S hS
end Hedetniemi
