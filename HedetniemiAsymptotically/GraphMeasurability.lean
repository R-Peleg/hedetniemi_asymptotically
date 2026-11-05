import Mathlib.MeasureTheory.Constructions.SimpleGraph

namespace Hedetniemi
open MeasureTheory

/-- A graph on countably many vertices has measurable singleton events.
For finitely many vertices this also gives a discrete measurable space. -/
instance simpleGraph_measurableSingletonClass {V : Type*} [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) := by
  constructor
  intro G
  have heq : ({G} : Set (SimpleGraph V)) = SimpleGraph.Adj ⁻¹' {G.Adj} := by
    ext H
    simp only [Set.mem_singleton_iff, Set.mem_preimage, SimpleGraph.adj_inj]
  rw [heq]
  exact SimpleGraph.measurable_adj (MeasurableSet.singleton _)

end Hedetniemi
