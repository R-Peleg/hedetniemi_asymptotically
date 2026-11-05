import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-! Graphs in the paper may have loops, but have no multiple edges. -/
namespace Hedetniemi

/-- An undirected graph, with loops permitted. -/
structure Graph (V : Type*) where
  Adj : V → V → Prop
  symm : ∀ ⦃v w⦄, Adj v w → Adj w v

namespace Graph

variable {V W C : Type*}

/-- Proper colorings also make sense for a graph with loops: none can exist
if a loop is present. -/
def Coloring (G : Graph V) (C : Type*) :=
  {f : V → C // ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w}

/-- Regard a Mathlib simple graph as a graph allowing loops. -/
def ofSimpleGraph (G : SimpleGraph V) : Graph V := ⟨G.Adj, fun {_ _} h ↦ G.symm.symm _ _ h⟩

/-- Recover a simple graph when there are no loops. -/
def toSimpleGraph (G : Graph V) (h : ∀ v, ¬ G.Adj v v) : SimpleGraph V where
  Adj := G.Adj
  symm := ⟨fun _ _ h ↦ G.symm h⟩
  loopless := ⟨h⟩

end Graph
end Hedetniemi
