import HedetniemiAsymptotically.Graph

namespace Hedetniemi

/-- The graph `G°` obtained by adding a loop at every vertex of a simple graph. -/
def loopedGraph {V : Type*} (G : SimpleGraph V) : Graph V where
  Adj v w := v = w ∨ G.Adj v w
  symm := fun {_ _} h ↦ h.elim (fun h ↦ Or.inl h.symm)
    (fun h ↦ Or.inr (G.symm.symm _ _ h))

@[simp] theorem loopedGraph_loop {V : Type*} (G : SimpleGraph V) (v : V) :
    (loopedGraph G).Adj v v := Or.inl rfl

end Hedetniemi
