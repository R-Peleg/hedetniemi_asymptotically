import HedetniemiAsymptotically.LoopedGraph

namespace Hedetniemi

/-- Vertices at distance zero or two from the center, described by walks.
For a triangle-free simple graph this is disjoint from the neighbors of
the center. This description also handles disconnected graphs. -/
def EvenNear {V : Type*} (G : SimpleGraph V) (v w : V) : Prop :=
  w = v ∨ ∃ u, G.Adj v u ∧ G.Adj u w

/-- Every neighbor of a neighbor belongs to the even part of the radius-two ball. -/
theorem evenNear_of_adj_adj {V : Type*} {G : SimpleGraph V} {v u w : V}
    (hvu : G.Adj v u) (huw : G.Adj u w) : EvenNear G v w :=
  Or.inr ⟨u, hvu, huw⟩

/-- A vertex outside the radius-two ball cannot equal or be adjacent to
a neighbor of the center. -/
theorem far_not_loopedAdj_neighbor {V : Type*} {G : SimpleGraph V} {v x y : V}
    (hxe : ¬ EvenNear G v x) (hxn : ¬ G.Adj v x) (hy : G.Adj v y) :
    ¬ (loopedGraph G).Adj x y := by
  intro hxy
  rcases hxy with hxy | hxy
  · subst y
    exact hxn hy
  · exact hxe (evenNear_of_adj_adj hy hxy.symm)

end Hedetniemi
