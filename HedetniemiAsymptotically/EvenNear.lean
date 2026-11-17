import HedetniemiAsymptotically.LoopedGraph
import HedetniemiAsymptotically.HighGirth

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

/-- The same exclusion holds for the entire closed neighborhood. -/
theorem far_not_loopedAdj_closed {V : Type*} {G : SimpleGraph V} {v x y : V}
    (hxe : ¬ EvenNear G v x) (hxn : ¬ G.Adj v x) (hy : y = v ∨ G.Adj v y) :
    ¬ (loopedGraph G).Adj x y := by
  rcases hy with rfl | hy
  · intro hxy
    rcases hxy with hxy | hxy
    · exact hxe (Or.inl hxy)
    · exact hxn hxy.symm
  · exact far_not_loopedAdj_neighbor hxe hxn hy


/-- The even part of a radius-two ball is independent when the girth is at least six. -/
theorem evenNear_not_adj_of_six_le_egirth {V : Type*} {G : SimpleGraph V}
    (hG : 6 ≤ G.egirth) (v : V) {g h : V}
    (hg : EvenNear G v g) (hh : EvenNear G v h) : ¬ G.Adj g h := by
  intro hgh
  rcases hg with rfl | ⟨a, hva, hag⟩
  · rcases hh with rfl | ⟨b, hvb, hbh⟩
    · exact hgh.ne rfl
    · exact no_triangle_of_six_le_egirth hG hvb hbh hgh.symm
  · rcases hh with rfl | ⟨b, hvb, hbh⟩
    · exact no_triangle_of_six_le_egirth hG hva hag hgh
    · exact no_five_walk_of_six_le_egirth hG hva hag hgh hbh.symm hvb.symm

end Hedetniemi
