import HedetniemiAsymptotically.LoopedGraph

namespace Hedetniemi

/-- The strong product of two simple graphs. Coordinates are equal or adjacent,
and the two product vertices must be distinct. -/
def strongProduct {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) :
    SimpleGraph (V × W) where
  Adj x y := (loopedGraph G).Adj x.1 y.1 ∧ (loopedGraph H).Adj x.2 y.2 ∧ x ≠ y
  symm := ⟨fun _ _ h ↦ ⟨(loopedGraph G).symm h.1,
    (loopedGraph H).symm h.2.1, h.2.2.symm⟩⟩
  loopless := ⟨fun _ h ↦ h.2.2 rfl⟩

/-- An edge in a strong product projects to equality or an edge in the
first factor. This is the property needed for exponential lifting. -/
theorem strongProduct_adj_left {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x y : V × W} (h : (strongProduct G H).Adj x y) :
    x.1 = y.1 ∨ G.Adj x.1 y.1 := h.1

/-- If an edge keeps the second coordinate fixed, the first coordinates
must be adjacent, since equality in both coordinates is forbidden. -/
theorem strongProduct_adj_of_snd_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {x y : V × W} (h : (strongProduct G H).Adj x y) (hxy : x.2 = y.2) :
    G.Adj x.1 y.1 := by
  rcases h.1 with heq | hadj
  · exact (h.2.2 (Prod.ext heq hxy)).elim
  · exact hadj

end Hedetniemi
