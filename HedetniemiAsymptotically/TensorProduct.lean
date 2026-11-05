import HedetniemiAsymptotically.Graph

namespace Hedetniemi

/-- The tensor (categorical) product, retaining any loops. -/
def tensorProduct {V W : Type*} (G : Graph V) (H : Graph W) : Graph (V × W) where
  Adj x y := G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := fun {_ _} h ↦ ⟨G.symm h.1, H.symm h.2⟩

/-- The first projection pulls a coloring back to the tensor product. -/
def tensorColoringLeft {V W C : Type*} {G : Graph V} (H : Graph W)
    (f : G.Coloring C) : (tensorProduct G H).Coloring C :=
  ⟨fun x ↦ f.val x.1, fun {_ _} h ↦ f.property h.1⟩

/-- The second projection pulls a coloring back to the tensor product. -/
def tensorColoringRight {V W C : Type*} (G : Graph V) {H : Graph W}
    (f : H.Coloring C) : (tensorProduct G H).Coloring C :=
  ⟨fun x ↦ f.val x.2, fun {_ _} h ↦ f.property h.2⟩

end Hedetniemi
