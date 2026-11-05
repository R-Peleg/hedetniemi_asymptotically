import HedetniemiAsymptotically.Graph

namespace Hedetniemi

variable {V C : Type*}

/-- Two maps are co-proper if their values differ across every edge. -/
def CoProper (G : Graph V) (f g : V → C) : Prop :=
  ∀ ⦃v w⦄, G.Adj v w → f v ≠ g w

theorem coProper_symm {G : Graph V} {f g : V → C}
    (h : CoProper G f g) : CoProper G g f := by
  intro v w hvw heq
  exact h (G.symm hvw) heq.symm

/-- The exponential graph has all maps to the color type as vertices.
Loops are retained, as in Section 2 of the paper. -/
def exponentialGraph (G : Graph V) (C : Type*) : Graph (V → C) where
  Adj := CoProper G
  symm := fun {_ _} h ↦ coProper_symm h

/-- A loop in the exponential graph is exactly a proper coloring of the base. -/
theorem exponentialGraph_loop_iff (G : Graph V) (f : V → C) :
    (exponentialGraph G C).Adj f f ↔ ∀ ⦃v w⦄, G.Adj v w → f v ≠ f w :=
  Iff.rfl

end Hedetniemi
