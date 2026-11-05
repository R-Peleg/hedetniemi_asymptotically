import HedetniemiAsymptotically.Graph

namespace Hedetniemi

/-- Relabel a proper coloring by an equivalence of palettes. -/
def recolor {V C D : Type*} {G : Graph V} (e : C ≃ D) (χ : G.Coloring C) : G.Coloring D :=
  ⟨fun v ↦ e (χ.val v), fun {_ _} h heq ↦ χ.property h (e.injective heq)⟩

@[simp] theorem recolor_apply {V C D : Type*} {G : Graph V} (e : C ≃ D)
    (χ : G.Coloring C) (v : V) : (recolor e χ).val v = e (χ.val v) := rfl

end Hedetniemi
