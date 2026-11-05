import HedetniemiAsymptotically.SuitedColoring

namespace Hedetniemi

/-- Section 3: a primary color is robust at `v` if every map receiving that
color takes that value somewhere in the closed neighborhood of `v`. -/
def IsRobust {V C D : Type*} {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) (b : C) : Prop :=
  ∀ f, χ.val f = Sum.inl b →
    ∃ w, (w = v ∨ G.Adj v w) ∧ f w = b

/-- A map with a unique occurrence of a robust color locates that occurrence
in the closed neighborhood of every vertex where the color is robust. -/
theorem IsRobust.unique_support {V C D : Type*} {G : Graph V}
    {χ : (exponentialGraph G C).Coloring (C ⊕ D)} {v u : V} {b : C}
    (h : IsRobust χ v b) {f : V → C} (hf : χ.val f = Sum.inl b)
    (hsupport : ∀ w, f w = b → w = u) : u = v ∨ G.Adj v u := by
  obtain ⟨w, hw, hwb⟩ := h f hf
  simpa only [hsupport w hwb] using hw

end Hedetniemi
