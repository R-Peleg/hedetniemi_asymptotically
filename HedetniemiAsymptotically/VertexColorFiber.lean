import HedetniemiAsymptotically.SuitedColoring
import Mathlib.Data.Fintype.Pi

namespace Hedetniemi

/-- The family `I(v,b)` in Lemma 5: maps colored `b` and taking value `b`
at the vertex `v`. -/
noncomputable def vertexColorFiber {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) (b : C) : Finset (V → C) := by
  classical
  exact Finset.univ.filter (fun f ↦ χ.val f = Sum.inl b ∧ f v = b)

@[simp] theorem mem_vertexColorFiber {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) (b : C) (f : V → C) :
    f ∈ vertexColorFiber χ v b ↔ χ.val f = Sum.inl b ∧ f v = b := by
  classical
  simp [vertexColorFiber]

end Hedetniemi
