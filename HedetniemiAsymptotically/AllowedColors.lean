import HedetniemiAsymptotically.VertexColorFiber

namespace Hedetniemi

/-- The colors not excluded at `v` by a large fiber. Their number is `s(v)`
in the proof of Lemma 5. -/
noncomputable def allowedColors {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) : Finset C := by
  classical
  exact Finset.univ.filter (fun b ↦ (vertexColorFiber χ v b).card ≤
    Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2))

@[simp] theorem mem_allowedColors {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) (b : C) :
    b ∈ allowedColors χ v ↔ (vertexColorFiber χ v b).card ≤
      Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) := by
  classical
  simp [allowedColors]

end Hedetniemi
