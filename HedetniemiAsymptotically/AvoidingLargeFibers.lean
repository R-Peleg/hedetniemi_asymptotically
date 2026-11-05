import HedetniemiAsymptotically.AllowedColors
import Mathlib.Data.Fintype.BigOperators

namespace Hedetniemi

/-- The family `S` of Lemma 5: at each vertex the chosen value avoids
the colors whose vertex/color fibers are large. -/
noncomputable def avoidingLargeFibers {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) : Finset (V → C) :=
  Fintype.piFinset (allowedColors χ)

@[simp] theorem mem_avoidingLargeFibers {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (f : V → C) :
    f ∈ avoidingLargeFibers χ ↔ ∀ v, (vertexColorFiber χ v (f v)).card ≤
      Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) := by
  classical
  simp [avoidingLargeFibers, Fintype.mem_piFinset]

/-- Independent choices of the allowed colors give the product formula
for the size of the avoiding family. -/
theorem card_avoidingLargeFibers {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) :
    (avoidingLargeFibers χ).card = ∏ v, (allowedColors χ v).card :=
  Fintype.card_piFinset _

end Hedetniemi
