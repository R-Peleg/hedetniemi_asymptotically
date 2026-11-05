import HedetniemiAsymptotically.RobustColor

namespace Hedetniemi

/-- The finite set of primary colors robust at a given vertex. -/
noncomputable def robustColors {V C D : Type*} [Fintype C] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) : Finset C := by
  classical
  exact Finset.univ.filter (IsRobust χ v)

@[simp] theorem mem_robustColors {V C D : Type*} [Fintype C] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) (b : C) :
    b ∈ robustColors χ v ↔ IsRobust χ v b := by
  classical
  simp [robustColors]

end Hedetniemi
