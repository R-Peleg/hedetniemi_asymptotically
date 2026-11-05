import HedetniemiAsymptotically.NuMap
import HedetniemiAsymptotically.FiniteMap

namespace Hedetniemi

/-- The `ν` construction with both image colors in the finite palette. -/
noncomputable def finiteNuMap {V : Type*} (G : SimpleGraph V) (v : V) {c : ℕ}
    (r σ : Fin c) : V → Fin c :=
  finiteMap (nuMap G v r.val σ.val) (nuMap_lt G v r.isLt σ.isLt)

@[simp] theorem finiteNuMap_val {V : Type*} (G : SimpleGraph V) (v : V) {c : ℕ}
    (r σ : Fin c) (w : V) :
    (finiteNuMap G v r σ w).val = nuMap G v r.val σ.val w := rfl

end Hedetniemi
