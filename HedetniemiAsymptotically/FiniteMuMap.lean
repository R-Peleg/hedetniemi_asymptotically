import HedetniemiAsymptotically.MuMap
import HedetniemiAsymptotically.FiniteMap

namespace Hedetniemi

/-- The `μ` construction with its range recorded in `Fin c`. -/
noncomputable def finiteMuMap {V : Type*} (G : SimpleGraph V) (v : V) {q c : ℕ}
    (hq : 2 * q ≤ c) (r : Fin c) : V × Fin q → Fin c :=
  finiteMap (muMap G v q r.val) (muMap_lt G v hq r.isLt)

@[simp] theorem finiteMuMap_val {V : Type*} (G : SimpleGraph V) (v : V) {q c : ℕ}
    (hq : 2 * q ≤ c) (r : Fin c) (x : V × Fin q) :
    (finiteMuMap G v hq r x).val = muMap G v q r.val x := rfl

end Hedetniemi
