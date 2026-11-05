import HedetniemiAsymptotically.ExponentialGraph

namespace Hedetniemi

/-- Regard a bounded natural-valued map as a map to a finite palette. -/
def finiteMap {V : Type*} {c : ℕ} (f : V → ℕ) (hf : ∀ v, f v < c) : V → Fin c :=
  fun v ↦ ⟨f v, hf v⟩

/-- Passing to finite colors preserves and reflects co-properness. -/
theorem coProper_finiteMap_iff {V : Type*} {G : Graph V} {c : ℕ}
    {f g : V → ℕ} {hf : ∀ v, f v < c} {hg : ∀ v, g v < c} :
    CoProper G (finiteMap f hf) (finiteMap g hg) ↔ CoProper G f g := by
  constructor
  · intro h v w hvw heq
    exact h hvw (Fin.ext heq)
  · intro h v w hvw heq
    exact h hvw (congrArg Fin.val heq)

end Hedetniemi
