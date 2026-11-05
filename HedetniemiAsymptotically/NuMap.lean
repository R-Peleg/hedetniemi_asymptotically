import HedetniemiAsymptotically.Graph

namespace Hedetniemi

/-- The maps `ν_s` of Lemma 6 take the color `r_s` in the closed
neighborhood of the center and the color `σ_s` elsewhere. -/
noncomputable def nuMap {V : Type*} (G : SimpleGraph V) (v : V) (r σ : ℕ) : V → ℕ := by
  classical
  exact fun w ↦ if w = v ∨ G.Adj v w then r else σ

/-- The value on the entire closed neighborhood is `r`. -/
theorem nuMap_eq_on_closed {V : Type*} {G : SimpleGraph V} {v w : V} {r σ : ℕ}
    (hw : w = v ∨ G.Adj v w) : nuMap G v r σ w = r := by
  classical
  simp [nuMap, hw]

end Hedetniemi
