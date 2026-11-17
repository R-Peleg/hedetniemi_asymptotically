import HedetniemiAsymptotically.EvenNear

namespace Hedetniemi

/-- The maps `μ_r` in Lemma 6. Finite colors are indexed from zero: the
first two blocks are `[0,q)` and `[q,2q)`. -/
noncomputable def muMap {V : Type*} (G : SimpleGraph V) (v : V) (q r : ℕ):
    V × Fin q → ℕ := by
  classical
  exact fun x ↦ if EvenNear G v x.1 then x.2.val
    else if G.Adj v x.1 then q + x.2.val else r

/-- Small helper lemmas for the case splitting of muMap -/
lemma muMap_of_EvenNear {V : Type*} {G : SimpleGraph V} {v : V} {q r : ℕ} {x: V × Fin q}
    (hEvenNear: EvenNear G v x.1) :
    (muMap G v q r) x = x.2 := by
  unfold muMap
  simp only [ite_eq_left hEvenNear]

lemma muMap_of_not_EvenNear_ge {V : Type*} {G : SimpleGraph V} {v : V} {q r : ℕ} {x: V × Fin q}
    (hr : r ≥ q)
    (hnot_EvenNear: ¬ EvenNear G v x.1) :
    (muMap G v q r) x ≥ q := by
  unfold muMap
  split_ifs <;> simp only [ge_iff_le, le_add_iff_nonneg_right, zero_le, hr]

lemma muMap_of_Adj {V : Type*} {G : SimpleGraph V} {v : V} {q r : ℕ} {x: V × Fin q}
    (hNoEvenNear : ¬EvenNear G v x.1) (hAdj: G.Adj v x.1) :
    (muMap G v q r) x = q + x.2.val := by
  unfold muMap
  simp only [ite_eq_right hNoEvenNear, ite_eq_left hAdj]

lemma muMap_of_far {V : Type*} {G : SimpleGraph V} {v : V} {q r : ℕ} {x: V × Fin q}
    (hNoEvenNear : ¬EvenNear G v x.1) (hAdj: ¬G.Adj v x.1) :
    (muMap G v q r) x = r := by
  unfold muMap
  simp only [ite_eq_right hNoEvenNear, ite_eq_right hAdj]

/-- All values of `μ_r` lie in the palette when both low blocks and `r` do. -/
theorem muMap_lt {V : Type*} (G : SimpleGraph V) (v : V) {q r c : ℕ}
    (hq : 2 * q ≤ c) (hr : r < c) (x : V × Fin q) : muMap G v q r x < c := by
  have hi := x.2.isLt
  unfold muMap
  split_ifs <;> omega

/-- A value outside the first two blocks must be the parameter `r`. -/
theorem muMap_eq_parameter_of_ge {V : Type*} (G : SimpleGraph V) (v : V) {q r : ℕ}
    (x : V × Fin q) (hx : 2 * q ≤ muMap G v q r x) : muMap G v q r x = r := by
  have hi := x.2.isLt
  unfold muMap at hx ⊢
  split_ifs at hx ⊢ <;> omega

end Hedetniemi
