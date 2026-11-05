import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Exponential

namespace Hedetniemi

/-- Bounding one term of `(1+2)^n` gives a binomial coefficient estimate
which is sharper than `choose n k ≤ 2^n` at the parameters of Lemma 7. -/
theorem choose_mul_two_pow_le_three_pow (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) * (2 : ℝ) ^ (n - k) ≤ (3 : ℝ) ^ n := by
  calc
    _ = (1 : ℝ) ^ k * 2 ^ (n - k) * (n.choose k : ℝ) := by simp [mul_comm]
    _ ≤ ∑ m ∈ Finset.range (n + 1),
        (1 : ℝ) ^ m * 2 ^ (n - m) * (n.choose m : ℝ) :=
      Finset.single_le_sum
        (f := fun m ↦ (1 : ℝ) ^ m * 2 ^ (n - m) * (n.choose m : ℝ))
        (fun m _ ↦ by positivity)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
    _ = ((1 : ℝ) + 2) ^ n := (add_pow 1 2 n).symm
    _ = (3 : ℝ) ^ n := by norm_num

/-- A rational upper bound on the exponential used in the binomial estimate. -/
theorem exp_two_thirds_le_two : Real.exp ((2 : ℝ) / 3) ≤ 2 := by
  have h := Real.exp_lt_two_add_div_two_sub
    (x := (2 : ℝ) / 3) (by norm_num) (by norm_num)
  norm_num at h
  exact h.le

/-- A short Taylor sum bounds `exp(11/10)` from below by three. -/
theorem three_le_exp_eleven_tenths : (3 : ℝ) ≤ Real.exp (11 / 10) := by
  have h := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 11 / 10 by norm_num) 7
  norm_num [Finset.sum_range_succ] at h
  exact le_trans (by norm_num) h

end Hedetniemi
