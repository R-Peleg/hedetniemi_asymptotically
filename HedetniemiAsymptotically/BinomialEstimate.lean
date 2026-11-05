import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

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

/-- An exponential binomial bound suited to `k/n` near `0.285`. -/
theorem choose_le_exp_bound (n k : ℕ) (hk : k ≤ n) :
    (n.choose k : ℝ) ≤ Real.exp ((11 / 10 : ℝ) * n - (2 / 3 : ℝ) * (n - k : ℕ)) := by
  have h2 : Real.exp ((n - k : ℕ) * (2 / 3 : ℝ)) ≤ (2 : ℝ) ^ (n - k) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_nonneg _) exp_two_thirds_le_two _
  have h3 : (3 : ℝ) ^ n ≤ Real.exp ((n : ℝ) * (11 / 10)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) three_le_exp_eleven_tenths _
  have hm := (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (n.choose k))).trans
    ((choose_mul_two_pow_le_three_pow n k hk).trans h3)
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simpa [mul_comm] using hm

/-- Combine the binomial bound with `(1-p)^m ≤ exp(-pm)`. -/
theorem choose_mul_one_sub_pow_le_exp (n k m : ℕ) (hk : k ≤ n) (p : ℝ) (hp : p ≤ 1) :
    (n.choose k : ℝ) * (1 - p) ^ m ≤
      Real.exp ((11 / 10 : ℝ) * n - (2 / 3 : ℝ) * (n - k : ℕ) - p * m) := by
  have hbase : 1 - p ≤ Real.exp (-p) := by linarith [Real.add_one_le_exp (-p)]
  have hp0 : 0 ≤ 1 - p := sub_nonneg.mpr hp
  have hpow : (1 - p) ^ m ≤ Real.exp ((m : ℝ) * (-p)) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ hp0 hbase m
  calc
    _ ≤ Real.exp ((11 / 10 : ℝ) * n - (2 / 3 : ℝ) * (n - k : ℕ)) *
        Real.exp ((m : ℝ) * (-p)) :=
      mul_le_mul (choose_le_exp_bound n k hk) hpow (pow_nonneg hp0 m) (Real.exp_nonneg _)
    _ = _ := by
      rw [← Real.exp_add]
      congr 1
      ring

/-- A simple Taylor bound suffices for the final numerical probability comparison. -/
theorem exp_neg_two_lt_quarter : Real.exp (-2) < (1 / 4 : ℝ) := by
  have h := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at h
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_lt_one_div_of_lt (show (0 : ℝ) < 4 by norm_num)
    (lt_of_lt_of_le (show (4 : ℝ) < 5 by norm_num) h)

end Hedetniemi
