import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

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

end Hedetniemi
