import Mathlib.Probability.Distributions.SetBernoulli

namespace Hedetniemi
open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped ENNReal

/-- The probability that a finite set of eligible elements is present. -/
theorem setBernoulli_contains_finset {ι : Type*} (u : Set ι) (p : I) (S : Finset ι)
    (hS : ∀ i ∈ S, i ∈ u) :
    setBernoulli u p {E | (S : Set ι) ⊆ E} = (toNNReal p : ℝ≥0∞) ^ S.card := by
  classical
  rw [setBernoulli_apply']
  have heq : ((fun f : ι → Prop ↦ {i | f i}) ⁻¹' {E | (S : Set ι) ⊆ E}) =
      Set.pi (S : Set ι) (fun _ ↦ {P : Prop | P}) := by
    ext f
    simp [Set.subset_def, Set.mem_pi]
  rw [heq, Measure.infinitePi_pi _ (fun _ _ ↦ MeasurableSet.of_discrete)]
  calc
    _ = ∏ _i ∈ S, (toNNReal p : ℝ≥0∞) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [bernoulliMeasure_apply p MeasurableSet.of_discrete]
      simp [hS i hi]
    _ = _ := by simp

/-- The probability that a finite set of eligible elements is absent. -/
theorem setBernoulli_avoids_finset {ι : Type*} (u : Set ι) (p : I) (S : Finset ι)
    (hS : ∀ i ∈ S, i ∈ u) :
    setBernoulli u p {E | Disjoint (S : Set ι) E} = (toNNReal (σ p) : ℝ≥0∞) ^ S.card := by
  classical
  rw [setBernoulli_apply']
  have heq : ((fun f : ι → Prop ↦ {i | f i}) ⁻¹' {E | Disjoint (S : Set ι) E}) =
      Set.pi (S : Set ι) (fun _ ↦ {P : Prop | ¬ P}) := by
    ext f
    simp [Set.disjoint_left, Set.mem_pi]
  rw [heq, Measure.infinitePi_pi _ (fun _ _ ↦ MeasurableSet.of_discrete)]
  calc
    _ = ∏ _i ∈ S, (toNNReal (σ p) : ℝ≥0∞) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [bernoulliMeasure_apply p MeasurableSet.of_discrete]
      simp [hS i hi]
    _ = _ := by simp

end Hedetniemi
