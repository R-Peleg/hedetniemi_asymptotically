import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hedetniemi
open MeasureTheory
open scoped ENNReal Classical

/-- The expected number of events that occur is the sum of their probabilities. -/
theorem lintegral_card_filter_events {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (E : ι → Set Ω)
    (hE : ∀ i ∈ S, MeasurableSet (E i)) :
    ∫⁻ ω, ((S.filter (fun i ↦ ω ∈ E i)).card : ℝ≥0∞) ∂μ = ∑ i ∈ S, μ (E i) := by
  classical
  have hcount (ω : Ω) : ((S.filter (fun i ↦ ω ∈ E i)).card : ℝ≥0∞) =
      ∑ i ∈ S, (E i).indicator (1 : Ω → ℝ≥0∞) ω := by
    simp [Set.indicator_apply, Finset.sum_boole]
  simp_rw [hcount]
  rw [lintegral_finsetSum (f := fun i ↦ (E i).indicator (1 : Ω → ℝ≥0∞))
    S (fun i hi ↦ measurable_const.indicator (hE i hi))]
  exact Finset.sum_congr rfl (fun i hi ↦ lintegral_indicator_one (hE i hi))

end Hedetniemi
