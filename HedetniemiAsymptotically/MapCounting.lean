import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.BigOperators

/-! Elementary finite-map counts used in the paper's counting arguments. -/
namespace Hedetniemi

open Finset

/-- A union bound for maps whose image contains a prescribed color. -/
theorem card_maps_containing_color_le {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (b : C) :
    (univ.filter (fun f : V → C ↦ b ∈ Set.range f)).card ≤
      Fintype.card V * Fintype.card C ^ (Fintype.card V - 1) := by
  classical
  have heq : univ.filter (fun f : V → C ↦ b ∈ Set.range f) =
      univ.biUnion (fun v : V ↦ univ.filter (fun f : V → C ↦ f v = b)) := by
    ext f
    simp
  rw [heq]
  calc
    _ ≤ ∑ v : V, (univ.filter (fun f : V → C ↦ f v = b)).card :=
      card_biUnion_le
    _ = _ := by
      have hpi : (Fintype.piFinset fun _ : V ↦ (univ : Finset C)) = (univ : Finset (V → C)) := by
        ext f
        simp
      simp_rw [← hpi, Fintype.card_filter_piFinset_const_eq_of_mem univ _ (mem_univ b)]
      simp

/-- The number of maps onto a prescribed set depends only on its size. -/
theorem card_maps_with_image_eq {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (s t : Finset C) (hst : s.card = t.card) :
    (univ.filter (fun f : V → C ↦ univ.image f = s)).card =
      (univ.filter (fun f : V → C ↦ univ.image f = t)).card := by
  classical
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_map_finset_eq s t hst
  have hσ' : s.image σ = t := by simpa [map_eq_image] using hσ
  have hrange (f : V → C) : univ.image (σ ∘ f) = (univ.image f).image σ := by
    rw [image_image]
  apply card_bij (fun f _ ↦ σ ∘ f)
  · intro f hf
    simp only [mem_filter, mem_univ, true_and] at hf ⊢
    rw [hrange, hf, hσ']
  · intro f _ g _ hfg
    funext v
    exact σ.injective (congrFun hfg v)
  · intro g hg
    refine ⟨σ.symm ∘ g, ?_, ?_⟩
    · simp only [mem_filter, mem_univ, true_and] at hg ⊢
      apply (image_injective σ.injective)
      rw [← hrange]
      simpa [Function.comp_def, hσ'] using hg
    · funext v
      exact σ.apply_symm_apply (g v)

end Hedetniemi
