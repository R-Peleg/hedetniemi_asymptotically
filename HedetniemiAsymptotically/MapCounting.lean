import Mathlib.Logic.Equiv.Fintype
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

/-- Partition a finite family of maps according to its exact image. -/
theorem card_maps_with_images {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (A : Finset (Finset C)) :
    (univ.filter (fun f : V → C ↦ univ.image f ∈ A)).card =
      ∑ s ∈ A, (univ.filter (fun f : V → C ↦ univ.image f = s)).card := by
  classical
  trans ∑ s ∈ A,
    ((univ.filter (fun f : V → C ↦ univ.image f ∈ A)).filter
      (fun f ↦ univ.image f = s)).card
  · exact card_eq_sum_card_fiberwise (f := fun f : V → C ↦ univ.image f)
      (fun f hf ↦ (mem_filter.mp hf).2)
  apply sum_congr rfl
  intro s hs
  congr 1
  ext f
  simp only [mem_filter, mem_univ, true_and]
  exact and_iff_right_of_imp (fun h ↦ h ▸ hs)

/-- For uniform set families, comparing the numbers of images also compares
the numbers of maps having those images. -/
theorem card_maps_with_images_le {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] {A B : Finset (Finset C)} {k : ℕ}
    (hA : ∀ s ∈ A, s.card = k) (hB : ∀ s ∈ B, s.card = k)
    (hcard : A.card ≤ B.card) :
    (univ.filter (fun f : V → C ↦ univ.image f ∈ A)).card ≤
      (univ.filter (fun f : V → C ↦ univ.image f ∈ B)).card := by
  classical
  by_cases hBempty : B = ∅
  · have hAempty : A = ∅ := card_eq_zero.mp (by simpa [hBempty] using hcard)
    simp [hAempty, hBempty]
  obtain ⟨t, ht⟩ := nonempty_iff_ne_empty.mpr hBempty
  have hcount (F : Finset (Finset C)) (hF : ∀ s ∈ F, s.card = k) :
      (univ.filter (fun f : V → C ↦ univ.image f ∈ F)).card =
        F.card * (univ.filter (fun f : V → C ↦ univ.image f = t)).card := by
    rw [card_maps_with_images]
    calc
      _ = ∑ _s ∈ F, (univ.filter (fun f : V → C ↦ univ.image f = t)).card := by
        apply sum_congr rfl
        intro s hs
        exact card_maps_with_image_eq s t ((hF s hs).trans (hB t ht).symm)
      _ = _ := by simp
  rw [hcount A hA, hcount B hB]
  exact Nat.mul_le_mul_right _ hcard

/-- Fixing two distinct coordinates leaves exactly `|C|^(|V|-2)` maps. -/
theorem card_maps_fixing_two {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (v w : V) (hvw : v ≠ w) (a b : C) :
    (univ.filter (fun f : V → C ↦ f v = a ∧ f w = b)).card =
      Fintype.card C ^ (Fintype.card V - 2) := by
  classical
  let s : V → Finset C := Function.update (fun _ ↦ univ) v {a}
  have hfirst : univ.filter (fun f : V → C ↦ f v = a) = Fintype.piFinset s := by
    symm
    simpa [s] using Fintype.piFinset_update_singleton_eq_filter_piFinset_eq
      (fun _ : V ↦ (univ : Finset C)) v (mem_univ a)
  have hcard : (fun j ↦ (s j).card) =
      Function.update (fun _ : V ↦ Fintype.card C) v 1 := by
    funext j
    by_cases hj : j = v <;> simp [s, hj, Function.update_of_ne]
  calc
    _ = ((univ.filter (fun f : V → C ↦ f v = a)).filter (fun f ↦ f w = b)).card := by
      rw [filter_filter]
    _ = ∏ j ∈ univ.erase w, (s j).card := by
      rw [hfirst]
      exact Fintype.card_filter_piFinset_eq_of_mem s w (by simp [s, hvw.symm])
    _ = _ := by
      rw [hcard, prod_update_of_mem (by simp [hvw])]
      simp [sdiff_singleton_eq_erase, card_erase_of_mem, hvw, Nat.sub_sub]

/-- After fixing one coordinate, maps that share any value with a prescribed
map at some other coordinate number at most `|V|² * |C|^(|V|-2)`. -/
theorem card_maps_with_secondary_match_le {V C : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] (v : V) (b : C) (f : V → C) :
    (univ.filter (fun g : V → C ↦ g v = b ∧
      ∃ w, w ≠ v ∧ ∃ u, g w = f u)).card ≤
      Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) := by
  classical
  let T (w u : V) := univ.filter (fun g : V → C ↦ g v = b ∧ g w = f u)
  calc
    _ ≤ ((univ.erase v).biUnion (fun w ↦ univ.biUnion (T w))).card := by
      apply card_le_card
      intro g hg
      obtain ⟨hgv, w, hw, u, hgu⟩ := (mem_filter.mp hg).2
      exact mem_biUnion.mpr ⟨w, mem_erase.mpr ⟨hw, mem_univ _⟩,
        mem_biUnion.mpr ⟨u, mem_univ _, mem_filter.mpr ⟨mem_univ _, hgv, hgu⟩⟩⟩
    _ ≤ ∑ w ∈ univ.erase v, (univ.biUnion (T w)).card := card_biUnion_le
    _ ≤ ∑ _w ∈ univ.erase v,
        Fintype.card V * Fintype.card C ^ (Fintype.card V - 2) := by
      apply sum_le_sum
      intro w hw
      calc
        _ ≤ ∑ u : V, (T w u).card := card_biUnion_le
        _ = _ := by
          have hcount (u : V) : (T w u).card = Fintype.card C ^ (Fintype.card V - 2) :=
            card_maps_fixing_two v w (mem_erase.mp hw).1.symm b (f u)
          simp_rw [hcount]
          simp
    _ ≤ _ := by
      rw [sum_const_nat (fun _ _ ↦ rfl)]
      calc
        _ ≤ Fintype.card V *
            (Fintype.card V * Fintype.card C ^ (Fintype.card V - 2)) :=
          Nat.mul_le_mul_right _ (by simp)
        _ = _ := by rw [pow_two, Nat.mul_assoc]

end Hedetniemi
