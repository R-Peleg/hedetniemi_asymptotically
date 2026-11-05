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

end Hedetniemi
