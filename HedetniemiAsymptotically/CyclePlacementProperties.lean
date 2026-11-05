import HedetniemiAsymptotically.CyclePlacement
import HedetniemiAsymptotically.PlaceCycleEdges
import HedetniemiAsymptotically.CycleTemplateProperties

namespace Hedetniemi

/-- Any cyclic ordering of distinct vertices is represented by a canonical placement. -/
theorem exists_cyclePlacement {V : Type*} [LinearOrder V] {m : ℕ}
    (f : Fin (m + 3) → V) (hf : Function.Injective f) :
    ∃ P : CyclePlacement V m,
      P.1.val = Finset.univ.image f ∧
      placeCycleEdges P.1.val P.1.property P.2.val =
        Finset.univ.image (fun i ↦ s(f i, f (i + 1))) := by
  classical
  let S := Finset.univ.image f
  have hS : S.card = m + 3 := by
    rw [Finset.card_image_of_injective _ hf]
    simp
  let g : Fin (m + 3) → S := fun i ↦ ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩
  have hg : Function.Bijective g := by
    constructor
    · intro i j hij
      exact hf (congrArg Subtype.val hij)
    · intro x
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp x.property
      exact ⟨i, Subtype.ext hi⟩
  let e := Equiv.ofBijective g hg
  let σ : Equiv.Perm (Fin (m + 3)) := e.trans (S.orderIsoOfFin hS).toEquiv.symm
  have hσ (i : Fin (m + 3)) : S.orderEmbOfFin hS (σ i) = f i := by
    change ((S.orderIsoOfFin hS) ((S.orderIsoOfFin hS).symm (e i))).val = f i
    rw [OrderIso.apply_symm_apply]
    rfl
  refine ⟨⟨⟨S, hS⟩, ⟨cycleEdges σ, Finset.mem_image.mpr
    ⟨σ, Finset.mem_univ _, rfl⟩⟩⟩, rfl, ?_⟩
  change (cycleEdges σ).image (Sym2.map (S.orderEmbOfFin hS)) = _
  rw [cycleEdges, Finset.image_image]
  congr 1
  funext i
  simp only [Function.comp_apply, Sym2.map_mk, hσ]

/-- Placed templates have the right edge count and no loops. -/
theorem cyclePlacement_properties {V : Type*} [LinearOrder V] {m : ℕ}
    (P : CyclePlacement V m) :
    (placeCycleEdges P.1.val P.1.property P.2.val).card = m + 3 ∧
      ∀ e ∈ placeCycleEdges P.1.val P.1.property P.2.val, ¬ e.IsDiag := by
  obtain ⟨hcard, hdiag⟩ := cycleTemplate_properties P.2.property
  refine ⟨(card_placeCycleEdges _ _ _).trans hcard, ?_⟩
  intro e he
  obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
  rw [Sym2.isDiag_map (P.1.val.orderEmbOfFin P.1.property).injective]
  exact hdiag d hd

end Hedetniemi
