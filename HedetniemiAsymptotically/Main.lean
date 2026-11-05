import HedetniemiAsymptotically.ElZaharSauer
import HedetniemiAsymptotically.SuitedColoring
import Mathlib.Logic.Equiv.Fintype

/-! Proofs appearing in He and Wigderson, *Hedetniemi's conjecture is
asymptotically false* (arXiv:1906.06783v3). -/
namespace Hedetniemi

/-- Lemma 3. A coloring with finitely many primary colors can be made suited
by permuting its colors. Taking `C = Fin c` and `D = Fin t` gives the paper's
`(c+t)`-coloring statement. -/
theorem exists_suited_coloring {V C D : Type*} [Finite C] (G : Graph V)
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) :
    ∃ χ' : (exponentialGraph G C).Coloring (C ⊕ D), IsSuited χ' := by
  classical
  have hinj : Function.Injective (fun b : C ↦ χ.val (fun _ ↦ b)) := by
    intro b d heq
    by_contra hne
    exact χ.property (fun {_ _} _ ↦ hne) heq
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun b : C ↦ χ.val (fun _ ↦ b)) Sum.inl hinj Sum.inl_injective
  let χ' : (exponentialGraph G C).Coloring (C ⊕ D) :=
    ⟨fun f ↦ σ (χ.val f), fun {_ _} h heq ↦ χ.property h (σ.injective heq)⟩
  refine ⟨χ', ?_⟩
  intro f b hfb
  by_contra hb
  have hadj : (exponentialGraph G C).Adj f (fun _ ↦ b) := by
    intro v w _ heq
    exact hb ⟨v, heq⟩
  apply χ'.property hadj
  exact hfb.trans (hσ b).symm

end Hedetniemi
