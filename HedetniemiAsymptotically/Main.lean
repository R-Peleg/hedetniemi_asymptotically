import HedetniemiAsymptotically.ElZaharSauer
import HedetniemiAsymptotically.SuitedColoring
import HedetniemiAsymptotically.RobustColor
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

/-- The clique step in Lemma 5: if each vertex in a set supports a map with
one occurrence of `b`, and `b` is robust at each vertex, the set is a clique.
The counting part of Lemma 5 will supply these two hypotheses. -/
theorem robust_supports_form_clique {V C D : Type*} {G : Graph V}
    {χ : (exponentialGraph G C).Coloring (C ⊕ D)} {b : C} {S : Set V}
    (hrobust : ∀ v ∈ S, IsRobust χ v b)
    (hsupport : ∀ u ∈ S, ∃ f : V → C,
      χ.val f = Sum.inl b ∧ ∀ w, f w = b → w = u) :
    ∀ v ∈ S, ∀ u ∈ S, v ≠ u → G.Adj v u := by
  intro v hv u hu hne
  obtain ⟨f, hf, hfu⟩ := hsupport u hu
  rcases (hrobust v hv).unique_support hf hfu with heq | hadj
  · exact (hne heq.symm).elim
  · exact hadj

end Hedetniemi
