import HedetniemiAsymptotically.ElZaharSauer
import HedetniemiAsymptotically.SuitedColoring
import HedetniemiAsymptotically.RobustColor
import HedetniemiAsymptotically.IndependentSet
import HedetniemiAsymptotically.MapCounting
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.SetFamily.KruskalKatona

/-! Proofs appearing in He and Wigderson, *Hedetniemi's conjecture is
asymptotically false* (arXiv:1906.06783v3). -/
namespace Hedetniemi

/-- The reduction in Lemma 4: maps in an independent family have intersecting
images. The nonempty vertex hypothesis also handles comparison of a map
with itself. -/
theorem independent_maps_images_intersect {V C : Type*} [Nonempty V]
    {G : Graph V} {I : Set (V → C)}
    (hI : (exponentialGraph G C).IsIndependent I)
    {f g : V → C} (hf : f ∈ I) (hg : g ∈ I) :
    ∃ v w, f v = g w := by
  classical
  by_cases hfg : f = g
  · obtain ⟨v⟩ := ‹Nonempty V›
    exact ⟨v, v, congrFun hfg v⟩
  · by_contra h
    apply hI hf hg hfg
    intro v w _ heq
    exact h ⟨v, w, heq⟩

/-- The Erdős–Ko–Rado step in Lemma 4, applied to one image-size layer. -/
theorem independent_image_layer_card_le {V : Type*} [Fintype V] [Nonempty V]
    {c k : ℕ} {G : Graph V} (I : Finset (V → Fin c))
    (hI : (exponentialGraph G (Fin c)).IsIndependent (I : Set (V → Fin c)))
    (hk : k ≤ c / 2) :
    ((I.image (fun f ↦ Finset.univ.image f)).filter (fun s ↦ s.card = k)).card ≤
      (c - 1).choose (k - 1) := by
  classical
  apply Finset.erdos_ko_rado _ _ hk
  · intro s hs t ht
    obtain ⟨hs, _⟩ := Finset.mem_filter.mp hs
    obtain ⟨ht, _⟩ := Finset.mem_filter.mp ht
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨v, w, hvw⟩ := independent_maps_images_intersect hI hf hg
    exact Finset.not_disjoint_iff.mpr ⟨f v,
      Finset.mem_image.mpr ⟨v, Finset.mem_univ _, rfl⟩,
      Finset.mem_image.mpr ⟨w, Finset.mem_univ _, hvw.symm⟩⟩
  · intro s hs
    exact (Finset.mem_filter.mp hs).2

/-- The weighted-layer step of Lemma 4: a layer has no more maps than the
same layer of the family of all maps containing one fixed color. -/
theorem independent_map_layer_card_le {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] {c k : ℕ} {G : Graph V} (I : Finset (V → Fin c))
    (hI : (exponentialGraph G (Fin c)).IsIndependent (I : Set (V → Fin c)))
    (b : Fin c) (hkpos : 1 ≤ k) (hk : k ≤ c / 2) :
    (I.filter (fun f ↦ (Finset.univ.image f).card = k)).card ≤
      (Finset.univ.filter (fun f : V → Fin c ↦
        b ∈ Set.range f ∧ (Finset.univ.image f).card = k)).card := by
  classical
  let A := (I.image (fun f ↦ Finset.univ.image f)).filter (fun s ↦ s.card = k)
  let B := ((Finset.univ : Finset (Fin c)).powersetCard k).filter (fun s ↦ {b} ⊆ s)
  have hBcard : B.card = (c - 1).choose (k - 1) := by
    simpa [B] using Finset.card_filter_powersetCard_subset
      ({b} : Finset (Fin c)) Finset.univ k (by simp) (by simpa using hkpos)
  have hcard : A.card ≤ B.card := by
    rw [hBcard]
    exact independent_image_layer_card_le I hI hk
  calc
    _ ≤ (Finset.univ.filter (fun f : V → Fin c ↦ Finset.univ.image f ∈ A)).card := by
      apply Finset.card_le_card
      intro f hf
      obtain ⟨hfI, hfk⟩ := Finset.mem_filter.mp hf
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨f, hfI, rfl⟩, hfk⟩
    _ ≤ (Finset.univ.filter (fun f : V → Fin c ↦ Finset.univ.image f ∈ B)).card := by
      apply card_maps_with_images_le (k := k) _ _ hcard
      · intro s hs
        exact (Finset.mem_filter.mp hs).2
      · intro s hs
        exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp hs).1).2
    _ = _ := by
      congr 1
      ext f
      simp [B, Finset.mem_powersetCard, Set.mem_range, and_comm]

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
