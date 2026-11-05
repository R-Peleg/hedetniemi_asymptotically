import HedetniemiAsymptotically.ElZaharSauer
import HedetniemiAsymptotically.SuitedColoring
import HedetniemiAsymptotically.RobustColor
import HedetniemiAsymptotically.IndependentSet
import HedetniemiAsymptotically.MapCounting
import HedetniemiAsymptotically.VertexColorFiber
import HedetniemiAsymptotically.TriangleFree
import HedetniemiAsymptotically.AvoidingLargeFibers
import HedetniemiAsymptotically.RobustColors
import HedetniemiAsymptotically.ExponentialLift
import HedetniemiAsymptotically.RobustError
import HedetniemiAsymptotically.EvenNear
import HedetniemiAsymptotically.MuMap
import HedetniemiAsymptotically.NuMap
import HedetniemiAsymptotically.RestrictedColoring
import HedetniemiAsymptotically.FiniteMap
import HedetniemiAsymptotically.FiniteMuMap
import HedetniemiAsymptotically.FiniteNuMap
import HedetniemiAsymptotically.Recoloring
import HedetniemiAsymptotically.ConstructionDelta
import HedetniemiAsymptotically.FractionalChromaticLowerBound
import HedetniemiAsymptotically.BinomialEstimate
import HedetniemiAsymptotically.CycleTemplates
import HedetniemiAsymptotically.PlaceCycleEdges
import HedetniemiAsymptotically.CyclePlacement
import HedetniemiAsymptotically.CyclePlacementProperties
import HedetniemiAsymptotically.PresentCyclePlacements
import HedetniemiAsymptotically.InducedIndependence
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Algebra.Order.Floor.Ring

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

/-- Lemma 4. An independent family in an exponential graph on `n` nonempty
vertices has size at most `n * c^(n-1)`, provided `c ≥ 2*n`. -/
theorem exponential_independent_card_le {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] (G : Graph V) (c : ℕ) (hc : 2 * Fintype.card V ≤ c)
    (I : Finset (V → Fin c))
    (hI : (exponentialGraph G (Fin c)).IsIndependent (I : Set (V → Fin c))) :
    I.card ≤ Fintype.card V * c ^ (Fintype.card V - 1) := by
  classical
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hcpos : 0 < c := by omega
  let b : Fin c := ⟨0, hcpos⟩
  let K := Finset.Icc 1 (Fintype.card V)
  let star := Finset.univ.filter (fun f : V → Fin c ↦ b ∈ Set.range f)
  have hrange (f : V → Fin c) : (Finset.univ.image f).card ∈ K := by
    apply Finset.mem_Icc.mpr
    constructor
    · exact Finset.card_pos.mpr (Finset.univ_nonempty.image f)
    · exact (Finset.card_image_le).trans_eq (Finset.card_univ)
  have hpartition (F : Finset (V → Fin c)) :
      F.card = ∑ k ∈ K, (F.filter (fun f ↦ (Finset.univ.image f).card = k)).card :=
    Finset.card_eq_sum_card_fiberwise (fun f _ ↦ hrange f)
  calc
    I.card = ∑ k ∈ K, (I.filter (fun f ↦ (Finset.univ.image f).card = k)).card :=
      hpartition I
    _ ≤ ∑ k ∈ K, (Finset.univ.filter (fun f : V → Fin c ↦
        b ∈ Set.range f ∧ (Finset.univ.image f).card = k)).card := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hkpos, hkn⟩ := Finset.mem_Icc.mp hk
      exact independent_map_layer_card_le I hI b hkpos (by omega)
    _ = star.card := by
      rw [hpartition star]
      apply Finset.sum_congr rfl
      intro k _
      simp only [star, Finset.filter_filter]
    _ ≤ Fintype.card V * c ^ (Fintype.card V - 1) := by
      simpa [star] using card_maps_containing_color_le (V := V) b

/-- The first counting step of Lemma 5: a vertex/color fiber larger than
`n² c^(n-2)` forces that color to be robust at the vertex. -/
theorem large_vertexColorFiber_isRobust {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) (b : C)
    (hlarge : Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) <
      (vertexColorFiber χ v b).card) : IsRobust χ v b := by
  classical
  intro f hf
  by_contra hrobust
  have hsmall : (vertexColorFiber χ v b).card ≤
      Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) := by
    apply le_trans _ (card_maps_with_secondary_match_le v b f)
    apply Finset.card_le_card
    intro g hg
    obtain ⟨hχg, hgv⟩ := (mem_vertexColorFiber χ v b g).mp hg
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hgv, ?_⟩
    by_contra hmatch
    apply χ.property (v := g) (w := f) ?_ (hχg.trans hf.symm)
    intro w u hwu heq
    by_cases hw : w = v
    · subst w
      exact hrobust ⟨u, Or.inr hwu, heq.symm.trans hgv⟩
    · exact hmatch ⟨w, hw, u, heq⟩
  exact (Nat.not_le_of_gt hlarge) hsmall

/-- A large fiber also contains a map taking its primary color only at its
specified vertex. This supplies the support hypothesis in the clique step
of Lemma 5. -/
theorem large_vertexColorFiber_has_unique_support {V C D : Type*}
    [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) (b : C)
    (hlarge : Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) <
      (vertexColorFiber χ v b).card) :
    ∃ f : V → C, χ.val f = Sum.inl b ∧ ∀ w, f w = b → w = v := by
  classical
  by_contra hnone
  have hsmall : (vertexColorFiber χ v b).card ≤
      Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) := by
    apply le_trans _ (card_maps_with_secondary_match_le v b (fun _ : V ↦ b))
    apply Finset.card_le_card
    intro f hf
    obtain ⟨hχf, hfv⟩ := (mem_vertexColorFiber χ v b f).mp hf
    have hsecond : ∃ w, w ≠ v ∧ f w = b := by
      by_contra h
      apply hnone
      refine ⟨f, hχf, ?_⟩
      intro w hwb
      by_contra hw
      exact h ⟨w, hw, hwb⟩
    obtain ⟨w, hw, hwb⟩ := hsecond
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfv, w, hw, v, hwb⟩
  exact (Nat.not_le_of_gt hlarge) hsmall

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

/-- The sets `V_b` of Lemma 5, defined by large fibers, are cliques. -/
theorem large_vertexColorFibers_form_clique {V C D : Type*}
    [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (b : C) :
    ∀ v, Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) <
      (vertexColorFiber χ v b).card →
    ∀ u, Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) <
      (vertexColorFiber χ u b).card → v ≠ u → G.Adj v u := by
  apply robust_supports_form_clique
  · intro v hv
    exact large_vertexColorFiber_isRobust χ v b hv
  · intro v hv
    exact large_vertexColorFiber_has_unique_support χ v b hv

/-- In the triangle-free setting of Lemma 5, every set `V_b` has size at most two. -/
theorem large_vertexColorFibers_card_le_two {V C D : Type*}
    [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] {G : Graph V}
    (hG : G.IsTriangleFree)
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (b : C) :
    (Finset.univ.filter (fun v ↦
      Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2) <
        (vertexColorFiber χ v b).card)).card ≤ 2 := by
  classical
  apply hG.card_clique_le_two
  intro v hv u hu hne
  exact large_vertexColorFibers_form_clique χ b v (Finset.mem_filter.mp hv).2
    u (Finset.mem_filter.mp hu).2 hne

/-- Primary color classes in the avoiding family are covered by the small
vertex/color fibers, as in the upper-bound argument of Lemma 5. -/
theorem avoiding_primary_class_card_le {V C D : Type*}
    [Fintype V] [Fintype C] [DecidableEq V] [DecidableEq C] [DecidableEq D] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (hχ : IsSuited χ) (b : C) :
    ((avoidingLargeFibers χ).filter (fun f ↦ χ.val f = Sum.inl b)).card ≤
      Fintype.card V * (Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2)) := by
  classical
  let K := Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2)
  let F (v : V) := if (vertexColorFiber χ v b).card ≤ K then vertexColorFiber χ v b else ∅
  calc
    _ ≤ (Finset.univ.biUnion F).card := by
      apply Finset.card_le_card
      intro f hf
      obtain ⟨hfS, hfb⟩ := Finset.mem_filter.mp hf
      obtain ⟨v, hfv⟩ := hχ f b hfb
      have hsmall : (vertexColorFiber χ v b).card ≤ K := by
        simpa only [hfv] using (mem_avoidingLargeFibers χ f).mp hfS v
      exact Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, by
        simp [F, hsmall, hfb, hfv]⟩
    _ ≤ ∑ v : V, (F v).card := Finset.card_biUnion_le
    _ ≤ ∑ _v : V, K := by
      apply Finset.sum_le_sum
      intro v _
      dsimp [F]
      split_ifs with hv
      · exact hv
      · exact Nat.zero_le _
    _ = _ := by simp [K]

/-- The upper bound on `|S|` in Lemma 5. -/
theorem card_avoidingLargeFibers_le {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] {G : Graph V} {c t : ℕ}
    (χ : (exponentialGraph G (Fin c)).Coloring (Fin c ⊕ Fin t))
    (hχ : IsSuited χ) (hn : 2 ≤ Fintype.card V) (hc : 2 * Fintype.card V ≤ c) :
    (avoidingLargeFibers χ).card ≤
      (Fintype.card V * t + Fintype.card V ^ 3) * c ^ (Fintype.card V - 1) := by
  classical
  let n := Fintype.card V
  let S := avoidingLargeFibers χ
  have hp : (∑ b : Fin c, (S.filter (fun f ↦ χ.val f = Sum.inl b)).card) ≤
      c * (n * (n ^ 2 * c ^ (n - 2))) := by
    calc
      _ ≤ ∑ _b : Fin c, n * (n ^ 2 * c ^ (n - 2)) := by
        apply Finset.sum_le_sum
        intro b _
        simpa [n, S] using avoiding_primary_class_card_le χ hχ b
      _ = _ := by simp
  have hs : (∑ d : Fin t, (S.filter (fun f ↦ χ.val f = Sum.inr d)).card) ≤
      t * (n * c ^ (n - 1)) := by
    calc
      _ ≤ ∑ _d : Fin t, n * c ^ (n - 1) := by
        apply Finset.sum_le_sum
        intro d _
        apply exponential_independent_card_le G c hc
        intro f hf g hg _ hadj
        exact χ.property hadj ((Finset.mem_filter.mp hf).2.trans
          (Finset.mem_filter.mp hg).2.symm)
      _ = _ := by simp
  calc
    S.card = (∑ b : Fin c, (S.filter (fun f ↦ χ.val f = Sum.inl b)).card) +
        ∑ d : Fin t, (S.filter (fun f ↦ χ.val f = Sum.inr d)).card := by
      rw [Finset.card_eq_sum_card_fiberwise (f := χ.val)
        (t := Finset.univ) (fun _ _ ↦ Finset.mem_univ _), Fintype.sum_sum_type]
    _ ≤ c * (n * (n ^ 2 * c ^ (n - 2))) + t * (n * c ^ (n - 1)) :=
      Nat.add_le_add hp hs
    _ = _ := by
      change _ = (n * t + n ^ 3) * c ^ (n - 1)
      have he : n - 1 = n - 2 + 1 := by dsimp [n]; omega
      simp only [he, pow_succ]
      ring

/-- Double counting the excluded vertex/color pairs gives the sum estimate
`∑ s(v) ≥ (n-2)c` used for the product bound in Lemma 5. -/
theorem sum_card_allowedColors_ge {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] [DecidableEq C] {G : Graph V} (hG : G.IsTriangleFree)
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) :
    (Fintype.card V - 2) * Fintype.card C ≤ ∑ v, (allowedColors χ v).card := by
  classical
  let K := Fintype.card V ^ 2 * Fintype.card C ^ (Fintype.card V - 2)
  let E (v : V) := Finset.univ.filter (fun b : C ↦ K < (vertexColorFiber χ v b).card)
  let B (b : C) := Finset.univ.filter (fun v : V ↦ K < (vertexColorFiber χ v b).card)
  have hswap : (∑ v, (E v).card) = ∑ b, (B b).card := by
    simp only [E, B, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  have htotal : (∑ v, (allowedColors χ v).card) + (∑ b, (B b).card) =
      Fintype.card V * Fintype.card C := by
    rw [← hswap, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _v : V, Fintype.card C := by
        apply Finset.sum_congr rfl
        intro v _
        simpa [allowedColors, E, K, not_le] using
          Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset C))
            (fun b ↦ (vertexColorFiber χ v b).card ≤ K)
      _ = _ := by simp
  have hbound : (∑ b, (B b).card) ≤ 2 * Fintype.card C := by
    calc
      _ ≤ ∑ _b : C, 2 := by
        apply Finset.sum_le_sum
        intro b _
        exact large_vertexColorFibers_card_le_two hG χ b
      _ = _ := by simp [Nat.mul_comm]
  rw [Nat.sub_mul]
  omega

/-- Every excluded primary color is robust. Thus the number of robust
colors is at least `c - s(v)`. -/
theorem card_robustColors_ge_excluded {V C D : Type*} [Fintype V] [Fintype C]
    [DecidableEq V] {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) (v : V) :
    Fintype.card C - (allowedColors χ v).card ≤ (robustColors χ v).card := by
  classical
  have hcover : (allowedColors χ v).card + (robustColors χ v).card ≥ Fintype.card C := by
    calc
      Fintype.card C = (Finset.univ : Finset C).card := Finset.card_univ.symm
      _ = (allowedColors χ v ∪ robustColors χ v).card := by
        congr 1
        ext b
        simp only [Finset.mem_univ, Finset.mem_union, true_iff]
        by_cases hb : b ∈ allowedColors χ v
        · exact Or.inl hb
        · exact Or.inr ((mem_robustColors χ v b).mpr
            (large_vertexColorFiber_isRobust χ v b
              (Nat.lt_of_not_ge (fun h ↦ hb ((mem_allowedColors χ v b).mpr h)))))
      _ ≤ _ := Finset.card_union_le _ _
  omega

/-- A strict logarithmic chord estimate used in the convexity argument of
Lemma 5. The endpoint `r ≤ 1/2` allows the coefficient to be bounded by two. -/
theorem log_factor_gt {r a : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (hra : r < a) (ha : a < 1) :
    2 * (1 - a) * Real.log r < Real.log a := by
  have hr1 : r < 1 := by linarith
  have hden : 0 < 1 - r := by linarith
  have hu : 0 < (1 - a) / (1 - r) := div_pos (by linarith) hden
  have hv : 0 < (a - r) / (1 - r) := div_pos (by linarith) hden
  have huv : (1 - a) / (1 - r) + (a - r) / (1 - r) = 1 := by
    field_simp
    ring
  have hcombo : (1 - a) / (1 - r) * r + (a - r) / (1 - r) * 1 = a := by
    field_simp
    ring
  have hlog := strictConcaveOn_log_Ioi.2 hr (by norm_num) hr1.ne hu hv huv
  simp only [smul_eq_mul, Real.log_one, mul_zero, add_zero, hcombo] at hlog
  have hcoef : (1 - a) / (1 - r) ≤ 2 * (1 - a) := by
    apply (div_le_iff₀ hden).mpr
    nlinarith [mul_nonneg (show 0 ≤ 1 - a by linarith) (show 0 ≤ 1 - 2 * r by linarith)]
  exact (mul_le_mul_of_nonpos_right hcoef (Real.log_nonpos hr.le hr1.le)).trans_lt hlog

/-- The normalized product estimate in Lemma 5. If the total deficit from
one is at most two, factors all strictly above `r ≤ 1/2` have product
strictly greater than `r^4`. -/
theorem normalized_product_gt_fourth {V : Type*} [Fintype V]
    (a : V → ℝ) {r : ℝ} (hr : 0 < r) (hrhalf : r ≤ 1 / 2)
    (ha : ∀ v, r < a v) (ha1 : ∀ v, a v ≤ 1)
    (hsum : ∑ v, (1 - a v) ≤ 2) : r ^ 4 < ∏ v, a v := by
  classical
  have hr1 : r < 1 := by linarith
  by_cases hall : ∀ v, a v = 1
  · simp only [hall, Finset.prod_const_one]
    calc
      r ^ 4 ≤ (1 / 2 : ℝ) ^ 4 := pow_le_pow_left₀ hr.le hrhalf 4
      _ < 1 := by norm_num
  obtain ⟨v, hv⟩ := not_forall.mp hall
  have hpoint (w : V) : 2 * (1 - a w) * Real.log r ≤ Real.log (a w) := by
    by_cases hw : a w = 1
    · simp [hw]
    · exact (log_factor_gt hr hrhalf (ha w) (lt_of_le_of_ne (ha1 w) hw)).le
  have hstrict : (∑ w, 2 * (1 - a w) * Real.log r) < ∑ w, Real.log (a w) := by
    apply Finset.sum_lt_sum (fun w _ ↦ hpoint w)
    exact ⟨v, Finset.mem_univ _, log_factor_gt hr hrhalf (ha v)
      (lt_of_le_of_ne (ha1 v) hv)⟩
  rw [← Finset.sum_mul, ← Finset.mul_sum] at hstrict
  have hbase : 4 * Real.log r ≤ 2 * (∑ w, (1 - a w)) * Real.log r :=
    mul_le_mul_of_nonpos_right (by linarith) (Real.log_nonpos hr.le hr1.le)
  have hlog : Real.log (r ^ 4) < Real.log (∏ w, a w) := by
    rw [Real.log_pow, Real.log_prod (fun w _ ↦ (hr.trans (ha w)).ne')]
    norm_num
    exact hbase.trans_lt hstrict
  exact (Real.log_lt_log_iff (pow_pos hr 4)
    (Finset.prod_pos (fun w _ ↦ hr.trans (ha w)))).mp hlog

/-- The product estimate of Lemma 5 after rescaling by `c`. Multiplying by
`c^4` avoids truncated subtraction in the exponent and is equivalent to
the paper's bound when there are at least four vertices. -/
theorem product_gt_fourth_scaled {V : Type*} [Fintype V]
    (s : V → ℝ) {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (hxhalf : x ≤ c / 2)
    (hs : ∀ v, x < s v) (hsc : ∀ v, s v ≤ c)
    (hdef : ∑ v, (c - s v) ≤ 2 * c) :
    x ^ 4 * c ^ Fintype.card V < (∏ v, s v) * c ^ 4 := by
  have hrhalf : x / c ≤ 1 / 2 := (div_le_iff₀ hc).mpr (by linarith)
  have hnorm : ∑ v, (1 - s v / c) ≤ 2 := by
    have heq : (∑ v, (1 - s v / c)) = (∑ v, (c - s v)) / c := by
      apply (eq_div_iff hc.ne').mpr
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro v _
      field_simp
    rw [heq]
    exact (div_le_iff₀ hc).mpr hdef
  have hprod := normalized_product_gt_fourth (fun v ↦ s v / c) (div_pos hx hc)
    hrhalf (fun v ↦ (div_lt_div_iff_of_pos_right hc).mpr (hs v))
    (fun v ↦ (div_le_one hc).mpr (hsc v)) hnorm
  rw [div_pow, Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ] at hprod
  exact (div_lt_div_iff₀ (pow_pos hc 4) (pow_pos hc (Fintype.card V))).mp hprod

/-- Lemma 5 with the fourth root specified by its defining equation and
the bound `x ≤ c/2`. The numerical hypothesis in the paper guarantees this
bound. This form isolates the combinatorial/convexity argument from the
elementary fourth-root arithmetic. -/
theorem exists_many_robust_colors_of_fourth_power {V : Type*} [Fintype V] [Nonempty V]
    [DecidableEq V] {G : Graph V} {c t : ℕ} (hG : G.IsTriangleFree)
    (χ : (exponentialGraph G (Fin c)).Coloring (Fin c ⊕ Fin t)) (hχ : IsSuited χ)
    (hn : 4 ≤ Fintype.card V) (hc : 2 * Fintype.card V ≤ c)
    (x : ℝ) (hx : 0 < x) (hxhalf : x ≤ (c : ℝ) / 2)
    (hxpow : x ^ 4 = ((Fintype.card V : ℝ) * t + (Fintype.card V : ℝ) ^ 3) * (c : ℝ) ^ 3) :
    ∃ v, (c : ℝ) - x ≤ ((robustColors χ v).card : ℝ) := by
  classical
  let n := Fintype.card V
  let s (v : V) : ℝ := (allowedColors χ v).card
  have hn2 : 2 ≤ n := by dsimp [n]; omega
  have hcpos : 0 < c := by omega
  have hcR : (0 : ℝ) < c := by exact_mod_cast hcpos
  have hsc (v : V) : s v ≤ c := by
    dsimp [s]
    exact_mod_cast (show (allowedColors χ v).card ≤ c by
      simpa using Finset.card_le_univ (allowedColors χ v))
  have hupper : (∏ v, s v) ≤ ((n : ℝ) * t + (n : ℝ) ^ 3) * (c : ℝ) ^ (n - 1) := by
    have hcard : (∏ v, (allowedColors χ v).card) ≤
        (n * t + n ^ 3) * c ^ (n - 1) := by
      rw [← card_avoidingLargeFibers]
      exact card_avoidingLargeFibers_le χ hχ hn2 hc
    dsimp [s]
    exact_mod_cast hcard
  have hsum : ((n : ℝ) - 2) * c ≤ ∑ v, s v := by
    have hcast : (((n - 2) * c : ℕ) : ℝ) ≤ ((∑ v, (allowedColors χ v).card : ℕ) : ℝ) := by
      exact_mod_cast (show (n - 2) * c ≤ ∑ v, (allowedColors χ v).card by
        simpa [n] using sum_card_allowedColors_ge hG χ)
    simpa only [Nat.cast_mul, Nat.cast_sub hn2, Nat.cast_ofNat, Nat.cast_sum] using hcast
  have hdef : (∑ v, ((c : ℝ) - s v)) ≤ 2 * c := by
    have heq : (∑ v, ((c : ℝ) - s v)) = (n : ℝ) * c - ∑ v, s v := by
      simp [Finset.sum_sub_distrib, n]
    rw [heq]
    linarith
  have hex : ∃ v, s v ≤ x := by
    by_contra hnone
    have hs : ∀ v, x < s v := by
      intro v
      exact lt_of_not_ge (fun h ↦ hnone ⟨v, h⟩)
    have hprod := product_gt_fourth_scaled s hcR hx hxhalf hs hsc hdef
    have hmul := mul_le_mul_of_nonneg_right hupper (pow_nonneg hcR.le 4)
    have heqpow : (((n : ℝ) * t + (n : ℝ) ^ 3) * (c : ℝ) ^ (n - 1)) * (c : ℝ) ^ 4 =
        x ^ 4 * (c : ℝ) ^ n := by
      rw [hxpow]
      have he : n - 1 + 4 = 3 + n := by omega
      calc
        _ = ((n : ℝ) * t + (n : ℝ) ^ 3) * (c : ℝ) ^ (n - 1 + 4) := by
          rw [pow_add]; ring
        _ = _ := by rw [he, pow_add]; ring
    rw [heqpow] at hmul
    exact (not_lt_of_ge hmul) hprod
  obtain ⟨v, hv⟩ := hex
  refine ⟨v, ?_⟩
  have hcardle : (allowedColors χ v).card ≤ c := by
    simpa using Finset.card_le_univ (allowedColors χ v)
  have hrob : (c : ℝ) - s v ≤ ((robustColors χ v).card : ℝ) := by
    have hcast : ((c - (allowedColors χ v).card : ℕ) : ℝ) ≤
        ((robustColors χ v).card : ℝ) := by
      exact_mod_cast (show c - (allowedColors χ v).card ≤ (robustColors χ v).card by
        simpa using card_robustColors_ge_excluded χ v)
    simpa only [Nat.cast_sub hcardle] using hcast
  linarith

/-- Lemma 5 (robust colors). A suited `(c+t)`-coloring of an exponential
graph over a triangle-free graph has a vertex with at least `c-x` robust
primary colors, where `x = ((nt+n³)c³)^(1/4)`. -/
theorem exists_many_robust_colors {V : Type*} [Fintype V] [DecidableEq V]
    {G : Graph V} {c t : ℕ} (hG : G.IsTriangleFree)
    (χ : (exponentialGraph G (Fin c)).Coloring (Fin c ⊕ Fin t)) (hχ : IsSuited χ)
    (hn : 4 ≤ Fintype.card V) (hc : 16 * (Fintype.card V * t + Fintype.card V ^ 3) ≤ c) :
    ∃ v, (c : ℝ) - robustError (Fintype.card V) c t ≤ ((robustColors χ v).card : ℝ) := by
  let n := Fintype.card V
  have hn0 : 0 < n := by dsimp [n]; omega
  have hn1 : 1 ≤ n := by omega
  have hn2 : n ≤ n * n := by simpa using Nat.mul_le_mul_left n hn1
  have hn3 : n ≤ n ^ 3 := by
    calc
      n ≤ n * n := hn2
      _ ≤ (n * n) * n := by simpa using Nat.mul_le_mul_left (n * n) hn1
      _ = _ := by ring
  have hc2 : 2 * Fintype.card V ≤ c := by
    change 2 * n ≤ c
    change 16 * (n * t + n ^ 3) ≤ c at hc
    omega
  have hc0 : 0 < c := by omega
  have : Nonempty V := Fintype.card_pos_iff.mp hn0
  exact exists_many_robust_colors_of_fourth_power hG χ hχ hn hc2 _
    (robustError_pos hn0 hc0) (robustError_le_half hc)
    (robustError_pow_four (Fintype.card V) c t)

/-- A girth bound of six excludes triangles, including closed three-step
walks presented without distinctness assumptions. -/
theorem no_triangle_of_six_le_egirth {V : Type*} {G : SimpleGraph V}
    (hG : 6 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hw : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [w, SimpleGraph.Walk.isPath_def, hbc.ne, hab.ne', hca.ne]
    · simp [w]
  have hbound := hG.trans hw.egirth_le_length
  norm_num [w] at hbound

/-- A girth bound of six excludes every closed five-step walk. If vertices
repeat, such a walk already contains a triangle; otherwise it is a cycle. -/
theorem no_five_walk_of_six_le_egirth {V : Type*} {G : SimpleGraph V}
    (hG : 6 ≤ G.egirth) {a b c d e : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d)
    (hde : G.Adj d e) (hea : G.Adj e a) : False := by
  have hac : a ≠ c := by
    intro h; subst c
    exact no_triangle_of_six_le_egirth hG hcd hde hea
  have had : a ≠ d := by
    intro h; subst d
    exact no_triangle_of_six_le_egirth hG hab hbc hcd
  have hbd : b ≠ d := by
    intro h; subst d
    exact no_triangle_of_six_le_egirth hG hab hde hea
  have hbe : b ≠ e := by
    intro h; subst e
    exact no_triangle_of_six_le_egirth hG hbc hcd hde
  have hce : c ≠ e := by
    intro h; subst e
    exact no_triangle_of_six_le_egirth hG hab hbc hea
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hcd (.cons hde (.cons hea .nil))))
  have hw : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [w, SimpleGraph.Walk.isPath_def, hbc.ne, hcd.ne, hde.ne, hea.ne,
        hab.ne', hbd, hbe, hce, hac.symm, had.symm]
    · simp [w]
  have hbound := hG.trans hw.egirth_le_length
  norm_num [w] at hbound

/-- The even part of a radius-two ball is independent when the girth is at least six. -/
theorem evenNear_not_adj_of_six_le_egirth {V : Type*} {G : SimpleGraph V}
    (hG : 6 ≤ G.egirth) (v : V) {g h : V}
    (hg : EvenNear G v g) (hh : EvenNear G v h) : ¬ G.Adj g h := by
  intro hgh
  rcases hg with rfl | ⟨a, hva, hag⟩
  · rcases hh with rfl | ⟨b, hvb, hbh⟩
    · exact hgh.ne rfl
    · exact no_triangle_of_six_le_egirth hG hvb hbh hgh.symm
  · rcases hh with rfl | ⟨b, hvb, hbh⟩
    · exact no_triangle_of_six_le_egirth hG hva hag hgh
    · exact no_five_walk_of_six_le_egirth hG hva hag hgh hbh.symm hvb.symm

/-- The first clique in Lemma 6: distinct maps `μ_r` are co-proper.
The colors `r` start at the end of the first block, as in the paper. -/
theorem muMap_coproper {V : Type*} {G : SimpleGraph V} (hG : 6 ≤ G.egirth)
    (v : V) {q r s : ℕ} (hr : q ≤ r) (hs : q ≤ s) (hrs : r ≠ s) :
    CoProper (Graph.ofSimpleGraph (strongProduct G (⊤ : SimpleGraph (Fin q))))
      (muMap G v q r) (muMap G v q s) := by
  classical
  intro x y hxy heq
  change (strongProduct G (⊤ : SimpleGraph (Fin q))).Adj x y at hxy
  have hi := x.2.isLt
  have hj := y.2.isLt
  by_cases hxE : EvenNear G v x.1
  · by_cases hyE : EvenNear G v y.1
    · have hij : x.2.val = y.2.val := by simpa [muMap, hxE, hyE] using heq
      exact evenNear_not_adj_of_six_le_egirth hG v hxE hyE
        (strongProduct_adj_of_snd_eq hxy (Fin.ext hij))
    · by_cases hyN : G.Adj v y.1
      · simp only [muMap, ite_eq_left hxE, ite_eq_right hyE, ite_eq_left hyN] at heq
        omega
      · simp only [muMap, ite_eq_left hxE, ite_eq_right hyE, ite_eq_right hyN] at heq
        omega
  · by_cases hxN : G.Adj v x.1
    · by_cases hyE : EvenNear G v y.1
      · simp only [muMap, ite_eq_right hxE, ite_eq_left hxN, ite_eq_left hyE] at heq
        omega
      · by_cases hyN : G.Adj v y.1
        · have hij : x.2.val = y.2.val := by
            simp only [muMap, ite_eq_right hxE, ite_eq_left hxN, ite_eq_right hyE, ite_eq_left hyN] at heq
            omega
          exact no_triangle_of_six_le_egirth hG hxN
            (strongProduct_adj_of_snd_eq hxy (Fin.ext hij)) hyN.symm
        · exact far_not_loopedAdj_neighbor hyE hyN hxN ((loopedGraph G).symm hxy.1)
    · by_cases hyE : EvenNear G v y.1
      · simp only [muMap, ite_eq_right hxE, ite_eq_right hxN, ite_eq_left hyE] at heq
        omega
      · by_cases hyN : G.Adj v y.1
        · exact far_not_loopedAdj_neighbor hxE hxN hyN hxy.1
        · exact hrs (by simpa [muMap, hxE, hxN, hyE, hyN] using heq)

/-- The second clique of Lemma 6 consists of `ν` maps with disjoint pairs
of image colors. This fact does not require a girth assumption. -/
theorem nuMap_coproper_of_disjoint_colors {V : Type*} (G : SimpleGraph V) (v : V)
    {r σ r' σ' : ℕ} (hrr : r ≠ r') (hrσ : r ≠ σ') (hσr : σ ≠ r') (hσσ : σ ≠ σ') :
    CoProper (loopedGraph G) (nuMap G v r σ) (nuMap G v r' σ') := by
  classical
  intro x y _
  unfold nuMap
  split_ifs <;> assumption

/-- The final edge in Lemma 6: `μ_r` and the lifted `ν_{r,σ}` are
co-proper when both high colors avoid the first two color blocks. -/
theorem muMap_nuMap_coproper {V : Type*} (G : SimpleGraph V) (v : V) {q r σ : ℕ}
    (hr : 2 * q ≤ r) (hσ : 2 * q ≤ σ) (hrσ : r ≠ σ) :
    CoProper (Graph.ofSimpleGraph (strongProduct G (⊤ : SimpleGraph (Fin q))))
      (muMap G v q r) (exponentialLift (W := Fin q) (nuMap G v r σ)) := by
  classical
  intro x y hxy heq
  have hi := x.2.isLt
  change muMap G v q r x = nuMap G v r σ y.1 at heq
  by_cases hxE : EvenNear G v x.1
  · simp only [muMap, ite_eq_left hxE, nuMap] at heq
    split_ifs at heq <;> omega
  · by_cases hxN : G.Adj v x.1
    · simp only [muMap, ite_eq_right hxE, ite_eq_left hxN, nuMap] at heq
      split_ifs at heq <;> omega
    · by_cases hyC : y.1 = v ∨ G.Adj v y.1
      · exact far_not_loopedAdj_closed hxE hxN hyC hxy.1
      · exact hrσ (by simpa [muMap, hxE, hxN, nuMap, hyC] using heq)

/-- Adding loops preserves the triangle-free hypothesis needed for Lemma 5. -/
theorem loopedGraph_triangleFree_of_six_le_egirth {V : Type*} {G : SimpleGraph V}
    (hG : 6 ≤ G.egirth) : (loopedGraph G).IsTriangleFree := by
  intro a b c habne hacne hbcne hab hac hbc
  exact no_triangle_of_six_le_egirth hG (hab.resolve_left habne)
    (hbc.resolve_left hbcne) (hac.resolve_left hacne).symm

/-- The pigeonhole step in Lemma 6: a clique of `t+1` vertices cannot all
receive the `t` secondary colors. -/
theorem secondary_clique_impossible {V C : Type*} {t : ℕ} {G : Graph V}
    (χ : G.Coloring (C ⊕ Fin t)) (F : Fin (t + 1) → V)
    (hF : ∀ i j, i ≠ j → G.Adj (F i) (F j))
    (hsecondary : ∀ i, ∃ d : Fin t, χ.val (F i) = Sum.inr d) : False := by
  classical
  choose d hd using hsecondary
  have hinj : Function.Injective d := by
    intro i j hij
    by_contra hne
    apply χ.property (hF i j hne)
    rw [hd i, hd j, hij]
  have hcard := Fintype.card_le_of_injective d hinj
  simp at hcard

/-- Robustness prevents the lifted `ν_{r,σ}` map from receiving `σ`, since
it takes the different color `r` throughout the closed neighborhood. -/
theorem finiteNuMap_not_robust_color {V : Type*} {G : SimpleGraph V} {q c t : ℕ}
    (χ : (exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin c ⊕ Fin t))
    (v : V) {r σ : Fin c} (hrσ : r ≠ σ)
    (hrob : IsRobust (restrictExponentialColoring χ) v σ) :
    χ.val (exponentialLift (W := Fin q) (finiteNuMap G v r σ)) ≠ Sum.inl σ := by
  intro hcolor
  obtain ⟨w, hw, hval⟩ := hrob (finiteNuMap G v r σ) hcolor
  have hwclosed : w = v ∨ G.Adj v w := by
    rcases hw with heq | heq | hadj
    · exact Or.inl heq
    · exact Or.inl heq.symm
    · exact Or.inr hadj
  have hvalr : (finiteNuMap G v r σ w).val = r.val := nuMap_eq_on_closed hwclosed
  exact hrσ ((Fin.ext hvalr).symm.trans hval)

/-- The final coloring contradiction in Lemma 6, once the families of
robust colors `σ_i` and self-colored maps `μ_{r_i}` have been chosen. -/
theorem lemma6_configuration_impossible {V : Type*} {G : SimpleGraph V} {q c t : ℕ}
    (χ : (exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin c ⊕ Fin t))
    (hχ : IsSuited χ) (v : V) (hq : 2 * q ≤ c)
    (r σ : Fin (t + 1) → Fin c) (hrinj : Function.Injective r) (hσinj : Function.Injective σ)
    (hdisjoint : ∀ i j, r i ≠ σ j)
    (hrhigh : ∀ i, 2 * q ≤ (r i).val) (hσhigh : ∀ i, 2 * q ≤ (σ i).val)
    (hrob : ∀ i, IsRobust (restrictExponentialColoring χ) v (σ i))
    (hmu : ∀ i, χ.val (finiteMuMap G v hq (r i)) = Sum.inl (r i)) : False := by
  classical
  apply secondary_clique_impossible χ
    (fun i ↦ exponentialLift (W := Fin q) (finiteNuMap G v (r i) (σ i)))
  · intro i j hij
    apply CoProper.exponentialLift
    apply coProper_finiteMap_iff.mpr
    apply nuMap_coproper_of_disjoint_colors
    · exact fun heq ↦ hij (hrinj (Fin.ext heq))
    · exact fun heq ↦ hdisjoint i j (Fin.ext heq)
    · exact fun heq ↦ hdisjoint j i (Fin.ext heq.symm)
    · exact fun heq ↦ hij (hσinj (Fin.ext heq))
  · intro i
    cases hcol : χ.val (exponentialLift (W := Fin q) (finiteNuMap G v (r i) (σ i))) with
    | inl b =>
      obtain ⟨x, hxb⟩ := hχ _ b hcol
      have hb : b = r i ∨ b = σ i := by
        have hnat : nuMap G v (r i).val (σ i).val x.1 = b.val := congrArg Fin.val hxb
        unfold nuMap at hnat
        split_ifs at hnat
        · exact Or.inl (Fin.ext hnat.symm)
        · exact Or.inr (Fin.ext hnat.symm)
      rcases hb with rfl | rfl
      · have hadj : (exponentialGraph (Graph.ofSimpleGraph
            (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Adj
            (finiteMuMap G v hq (r i))
            (exponentialLift (W := Fin q) (finiteNuMap G v (r i) (σ i))) := by
          intro x y hxy heq
          exact muMap_nuMap_coproper G v (hrhigh i) (hσhigh i)
            (fun h ↦ hdisjoint i i (Fin.ext h)) hxy (congrArg Fin.val heq)
        exact (χ.property hadj ((hmu i).trans hcol.symm)).elim
      · exact (finiteNuMap_not_robust_color χ v (hdisjoint i i) (hrob i) hcol).elim
    | inr d => exact ⟨d, rfl⟩

/-- The first color selection in Lemma 6: after discarding the first `2q`
primary colors, enough robust colors remain to choose `t+1` distinct ones. -/
theorem exists_high_robust_colors {V : Type*} {G : Graph V} {q c t : ℕ}
    (χ : (exponentialGraph G (Fin c)).Coloring (Fin c ⊕ Fin t)) (v : V)
    (hcard : 2 * q + t + 1 ≤ (robustColors χ v).card) :
    ∃ σ : Fin (t + 1) ↪ Fin c, ∀ i, 2 * q ≤ (σ i).val ∧ IsRobust χ v (σ i) := by
  classical
  let S := (robustColors χ v).filter (fun b ↦ 2 * q ≤ b.val)
  let L := (robustColors χ v).filter (fun b ↦ b.val < 2 * q)
  have hlow : L.card ≤ (Finset.range (2 * q)).card := by
    apply Finset.card_le_card_of_injOn Fin.val
    · intro b hb
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hb).2
    · intro a _ b _ hab
      exact Fin.ext hab
  have hpartition : S.card + L.card = (robustColors χ v).card := by
    simpa [S, L, not_le] using Finset.card_filter_add_card_filter_not
      (s := robustColors χ v) (fun b ↦ 2 * q ≤ b.val)
  have hsize : t + 1 ≤ S.card := by simp only [Finset.card_range] at hlow; omega
  obtain ⟨σ, hσ⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin (t + 1)) (s := S) (by simpa using hsize)
  refine ⟨σ, ?_⟩
  intro i
  obtain ⟨hrob, hhigh⟩ := Finset.mem_filter.mp (hσ ⟨i, rfl⟩)
  exact ⟨hhigh, (mem_robustColors χ v (σ i)).mp hrob⟩

/-- Suitedness makes a high primary color on `μ_r` equal to `r`. -/
theorem suited_finiteMuMap_color_eq_parameter {V : Type*} {G : SimpleGraph V} {q c t : ℕ}
    (χ : (exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin c ⊕ Fin t))
    (hχ : IsSuited χ) (v : V) (hq : 2 * q ≤ c) (r b : Fin c)
    (hb : 2 * q ≤ b.val) (hcolor : χ.val (finiteMuMap G v hq r) = Sum.inl b) : b = r := by
  obtain ⟨x, hx⟩ := hχ _ b hcolor
  have hnat : muMap G v q r.val x = b.val := congrArg Fin.val hx
  have hlarge : 2 * q ≤ muMap G v q r.val x := by rw [hnat]; exact hb
  exact Fin.ext (hnat.symm.trans (muMap_eq_parameter_of_ge G v x hlarge))

/-- Select the self-colored maps `μ_{r_i}` in Lemma 6. There are `c-q`
distinct clique colors; discarding the low colors, the chosen `σ` colors,
and the secondary colors leaves at least `t+1` usable parameters. -/
theorem exists_self_colored_mu_maps {V : Type*} {G : SimpleGraph V} {q c t : ℕ}
    (hG : 6 ≤ G.egirth)
    (χ : (exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin c ⊕ Fin t))
    (hχ : IsSuited χ) (v : V) (hq : 2 * q ≤ c) (hc : 3 * q + 3 * t + 2 ≤ c)
    (σ : Fin (t + 1) → Fin c) :
    ∃ r : Fin (t + 1) ↪ Fin c, (∀ i, 2 * q ≤ (r i).val) ∧
      (∀ i j, r i ≠ σ j) ∧
      ∀ i, χ.val (finiteMuMap G v hq (r i)) = Sum.inl (r i) := by
  classical
  let P := Finset.univ.filter (fun r : Fin c ↦ q ≤ r.val)
  let f (r : Fin c) := χ.val (finiteMuMap G v hq r)
  let A := P.image f
  let low := (Finset.univ : Finset (Fin c)).filter (fun b ↦ b.val < 2 * q)
  let B := (low.image (Sum.inl : Fin c → Fin c ⊕ Fin t) ∪
    (Finset.univ.image σ).image Sum.inl) ∪ Finset.univ.image Sum.inr
  have hlow (k : ℕ) : ((Finset.univ : Finset (Fin c)).filter (fun b ↦ b.val < k)).card ≤ k := by
    calc
      _ ≤ (Finset.range k).card := by
        apply Finset.card_le_card_of_injOn Fin.val
        · intro b hb
          exact Finset.mem_range.mpr (Finset.mem_filter.mp hb).2
        · intro a _ b _ hab
          exact Fin.ext hab
      _ = k := Finset.card_range k
  have hP : c - q ≤ P.card := by
    have hpartition := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin c))) (fun r ↦ q ≤ r.val)
    have hlowq := hlow q
    simp only [Finset.card_univ, Fintype.card_fin, not_le] at hpartition
    dsimp [P]
    omega
  have hinj : Set.InjOn f (P : Set (Fin c)) := by
    intro r hr s hs hcolor
    by_contra hrs
    apply χ.property (coProper_finiteMap_iff.mpr
      (muMap_coproper hG v (Finset.mem_filter.mp hr).2 (Finset.mem_filter.mp hs).2
        (fun h ↦ hrs (Fin.ext h)))) hcolor
  have hA : A.card = P.card := Finset.card_image_iff.mpr hinj
  have hB : B.card ≤ 2 * q + (t + 1) + t := by
    calc
      _ ≤ (low.image (Sum.inl : Fin c → Fin c ⊕ Fin t)).card +
          ((Finset.univ.image σ).image (Sum.inl : Fin c → Fin c ⊕ Fin t)).card +
          (Finset.univ.image (Sum.inr : Fin t → Fin c ⊕ Fin t)).card :=
        le_trans (Finset.card_union_le _ _) (Nat.add_le_add_right (Finset.card_union_le _ _) _)
      _ ≤ low.card + (t + 1) + t := by
        apply Nat.add_le_add
        · apply Nat.add_le_add Finset.card_image_le
          exact (Finset.card_image_le).trans (by simpa using Finset.card_image_le (s := Finset.univ) (f := σ))
        · simpa using Finset.card_image_le (s := Finset.univ) (f := (Sum.inr : Fin t → Fin c ⊕ Fin t))
      _ ≤ _ := Nat.add_le_add_right (Nat.add_le_add_right (hlow (2 * q)) _) _
  have hgood : t + 1 ≤ (A \ B).card := by
    have hdiff := Finset.card_le_card_sdiff_add_card (s := A) (t := B)
    omega
  obtain ⟨e, he⟩ := Function.Embedding.exists_of_card_le_finset
    (α := Fin (t + 1)) (s := A \ B) (by simpa using hgood)
  have hex (i : Fin (t + 1)) : ∃ r : Fin c, e i = Sum.inl r ∧ 2 * q ≤ r.val ∧
      (∀ j, r ≠ σ j) ∧ f r = Sum.inl r := by
    obtain ⟨hiA, hiB⟩ := Finset.mem_sdiff.mp (he ⟨i, rfl⟩)
    obtain ⟨r, hrP, hfr⟩ := Finset.mem_image.mp hiA
    cases hei : e i with
    | inr d =>
      exact (hiB (by simp [B, hei])).elim
    | inl b =>
      have hbhigh : 2 * q ≤ b.val := by
        by_contra h
        apply hiB
        simp [B, hei, low, Nat.lt_of_not_ge h]
      have hbr : b = r := suited_finiteMuMap_color_eq_parameter χ hχ v hq r b hbhigh
        (hfr.trans hei)
      subst r
      refine ⟨b, rfl, hbhigh, ?_, hfr.trans hei⟩
      intro j hbj
      apply hiB
      simp [B, hei, hbj]
  choose r her hrhigh hrdisjoint hrcolor using hex
  have hrinj : Function.Injective r := by
    intro i j hij
    apply e.injective
    rw [her i, her j, hij]
  exact ⟨⟨r, hrinj⟩, hrhigh, hrdisjoint, hrcolor⟩

/-- The discrete core of Lemma 6. These explicit inequalities are the
conditions verified for the paper's asymptotic choices of `c`, `t`, and `q`.
They force the exponential graph of the strong product to have no
`(c+t)`-coloring, including when it has loops. -/
theorem lemma6_discrete_uncolorability {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {q c t : ℕ} (hG : 6 ≤ G.egirth)
    (hn : 4 ≤ Fintype.card V)
    (hc : 16 * (Fintype.card V * t + Fintype.card V ^ 3) ≤ c)
    (hcq : 3 * q + 3 * t + 2 ≤ c)
    (herror : ((2 * q + t + 1 : ℕ) : ℝ) ≤
      (c : ℝ) - robustError (Fintype.card V) c t) :
    IsEmpty ((exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin c ⊕ Fin t)) := by
  refine ⟨fun χ ↦ ?_⟩
  obtain ⟨χ, hχ⟩ := exists_suited_coloring _ χ
  have hq : 2 * q ≤ c := by omega
  obtain ⟨v, hv⟩ := exists_many_robust_colors (loopedGraph_triangleFree_of_six_le_egirth hG)
    (restrictExponentialColoring χ) hχ.restrictExponentialColoring hn hc
  have hcount : 2 * q + t + 1 ≤ (robustColors (restrictExponentialColoring χ) v).card := by
    exact_mod_cast herror.trans hv
  obtain ⟨σ, hσ⟩ := exists_high_robust_colors (restrictExponentialColoring χ) v hcount
  obtain ⟨r, hrhigh, hrdisjoint, hrcolor⟩ :=
    exists_self_colored_mu_maps hG χ hχ v hq hcq σ
  exact lemma6_configuration_impossible χ hχ v hq r σ r.injective σ.injective
    hrdisjoint hrhigh (fun i ↦ (hσ i).1) (fun i ↦ (hσ i).2) hrcolor

/-- The same discrete statement using the standard palette `Fin (c+t)`. -/
theorem lemma6_discrete_no_coloring {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {q c t : ℕ} (hG : 6 ≤ G.egirth)
    (hn : 4 ≤ Fintype.card V)
    (hc : 16 * (Fintype.card V * t + Fintype.card V ^ 3) ≤ c)
    (hcq : 3 * q + 3 * t + 2 ≤ c)
    (herror : ((2 * q + t + 1 : ℕ) : ℝ) ≤
      (c : ℝ) - robustError (Fintype.card V) c t) :
    IsEmpty ((exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin (c + t))) := by
  refine ⟨fun χ ↦ ?_⟩
  exact (lemma6_discrete_uncolorability hG hn hc hcq herror).false
    (recolor finSumFinEquiv.symm χ)

/-- A quantitative version of the error estimate in Lemma 6. It gives
`x ≤ (1/3+δ/2)c` once the lower-order term `n³/c` is small enough. -/
theorem lemma6_error_estimate {n c t : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hδn : (n : ℝ) * δ = 1 / 81) (ht : (t : ℝ) ≤ δ * c)
    (hlarge : (n : ℝ) ^ 3 ≤ δ * c / 27) :
    robustError n c t ≤ (1 / 3 + δ / 2) * c := by
  have hnt : (n : ℝ) * t ≤ (c : ℝ) / 81 := by
    have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
    rw [← mul_assoc, hδn] at hm
    linarith
  have hβ : 0 ≤ (1 / 3 : ℝ) + δ / 2 := by linarith
  have hβlower : (1 / 81 : ℝ) + δ / 27 ≤ (1 / 3 + δ / 2) ^ 4 := by
    nlinarith [sq_nonneg δ, pow_nonneg hδ 3, pow_nonneg hδ 4]
  apply robustError_le_mul hβ
  have hm := mul_le_mul_of_nonneg_right hβlower (Nat.cast_nonneg c)
  nlinarith

/-- Explicit sufficient numerical conditions for the discrete Lemma 6.
These estimates allow integer rounding of the paper's real-valued parameters. -/
theorem lemma6_numeric_conditions {n q c t : ℕ} {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : δ ≤ 1 / 324) (hδn : (n : ℝ) * δ = 1 / 81)
    (ht : (t : ℝ) ≤ δ * c) (hclower : (3 + 10 * δ) * q ≤ c)
    (hq : 4 ≤ δ * q) (hlarge : (n : ℝ) ^ 3 ≤ δ * c / 27) :
    16 * (n * t + n ^ 3) ≤ c ∧ 3 * q + 3 * t + 2 ≤ c ∧
      ((2 * q + t + 1 : ℕ) : ℝ) ≤ (c : ℝ) - robustError n c t := by
  have hδsq : δ ^ 2 ≤ δ / 324 := by
    nlinarith [mul_le_mul_of_nonneg_left hsmall hδ]
  have hnt : (n : ℝ) * t ≤ (c : ℝ) / 81 := by
    have hm := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n)
    rw [← mul_assoc, hδn] at hm
    linarith
  have hc16 : (16 : ℝ) * ((n : ℝ) * t + (n : ℝ) ^ 3) ≤ c := by
    have hm := mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg c)
    nlinarith
  have hB : 0 ≤ 1 - 3 * δ := by linarith
  have hcoefB : 3 + δ / 2 ≤ (1 - 3 * δ) * (3 + 10 * δ) := by nlinarith
  have hcB := mul_le_mul_of_nonneg_left hclower hB
  have hqB := mul_le_mul_of_nonneg_right hcoefB (Nat.cast_nonneg q)
  have hcq : (3 : ℝ) * q + 3 * t + 2 ≤ c := by nlinarith
  have hA : 0 ≤ (2 / 3 : ℝ) - 3 * δ / 2 := by linarith
  have hcoefA : 2 + δ ≤ ((2 / 3 : ℝ) - 3 * δ / 2) * (3 + 10 * δ) := by nlinarith
  have hcA := mul_le_mul_of_nonneg_left hclower hA
  have hqA := mul_le_mul_of_nonneg_right hcoefA (Nat.cast_nonneg q)
  have hx := lemma6_error_estimate hδ hδn ht hlarge
  refine ⟨by exact_mod_cast hc16, by exact_mod_cast hcq, ?_⟩
  push_cast
  nlinarith

/-- Lemma 6 with explicit integer rounding and an explicit sufficient
threshold for `q`. Set `δ=1/(81n)`, `c=ceil((3+10δ)q)`, and `t=floor(δc)`.
The exponential graph has no `(c+t)`-coloring, as required for the paper's
strict lower bound on its chromatic number. -/
theorem lemma6_rounded_no_coloring {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : 6 ≤ G.egirth) (hn : 4 ≤ Fintype.card V)
    (q : ℕ) (hq : Nat.ceil (9 * (Fintype.card V : ℝ) ^ 3 /
      constructionDelta (Fintype.card V)) ≤ q) :
    let δ := constructionDelta (Fintype.card V)
    let c := Nat.ceil ((3 + 10 * δ) * (q : ℝ))
    let t := Nat.floor (δ * (c : ℝ))
    IsEmpty ((exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin (c + t))) := by
  let n := Fintype.card V
  let δ := constructionDelta n
  let c := Nat.ceil ((3 + 10 * δ) * (q : ℝ))
  let t := Nat.floor (δ * (c : ℝ))
  change IsEmpty ((exponentialGraph (Graph.ofSimpleGraph
    (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin (c + t)))
  have hn0 : 0 < n := by dsimp [n]; omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn3 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
    simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hn1 3
  have hδ : 0 < δ := constructionDelta_pos hn0
  have hsmall : δ ≤ 1 / 324 := constructionDelta_le hn
  have hδn : (n : ℝ) * δ = 1 / 81 := mul_constructionDelta hn0
  have ht : (t : ℝ) ≤ δ * c := Nat.floor_le (mul_nonneg hδ.le (Nat.cast_nonneg c))
  have hclower : (3 + 10 * δ) * q ≤ (c : ℝ) := Nat.le_ceil _
  have hqbound : 9 * (n : ℝ) ^ 3 / δ ≤ q := Nat.ceil_le.mp hq
  have hbig : 9 * (n : ℝ) ^ 3 ≤ δ * q := by
    have hm := (div_le_iff₀ hδ).mp hqbound
    nlinarith
  have hq4 : 4 ≤ δ * q := by nlinarith
  have hc3 : (3 : ℝ) * q ≤ c := by
    nlinarith [mul_nonneg hδ.le (Nat.cast_nonneg q)]
  have hlarge : (n : ℝ) ^ 3 ≤ δ * c / 27 := by
    have hm := mul_le_mul_of_nonneg_left hc3 hδ.le
    nlinarith
  obtain ⟨hc, hcq, herror⟩ := lemma6_numeric_conditions hδ.le hsmall hδn ht hclower hq4 hlarge
  exact lemma6_discrete_no_coloring hG hn hc hcq herror

/-- A finite loopless graph with no `floor(x)`-coloring has chromatic
number strictly greater than the real number `x`. -/
theorem real_lt_chromaticNumber_of_no_coloring {W : Type*} [Fintype W]
    (H : Graph W) (hloop : ∀ w, ¬ H.Adj w w) (x : ℝ)
    (hempty : IsEmpty (H.Coloring (Fin (Nat.floor x)))) :
    x < ((H.toSimpleGraph hloop).chromaticNumber.toNat : ℝ) := by
  have hfin : (H.toSimpleGraph hloop).chromaticNumber ≠ ⊤ :=
    (lt_of_le_of_lt (H.toSimpleGraph hloop).chromaticNumber_le_card
      (ENat.natCast_lt_top _)).ne
  have hlt : Nat.floor x < (H.toSimpleGraph hloop).chromaticNumber.toNat := by
    apply lt_of_not_ge
    intro hle
    have hle' : (H.toSimpleGraph hloop).chromaticNumber ≤ (Nat.floor x : ℕ∞) := by
      rw [← ENat.natCast_toNat hfin]
      exact_mod_cast hle
    obtain ⟨χ⟩ := SimpleGraph.chromaticNumber_le_iff_colorable.mp hle'
    exact hempty.false ⟨fun w ↦ χ w, fun {_ _} h ↦ χ.valid h⟩
  have hreal : ((Nat.floor x + 1 : ℕ) : ℝ) ≤
      ((H.toSimpleGraph hloop).chromaticNumber.toNat : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hlt
  exact (Nat.lt_floor_add_one x).trans_le (by simpa using hreal)

/-- Lemma 6 in chromatic-number form, with explicit rounding. Looplessness
is recorded explicitly because the paper only uses chromatic numbers of
simple graphs; it is supplied by the base graph's chromatic lower bound
in the proof of Theorem 1. -/
theorem lemma6_rounded_chromatic_bound {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} (hG : 6 ≤ G.egirth) (hn : 4 ≤ Fintype.card V)
    (q : ℕ) (hq : Nat.ceil (9 * (Fintype.card V : ℝ) ^ 3 /
      constructionDelta (Fintype.card V)) ≤ q)
    (hloop :
      let δ := constructionDelta (Fintype.card V)
      let c := Nat.ceil ((3 + 10 * δ) * (q : ℝ))
      ∀ f, ¬ (exponentialGraph (Graph.ofSimpleGraph
        (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Adj f f) :
    let δ := constructionDelta (Fintype.card V)
    let c := Nat.ceil ((3 + 10 * δ) * (q : ℝ))
    (1 + δ) * (c : ℝ) < (((exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).toSimpleGraph hloop).chromaticNumber.toNat : ℝ) := by
  let n := Fintype.card V
  let δ := constructionDelta n
  let c := Nat.ceil ((3 + 10 * δ) * (q : ℝ))
  let t := Nat.floor (δ * (c : ℝ))
  have hno : IsEmpty ((exponentialGraph (Graph.ofSimpleGraph
      (strongProduct G (⊤ : SimpleGraph (Fin q)))) (Fin c)).Coloring (Fin (c + t))) :=
    lemma6_rounded_no_coloring hG hn q hq
  have hδ : 0 ≤ δ := (constructionDelta_pos (show 0 < n by dsimp [n]; omega)).le
  have hf : Nat.floor ((1 + δ) * (c : ℝ)) = c + t := by
    rw [show (1 + δ) * (c : ℝ) = δ * c + c by ring,
      Nat.floor_add_natCast (mul_nonneg hδ (Nat.cast_nonneg c))]
    change t + c = c + t
    omega
  apply real_lt_chromaticNumber_of_no_coloring
  rw [hf]
  exact hno

/-- Projecting an independent set of `G ⊠ K_q` to `G` preserves independence.
This is the counting property behind the strong-product lower bound in Theorem 1. -/
theorem strongProduct_indepSet_project {V W : Type*} (G : SimpleGraph V)
    {S : Set (V × W)} (hS : (strongProduct G (⊤ : SimpleGraph W)).IsIndepSet S) :
    G.IsIndepSet (Prod.fst '' S) := by
  intro v hv w hw hne hadj
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hw
  apply hS hx hy (fun h ↦ hne (congrArg Prod.fst h))
  refine ⟨Or.inr hadj, ?_, fun h ↦ hne (congrArg Prod.fst h)⟩
  by_cases hxy : x.2 = y.2
  · exact Or.inl hxy
  · exact Or.inr (by simpa using hxy)

/-- An independent set in `G ⊠ K_q` has at most one vertex over each
vertex of `G`, so projection is injective on that set. -/
theorem strongProduct_indepSet_fst_injective {V W : Type*} (G : SimpleGraph V)
    {S : Set (V × W)} (hS : (strongProduct G (⊤ : SimpleGraph W)).IsIndepSet S) :
    Set.InjOn Prod.fst S := by
  intro x hx y hy hfst
  by_contra hne
  apply hS hx hy hne
  refine ⟨Or.inl hfst, ?_, hne⟩
  apply Or.inr
  change x.2 ≠ y.2
  exact fun hsnd ↦ hne (Prod.ext hfst hsnd)

/-- The explicit short-cycle expectation budget used in Lemma 7, for
`n=2,000,000` and `p=8·10⁻⁶=1/125000`. -/
theorem lemma7_cycle_expectation_budget :
    (2000000 : ℝ) ^ 3 * (1 / 125000 : ℝ) ^ 3 / 6 +
      (2000000 : ℝ) ^ 4 * (1 / 125000 : ℝ) ^ 4 / 8 +
      (2000000 : ℝ) ^ 5 * (1 / 125000 : ℝ) ^ 5 / 10 ≤ 115000 := by
  norm_num

/-- The final independence-ratio estimate in Lemma 7 after deleting at
most `230000` vertices from the initial graph on `2000000` vertices. -/
theorem lemma7_fractional_bound_of_indepNum {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hvertices : 1770000 ≤ Fintype.card V) (hind : G.indepNum ≤ 570000) :
    (31 / 10 : ℝ) ≤ fractionalChromaticNumber G := by
  calc
    (31 / 10 : ℝ) ≤ (Fintype.card V : ℝ) / 570000 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 570000)).mpr
      have hV : (1770000 : ℝ) ≤ Fintype.card V := by exact_mod_cast hvertices
      linarith
    _ ≤ fractionalChromaticNumber G := card_div_le_fractionalChromaticNumber G
      (by norm_num : 0 < (570000 : ℕ)) (fun S hS ↦ hS.card_le_indepNum.trans hind)

/-- An independent set in `G ⊠ K_q` has no more vertices than a largest
independent set of `G`. -/
theorem strongProduct_indepSet_card_le {V W : Type*} [Finite V] (G : SimpleGraph V)
    {S : Finset (V × W)} (hS : (strongProduct G (⊤ : SimpleGraph W)).IsIndepSet (S : Set (V × W))) :
    S.card ≤ G.indepNum := by
  classical
  have hproj : G.IsIndepSet ((S.image Prod.fst : Finset V) : Set V) := by
    simpa only [Finset.coe_image] using strongProduct_indepSet_project G hS
  calc
    S.card = (S.image Prod.fst).card :=
      (Finset.card_image_iff.mpr (strongProduct_indepSet_fst_injective G hS)).symm
    _ ≤ G.indepNum := hproj.card_le_indepNum

/-- Counting color classes gives the strong-product chromatic lower
bound needed in the final construction, expressed for an arbitrary finite palette. -/
theorem strongProduct_coloring_card_bound {V W C : Type*}
    [Fintype V] [Fintype W] [Fintype C] (G : SimpleGraph V)
    (χ : (strongProduct G (⊤ : SimpleGraph W)).Coloring C) :
    Fintype.card V * Fintype.card W ≤ Fintype.card C * G.indepNum := by
  classical
  calc
    Fintype.card V * Fintype.card W = (Finset.univ : Finset (V × W)).card := by simp
    _ = ∑ b : C, (Finset.univ.filter (fun x : V × W ↦ χ x = b)).card :=
      Finset.card_eq_sum_card_fiberwise (f := fun x ↦ χ x) (fun _ _ ↦ Finset.mem_univ _)
    _ ≤ ∑ _b : C, G.indepNum := by
      apply Finset.sum_le_sum
      intro b _
      apply strongProduct_indepSet_card_le
      intro x hx y hy _ hxy
      exact χ.valid hxy ((Finset.mem_filter.mp hx).2.trans (Finset.mem_filter.mp hy).2.symm)
    _ = Fintype.card C * G.indepNum := by simp

/-- The explicit independent-set union estimate in Lemma 7. The proof
uses symbolic exponential bounds instead of evaluating the huge binomial
coefficient or power. -/
theorem lemma7_independent_set_union_budget :
    ((2000000 : ℕ).choose 570000 : ℝ) *
      (1 - (1 / 125000 : ℝ)) ^ ((570000 : ℕ).choose 2) < 1 / 4 := by
  calc
    _ ≤ Real.exp ((11 / 10 : ℝ) * 2000000 -
        (2 / 3 : ℝ) * (2000000 - 570000 : ℕ) -
        (1 / 125000 : ℝ) * ((570000 : ℕ).choose 2)) :=
      choose_mul_one_sub_pow_le_exp 2000000 570000 ((570000 : ℕ).choose 2)
        (by norm_num) (1 / 125000) (by norm_num)
    _ ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by norm_num [Nat.choose_two_right])
    _ < 1 / 4 := exp_neg_two_lt_quarter

/-- Every cycle is covered by a canonical placement with the same vertices and edges. -/
theorem cycle_has_cyclePlacement {V : Type*} [LinearOrder V] {G : SimpleGraph V}
    {v : V} (w : G.Walk v v) (hc : w.IsCycle) {m : ℕ} (hl : w.length = m + 3) :
    ∃ P : CyclePlacement V m,
      (∀ x ∈ P.1.val, x ∈ w.support) ∧
      ∀ e ∈ placeCycleEdges P.1.val P.1.property P.2.val, e ∈ G.edgeSet := by
  classical
  let f : Fin (m + 3) → V := fun i ↦ w.getVert i.val
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    exact hc.getVert_injOn' (by dsimp; omega) (by dsimp; omega) hij
  obtain ⟨P, hP, he⟩ := exists_cyclePlacement f hf
  refine ⟨P, ?_, ?_⟩
  · intro x hx
    rw [hP] at hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact w.getVert_mem_support i.val
  · intro e he'
    rw [he] at he'
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp he'
    rw [SimpleGraph.mem_edgeSet]
    have hi : i.val < w.length := by omega
    have hadj := w.adj_getVert_succ hi
    by_cases h : i.val + 1 < m + 3
    · have hs : (i + 1).val = i.val + 1 := by
        change (i.val + 1) % (m + 3) = i.val + 1
        exact Nat.mod_eq_of_lt h
      simpa only [f, hs] using hadj
    · have hlast : i.val + 1 = w.length := by omega
      have hs : (i + 1).val = 0 := by
        change (i.val + 1) % (m + 3) = 0
        have : i.val + 1 = m + 3 := by omega
        simp [this]
      simpa only [f, hs, hlast, w.getVert_length, w.getVert_zero] using hadj

/-- Removing a set that hits every cycle placement of lengths three through five
leaves a graph of extended girth at least six. -/
theorem six_le_egirth_induce_of_hit_cyclePlacements {V : Type*} [LinearOrder V]
    (G : SimpleGraph V) (D : Finset V)
    (hD : ∀ m ≤ 2, ∀ P : CyclePlacement V m,
      (∀ e ∈ placeCycleEdges P.1.val P.1.property P.2.val, e ∈ G.edgeSet) →
        ∃ x ∈ P.1.val, x ∈ D) :
    6 ≤ (G.induce {v | v ∉ D}).egirth := by
  rw [SimpleGraph.le_egirth]
  intro v w hc
  suffices 6 ≤ w.length by exact_mod_cast this
  by_contra hlen
  have hshort : w.length < 6 := by omega
  have hthree := hc.three_le_length
  let φ : G.induce {v | v ∉ D} →g G :=
    { toFun := Subtype.val, map_rel' := fun h ↦ h }
  have hc' : (w.map φ).IsCycle := hc.map Subtype.val_injective
  obtain ⟨P, hverts, hedges⟩ := cycle_has_cyclePlacement (w.map φ) hc'
    (m := w.length - 3) (by simp only [SimpleGraph.Walk.length_map]; omega)
  obtain ⟨x, hx, hxD⟩ := hD (w.length - 3) (by omega) P hedges
  have hxw := hverts x hx
  rw [SimpleGraph.Walk.support_map] at hxw
  obtain ⟨y, _, hy⟩ := List.mem_map.mp hxw
  apply y.property
  change φ y ∈ D
  rw [hy]
  exact hxD

/-- Deleting one vertex from each present short cycle removes all short cycles. -/
theorem exists_shortCycle_deletion {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) :
    ∃ D : Finset V,
      D.card ≤ ∑ m ∈ Finset.range 3, (presentCyclePlacements G m).card ∧
      6 ≤ (G.induce {v | v ∉ D}).egirth := by
  classical
  have hn (m : ℕ) (P : CyclePlacement V m) : P.1.val.Nonempty := by
    apply Finset.card_pos.mp
    rw [P.1.property]
    omega
  let pick (m : ℕ) (P : CyclePlacement V m) := P.1.val.min' (hn m P)
  let D := (Finset.range 3).biUnion (fun m ↦ (presentCyclePlacements G m).image (pick m))
  refine ⟨D, ?_, ?_⟩
  · exact (Finset.card_biUnion_le).trans (Finset.sum_le_sum (fun m _ ↦ Finset.card_image_le))
  · apply six_le_egirth_induce_of_hit_cyclePlacements
    intro m hm P hP
    refine ⟨pick m P, Finset.min'_mem _ _, ?_⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨m, Finset.mem_range.mpr (by omega), ?_⟩
    apply Finset.mem_image.mpr
    exact ⟨P, (mem_presentCyclePlacements G P).mpr hP, rfl⟩

/-- The deterministic deletion step in Lemma 7, including the vertex and
fractional-chromatic bounds needed in the final construction. -/
theorem lemma7_deletion_conclusion {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hvertices : Fintype.card V = 2000000)
    (hind : G.indepNum ≤ 570000)
    (hcycles : ∑ m ∈ Finset.range 3, (presentCyclePlacements G m).card ≤ 230000) :
    ∃ D : Finset V,
      1770000 ≤ Fintype.card {v // v ∉ D} ∧
      Fintype.card {v // v ∉ D} ≤ 2000000 ∧
      6 ≤ (G.induce {v | v ∉ D}).egirth ∧
      (31 / 10 : ℝ) ≤ fractionalChromaticNumber (G.induce {v | v ∉ D}) := by
  classical
  obtain ⟨D, hD, hgirth⟩ := exists_shortCycle_deletion G
  have hcard : Fintype.card {v // v ∉ D} = Fintype.card V - D.card := by
    rw [Fintype.card_subtype_compl]
    simp
  have hlow : 1770000 ≤ Fintype.card {v // v ∉ D} := by
    rw [hcard, hvertices]
    omega
  refine ⟨D, hlow, ?_, hgirth, ?_⟩
  · rw [hcard, hvertices]
    omega
  · exact lemma7_fractional_bound_of_indepNum _ hlow ((indepNum_induce_le G _).trans hind)

/-- Integer rounding for the final construction, with an additive loss below four. -/
theorem construction_rounding (δ : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 324)
    (c : ℕ) :
    ∃ q c' : ℕ, c' = ⌈(3 + 10 * δ) * q⌉₊ ∧ c' ≤ c ∧
      (c : ℝ) - 4 < c' ∧ (c : ℝ) / (3 + 10 * δ) - 1 < q := by
  let a := 3 + 10 * δ
  have ha : 0 < a := by dsimp [a]; linarith
  have hasmall : a < 4 := by dsimp [a]; linarith
  let q := ⌊(c : ℝ) / a⌋₊
  let c' := ⌈a * q⌉₊
  have hqlo : (q : ℝ) ≤ (c : ℝ) / a := Nat.floor_le (by positivity)
  have hqhi : (c : ℝ) / a < (q : ℝ) + 1 := Nat.lt_floor_add_one _
  have hprod : a * q ≤ (c : ℝ) := by
    simpa only [mul_comm] using (le_div_iff₀ ha).mp hqlo
  have hceil : a * q ≤ (c' : ℝ) := Nat.le_ceil _
  refine ⟨q, c', rfl, Nat.ceil_le.mpr hprod, ?_, ?_⟩
  · have h := (div_lt_iff₀ ha).mp hqhi
    nlinarith
  · linarith

/-- The final multiplicative gain absorbs both integer-rounding errors. -/
theorem construction_rounded_gain (δ : ℝ)
    (hδ : 1 / 162000000 ≤ δ) (hδsmall : δ ≤ 1 / 324)
    {c q c' : ℕ} (hc : 2000000000 ≤ c)
    (hc' : (c : ℝ) - 4 < c')
    (hq : (c : ℝ) / (3 + 10 * δ) - 1 < q) :
    (1 + 1 / 1000000000 : ℝ) * c < (1 + δ) * c' ∧
      (1 + 1 / 1000000000 : ℝ) * c < (31 / 10 : ℝ) * q := by
  have hcR : (2000000000 : ℝ) ≤ c := by exact_mod_cast hc
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hδ0 : 0 ≤ δ := by linarith
  constructor
  · have hδc := mul_le_mul_of_nonneg_right hδ hc0
    have hfirst := mul_lt_mul_of_pos_left hc' (show (0 : ℝ) < 1 + δ by linarith)
    nlinarith
  · have ha : 0 < 3 + 10 * δ := by linarith
    have hq' : (c : ℝ) < ((q : ℝ) + 1) * (3 + 10 * δ) := by
      apply (div_lt_iff₀ ha).mp
      linarith
    have hδq := mul_le_mul_of_nonneg_right hδsmall (Nat.cast_nonneg q)
    have hcq : (c : ℝ) < ((q : ℝ) + 1) * (3 + 10 / 324) := by nlinarith
    nlinarith

/-- The base graph in the final construction inherits the required chromatic
lower bound from the quantitative witness in Lemma 7. -/
theorem lemma7_strongProduct_chromatic_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hvertices : 1770000 ≤ Fintype.card V)
    (hind : G.indepNum ≤ 570000) (q : ℕ) :
    (31 / 10 : ℝ) * q ≤
      ((strongProduct G (⊤ : SimpleGraph (Fin q))).chromaticNumber.toNat : ℝ) := by
  classical
  let H := strongProduct G (⊤ : SimpleGraph (Fin q))
  let k := H.chromaticNumber.toNat
  have hfin : H.chromaticNumber ≠ ⊤ :=
    (lt_of_le_of_lt H.chromaticNumber_le_card (ENat.natCast_lt_top _)).ne
  have hcolor : H.Colorable k := by
    apply SimpleGraph.chromaticNumber_le_iff_colorable.mp
    rw [ENat.natCast_toNat hfin]
  obtain ⟨χ⟩ := hcolor
  have hcount := strongProduct_coloring_card_bound G χ
  simp only [Fintype.card_fin] at hcount
  have hbound : Fintype.card V * q ≤ k * 570000 := by
    exact hcount.trans (Nat.mul_le_mul_left k hind)
  have hN : (1770000 : ℝ) ≤ Fintype.card V := by exact_mod_cast hvertices
  have hcountR : (Fintype.card V : ℝ) * q ≤ (k : ℝ) * 570000 := by exact_mod_cast hbound
  have hNq := mul_le_mul_of_nonneg_right hN (Nat.cast_nonneg q)
  change (31 / 10 : ℝ) * q ≤ (k : ℝ)
  nlinarith

/-- Rounded construction parameters exist above any prescribed threshold. -/
theorem construction_rounding_large (δ : ℝ) (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1 / 324)
    (Q : ℕ) :
    ∃ C₀ : ℕ, ∀ c ≥ C₀, ∃ q c' : ℕ,
      2000000000 ≤ c ∧ Q ≤ q ∧ c' = ⌈(3 + 10 * δ) * q⌉₊ ∧ c' ≤ c ∧
      (c : ℝ) - 4 < c' ∧ (c : ℝ) / (3 + 10 * δ) - 1 < q := by
  let a := 3 + 10 * δ
  have ha : 0 < a := by dsimp [a]; linarith
  refine ⟨max 2000000000 ⌈a * (Q + 1)⌉₊, ?_⟩
  intro c hc
  have hcbig : 2000000000 ≤ c := (le_max_left _ _).trans hc
  have hcceil : ⌈a * (Q + 1)⌉₊ ≤ c := (le_max_right _ _).trans hc
  have hca : a * (Q + 1) ≤ (c : ℝ) := Nat.ceil_le.mp hcceil
  have hdiv : (Q : ℝ) + 1 ≤ (c : ℝ) / a := by
    apply (le_div_iff₀ ha).mpr
    nlinarith
  obtain ⟨q, c', heq, hle, hnear, hq⟩ := construction_rounding δ hδ hδsmall c
  have hQ : (Q : ℝ) ≤ q := by dsimp [a] at hdiv; linarith
  exact ⟨q, c', hcbig, by exact_mod_cast hQ, heq, hle, hnear, hq⟩

end Hedetniemi
