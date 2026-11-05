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
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Combinatorics.SetFamily.KruskalKatona
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

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

end Hedetniemi
