import HedetniemiAsymptotically.Main

/-!
# Size of the counterexamples

`Main.lean` proves Theorem 1 without recording how large the graphs are. This
file reruns the same construction (it does not modify `Main.lean`) and tracks
the vertex counts.

For a target `c`, the construction uses
* `H₁ = G ⊠ K_q` on `V × Fin q`, where `G` is the Lemma 7 graph with
  `n = |V| ≤ 2·10⁶` vertices and `3q ≤ c`;
* `H₂ = (G ⊠ K_q)^{K_{c'}}` (the exponential graph), whose vertices are all maps
  `V × Fin q → Fin c'` with `c' ≤ c`.

So `|V(H₁)| = n q ≤ 666667 c`, `|V(H₂)| = c'^{n q} ≤ c^{666667 c}`, and the
tensor product `H₁ × H₂` has at most `666667 c · c^{666667 c}` vertices.
A trivial lower bound also holds: each factor has more than `c` vertices,
because its chromatic number is greater than `c`.
-/

namespace Hedetniemi

/-- A finite simple graph with chromatic number above `c` has more than `c`
vertices. -/
theorem lt_card_of_lt_chromaticNumber {W : Type*} [Fintype W] (H : SimpleGraph W)
    {c : ℕ} (h : (1 + 1 / 1000000000 : ℝ) * c < (H.chromaticNumber.toNat : ℝ)) :
    c < Fintype.card W := by
  have hfin : H.chromaticNumber ≠ ⊤ :=
    (lt_of_le_of_lt H.chromaticNumber_le_card (ENat.natCast_lt_top _)).ne
  have hle : H.chromaticNumber.toNat ≤ Fintype.card W := by
    have := H.chromaticNumber_le_card
    exact_mod_cast (show (H.chromaticNumber.toNat : ℕ∞) ≤ Fintype.card W by
      simpa only [ENat.natCast_toNat hfin] using this)
  have hc : (c : ℝ) < (H.chromaticNumber.toNat : ℝ) := by
    nlinarith [show (0 : ℝ) ≤ c from Nat.cast_nonneg c]
  have : c < H.chromaticNumber.toNat := by exact_mod_cast hc
  omega

/-- `theorem1_of_lemma7_witness`, with explicit bounds on the vertex counts. -/
theorem theorem1_of_lemma7_witness_sized {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hN : 1770000 ≤ Fintype.card V)
    (hNupper : Fintype.card V ≤ 2000000) (hgirth : 6 ≤ G.egirth)
    (hind : G.indepNum ≤ 570000) :
    ∃ C₀ : ℕ, ∀ c ≥ C₀,
      ∃ (W₁ W₂ : Type) (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
        Finite W₁ ∧ Finite W₂ ∧
        (1 + 1 / 1000000000 : ℝ) * c < (H₁.chromaticNumber.toNat : ℝ) ∧
        (1 + 1 / 1000000000 : ℝ) * c < (H₂.chromaticNumber.toNat : ℝ) ∧
        (tensorSimpleLeft H₁ (Graph.ofSimpleGraph H₂)).chromaticNumber ≤ c ∧
        c < Nat.card W₁ ∧ c < Nat.card W₂ ∧
        Nat.card W₁ ≤ 666667 * c ∧
        Nat.card W₂ ≤ c ^ (666667 * c) ∧
        Nat.card (W₁ × W₂) ≤ 666667 * c * c ^ (666667 * c) := by
  classical
  let n := Fintype.card V
  let δ := constructionDelta n
  have hn : 4 ≤ n := by dsimp [n]; omega
  have hδ : 0 < δ := constructionDelta_pos (by omega)
  have hδsmall : δ ≤ 1 / 324 := constructionDelta_le hn
  have hδlower : 1 / 162000000 ≤ δ := constructionDelta_lower_bound (by omega) hNupper
  let Q := ⌈9 * (n : ℝ) ^ 3 / δ⌉₊
  obtain ⟨C₀, hC₀⟩ := construction_rounding_large δ hδ.le hδsmall Q
  refine ⟨C₀, ?_⟩
  intro c hc
  obtain ⟨q, c', hcbig, hq, hc'eq, hc'le, hc'near, hqnear⟩ := hC₀ c hc
  obtain ⟨hgainExp, hgainBase⟩ := construction_rounded_gain δ hδlower hδsmall hcbig hc'near hqnear
  -- Size bookkeeping: `3 q ≤ c' ≤ c`.
  have h3q : 3 * q ≤ c' := by
    have hceil : (3 + 10 * δ) * q ≤ (c' : ℝ) := hc'eq ▸ Nat.le_ceil _
    have h : (3 * q : ℝ) ≤ c' := by nlinarith [show (0 : ℝ) ≤ q from Nat.cast_nonneg q]
    exact_mod_cast h
  have hnq : n * q ≤ 666667 * c := by
    have : n * q ≤ 2000000 * q := Nat.mul_le_mul_right q hNupper
    omega
  have hc1 : 1 ≤ c := by omega
  have hW₂ : c' ^ (n * q) ≤ c ^ (666667 * c) :=
    (Nat.pow_le_pow_left hc'le _).trans (Nat.pow_le_pow_right hc1 hnq)
  -- The construction itself, exactly as in `theorem1_of_lemma7_witness`.
  let H := strongProduct G (⊤ : SimpleGraph (Fin q))
  have hbase : (31 / 10 : ℝ) * q ≤ (H.chromaticNumber.toNat : ℝ) :=
    lemma7_strongProduct_chromatic_bound G hN hind q
  have hbaseGain : (1 + 1 / 1000000000 : ℝ) * c < (H.chromaticNumber.toNat : ℝ) :=
    hgainBase.trans_le hbase
  have hc'base : (c' : ℝ) < (H.chromaticNumber.toNat : ℝ) := by
    have hcle : (c' : ℝ) ≤ c := by exact_mod_cast hc'le
    nlinarith [show (0 : ℝ) ≤ c from Nat.cast_nonneg c]
  have hno : IsEmpty ((Graph.ofSimpleGraph H).Coloring (Fin c')) := by
    refine ⟨fun χ ↦ ?_⟩
    have hcol : H.Colorable c' := ⟨SimpleGraph.Coloring.mk χ.val (fun h ↦ χ.property h)⟩
    have hfin : H.chromaticNumber ≠ ⊤ :=
      (lt_of_le_of_lt H.chromaticNumber_le_card (ENat.natCast_lt_top _)).ne
    have hle := SimpleGraph.chromaticNumber_le_iff_colorable.mpr hcol
    have hleNat : H.chromaticNumber.toNat ≤ c' := by
      exact_mod_cast (show (H.chromaticNumber.toNat : ℕ∞) ≤ c' by
        simpa only [ENat.natCast_toNat hfin] using hle)
    have hleR : (H.chromaticNumber.toNat : ℝ) ≤ c' := by exact_mod_cast hleNat
    linarith
  have hloop : ∀ f, ¬ (exponentialGraph (Graph.ofSimpleGraph H) (Fin c')).Adj f f :=
    (exponentialGraph_loopless_iff _).mpr hno
  let E := (exponentialGraph (Graph.ofSimpleGraph H) (Fin c')).toSimpleGraph hloop
  have hexp : (1 + δ) * (c' : ℝ) < (E.chromaticNumber.toNat : ℝ) := by
    subst c'
    exact lemma6_rounded_chromatic_bound hgirth hn q hq hloop
  have hEgain : (1 + 1 / 1000000000 : ℝ) * c < (E.chromaticNumber.toNat : ℝ) :=
    hgainExp.trans hexp
  have hcardW₁ : Nat.card (V × Fin q) = n * q := by
    simp [Nat.card_eq_fintype_card, n]
  have hcardW₂ : Nat.card (V × Fin q → Fin c') = c' ^ (n * q) := by
    simp [Nat.card_eq_fintype_card, n]
  refine ⟨V × Fin q, (V × Fin q → Fin c'), H, E, inferInstance, inferInstance,
    hbaseGain, hEgain,
    (evaluation_chromaticNumber_le H c').trans (by exact_mod_cast hc'le), ?_, ?_, ?_, ?_, ?_⟩
  · rw [Nat.card_eq_fintype_card]; exact lt_card_of_lt_chromaticNumber H hbaseGain
  · rw [Nat.card_eq_fintype_card]; exact lt_card_of_lt_chromaticNumber E hEgain
  · rw [hcardW₁]; exact hnq
  · rw [hcardW₂]; exact hW₂
  · rw [Nat.card_prod, hcardW₁, hcardW₂]
    exact Nat.mul_le_mul hnq hW₂

/-- Theorem 1 with explicit size bounds. For every sufficiently large `c`, the
counterexample `H₁ × H₂` has at most `666667 c · c^{666667 c}` vertices, and each
factor necessarily has more than `c` vertices. -/
theorem theorem1_sized :
    ∃ C₀ : ℕ, ∀ c ≥ C₀,
      ∃ (W₁ W₂ : Type) (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂),
        Finite W₁ ∧ Finite W₂ ∧
        (1 + 1 / 1000000000 : ℝ) * c < (H₁.chromaticNumber.toNat : ℝ) ∧
        (1 + 1 / 1000000000 : ℝ) * c < (H₂.chromaticNumber.toNat : ℝ) ∧
        (tensorSimpleLeft H₁ (Graph.ofSimpleGraph H₂)).chromaticNumber ≤ c ∧
        c < Nat.card W₁ ∧ c < Nat.card W₂ ∧
        Nat.card W₁ ≤ 666667 * c ∧
        Nat.card W₂ ≤ c ^ (666667 * c) ∧
        Nat.card (W₁ × W₂) ≤ 666667 * c * c ^ (666667 * c) := by
  classical
  obtain ⟨G, D, hlow, hupp, hgirth, hind, _⟩ := lemma7_quantitative
  exact theorem1_of_lemma7_witness_sized (G.induce {v | v ∉ D}) hlow hupp hgirth hind

end Hedetniemi
