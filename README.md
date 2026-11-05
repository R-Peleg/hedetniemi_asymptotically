# Hedetniemi's conjecture is asymptotically false

Lean formalization of He and Wigderson, `pdf/main.pdf`
(arXiv:1906.06783v3). Uses Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Build with `lake build`. The complete root target passes. The axiom audits of
`Hedetniemi.theorem1` and `Hedetniemi.theorem1_sized` use only `propext`,
`Classical.choice`, and `Quot.sound`; the project contains no `sorry`,
`admit`, or added axioms.

Paper proofs belong in `HedetniemiAsymptotically/Main.lean`. Definitions
and basic technical facts have their own modules. Cited results missing from
Mathlib belong in dedicated modules: `ElZaharSauer.lean` proves the evaluation
coloring (Lemma 2). Graphs with loops are represented explicitly; the bridge
to Mathlib's simple graphs is in `Graph.lean`.

Primary and secondary colors are represented by a sum type `C ⊕ D`.
Specializing to `Fin c ⊕ Fin t` gives the paper's palette of `c+t` colors.

Checked results include Lemma 2 (both the evaluation coloring and its Mathlib
chromatic-number bound), Lemma 3 (existence of a suited coloring), Lemma 4
(the full independent-family cardinality bound for a nonempty vertex set),
Lemma 5 (the robust-color theorem with the paper's numerical hypotheses), and the
basic symmetry, containment, and looplessness properties of exponential graphs.
Lemma 5 includes the large-fiber counting argument, the triangle-free clique
bound, the upper count on maps avoiding large fibers, double counting of
excluded vertex/color pairs, and the strict product estimate derived from
Mathlib's strict concavity of `log`. The fourth-root error term and its basic
arithmetic are in `RobustError.lean`.

The strong product, adding loops, and exponential lifting from Section 4
are defined and checked. Lifting is injective and preserves co-properness;
it reflects co-properness when the second factor contains an edge.

Lemma 6 is checked, including both map cliques, both color selections,
the final coloring contradiction, and the numerical parameter estimates.
Its rounded version uses `δ = 1/(81n)`, `c = ceil((3+10δ)q)`, and
`t = floor(δc)` with the explicit sufficient threshold
`q ≥ ceil(9n³/δ)`. The chromatic-number form records looplessness explicitly,
as required by the paper's convention; the coloring obstruction also holds
for graphs with loops.

Fractional colorings and the fractional chromatic number are defined in
their own files. Checked basic results include nonnegativity, the singleton
upper bound, and the independence-ratio lower bound used in Lemma 7.
The numerical short-cycle and independent-set budgets of Lemma 7 are checked.
Finite undirected cycle templates have kernel-checked counts `1`, `3`, and
`12` on three, four, and five vertices respectively.

The strong-product counting bound is also checked: any finite coloring of
`G ⊠ K_q` satisfies `|V(G)|q ≤ (number of colors) · indepNum(G)`.
Every short cycle is represented by a canonical placement. Deleting one
vertex per present placement removes all cycles of lengths three through
five; the deletion budget, surviving vertex count, independence-number
bound, and fractional-chromatic conclusion are checked.

Lemma 7 is checked in full (`lemma7_quantitative`), including the binomial
random graph, exact finite-edge probabilities, short-cycle expectation,
Markov and independent-set union bounds, graph selection, and deletion.
It retains the vertex and independence-number bounds used by Theorem 1.

Theorem 1 is proved in `HedetniemiAsymptotically/Main.lean` as
`Hedetniemi.theorem1`. For every sufficiently large integer `c`, it constructs
two finite simple graphs whose chromatic numbers are strictly greater than
`(1 + 1/1000000000) * c`, while their tensor product has chromatic number
at most `c`. The proof includes looplessness of the exponential and rounding
for every integer target. The intermediate theorem
`theorem1_of_lemma7_witness` records the construction from a quantitative witness.

`HedetniemiAsymptotically/ProductSize.lean` records how large the
counterexamples are, leaving `Main.lean` unchanged. It reruns the construction
as `Hedetniemi.theorem1_sized`, which proves everything in `theorem1` and also
bounds the vertex sets `W₁` of `H₁ = G ⊠ K_q` and `W₂` of the exponential
graph `H₂`: `c < |W₁| ≤ 666667c`, `c < |W₂| ≤ c^(666667c)`, and
`|W₁ × W₂| ≤ 666667c · c^(666667c)`. The upper bounds follow from
`|V(G)| ≤ 2000000` and `3q ≤ c' ≤ c`. They describe this construction only.
The lower bounds are the trivial ones implied by chromatic number above `c`.

Finite-edge probability formulas are in `BernoulliSetEvents.lean` and
`BinomialGraphEvents.lean`; the general expected-event-count formula is in
`FiniteEventCount.lean`.

Lemma 4 uses Mathlib's `Finset.erdos_ko_rado` from
`Mathlib.Combinatorics.SetFamily.KruskalKatona`. Its image-size layers are
weighted using equal surjection counts, then compared with all maps whose
image contains a prescribed color. The elementary finite-map counting
lemmas are in `MapCounting.lean`.

The local `.lake/packages` reuses the installed Mathlib sources/cache. It is
ignored by Git; the manifest pins the normal upstream dependencies for a
fresh installation.
