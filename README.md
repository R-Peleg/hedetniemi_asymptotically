# Hedetniemi's conjecture is asymptotically false

Lean formalization in progress of He and Wigderson, `pdf/main.pdf`
(arXiv:1906.06783v3). Uses Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

Build with `lake build`.

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

Remaining paper results:

- Lemma 7: random-graph edge-event probabilities, short-cycle expectation
  and independent-set union bounds, selection of a graph satisfying both,
  and vertex deletion to obtain girth at least six. The deterministic
  fractional-chromatic conclusion after deletion is checked.
- Theorem 1: simplicity of the exponential, combination with Lemma 2 and Lemma 6,
  and rounding to cover all sufficiently large integers.

Lemma 4 uses Mathlib's `Finset.erdos_ko_rado` from
`Mathlib.Combinatorics.SetFamily.KruskalKatona`. Its image-size layers are
weighted using equal surjection counts, then compared with all maps whose
image contains a prescribed color. The elementary finite-map counting
lemmas are in `MapCounting.lean`.

The workspace's `.git` is an empty read-only mount. Requested commits are
stored in `.git-local`; inspect them with
`git --git-dir=.git-local --work-tree=. log`.

The local `.lake/packages` reuses the installed Mathlib sources/cache. It is
ignored by Git; the manifest pins the normal upstream dependencies for a
fresh installation.
