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
chromatic-number bound), Lemma 3 (existence of a suited coloring), and the
basic symmetry, containment, and looplessness properties of exponential graphs.
The robust-color definition and the unique-support clique step of Lemma 5
are also checked; its counting estimates remain to be proved.

Remaining paper results:

- Lemma 4: independence bound for exponential graphs. The cited
  Erdős–Ko–Rado theorem is available as `Finset.erdos_ko_rado` in
  `Mathlib.Combinatorics.SetFamily.KruskalKatona`.
- Lemma 5: robust colors and the counting argument.
- Lemma 6: construction from a graph of girth at least six.
- Lemma 7: probabilistic existence with explicit numerical bounds.
- Theorem 1, including rounding to cover all sufficiently large integers.

The workspace's `.git` is an empty read-only mount. Requested commits are
stored in `.git-local`; inspect them with
`git --git-dir=.git-local --work-tree=. log`.

The local `.lake/packages` reuses the installed Mathlib sources/cache. It is
ignored by Git; the manifest pins the normal upstream dependencies for a
fresh installation.
