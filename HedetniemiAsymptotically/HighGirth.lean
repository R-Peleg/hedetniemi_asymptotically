import HedetniemiAsymptotically.LoopedGraph
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace Hedetniemi

theorem no_triangle_of_four_le_egirth {V : Type*} {G : SimpleGraph V}
    (hG : 4 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  let w : G.Walk a a := .cons hab (.cons hbc (.cons hca .nil))
  have hw : w.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · simp [w, SimpleGraph.Walk.isPath_def, hbc.ne, hab.ne', hca.ne]
    · simp [w]
  have hbound := hG.trans hw.egirth_le_length
  norm_num [w] at hbound

/-- A girth bound of six excludes triangles, including closed three-step
walks presented without distinctness assumptions. -/
theorem no_triangle_of_six_le_egirth {V : Type*} {G : SimpleGraph V}
    (hG : 6 ≤ G.egirth) {a b c : V}
    (hab : G.Adj a b) (hbc : G.Adj b c) (hca : G.Adj c a) : False := by
  exact no_triangle_of_four_le_egirth (le_trans (by norm_num) hG)
    hab hbc hca

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

end Hedetniemi
