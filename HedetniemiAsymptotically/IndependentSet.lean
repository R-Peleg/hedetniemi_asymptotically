import HedetniemiAsymptotically.Graph

namespace Hedetniemi.Graph

/-- An independent set has no edges between distinct vertices. Loops do not
affect this definition, matching pairwise independence for simple graphs. -/
def IsIndependent {V : Type*} (G : Graph V) (S : Set V) : Prop :=
  S.Pairwise (fun v w ↦ ¬ G.Adj v w)

/-- Each color class is independent. -/
theorem Coloring.isIndependent_fiber {V C : Type*} {G : Graph V}
    (χ : G.Coloring C) (b : C) : G.IsIndependent {v | χ.val v = b} := by
  intro v hv w hw _ hadj
  exact χ.property hadj (hv.trans hw.symm)

end Hedetniemi.Graph
