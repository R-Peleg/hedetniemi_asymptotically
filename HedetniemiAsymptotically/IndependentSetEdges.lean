import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Data.Sym.Card

namespace Hedetniemi

/-- Independence is the absence of all unordered pairs of distinct vertices. -/
theorem isIndepSet_iff_disjoint_pairEdges {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) :
    G.IsIndepSet (S : Set V) ↔
      Disjoint ((S.offDiag.image Sym2.mk.uncurry : Finset (Sym2 V)) : Set (Sym2 V))
        G.edgeSet := by
  constructor
  · intro h
    apply Set.disjoint_left.mpr
    intro e he heG
    obtain ⟨⟨v, w⟩, hvw, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hv, hw, hne⟩ := Finset.mem_offDiag.mp hvw
    exact h hv hw hne heG
  · intro h v hv w hw hne hadj
    exact Set.disjoint_left.mp h
      (show s(v, w) ∈ S.offDiag.image Sym2.mk.uncurry from
        Finset.mem_image.mpr ⟨(v, w), Finset.mem_offDiag.mpr ⟨hv, hw, hne⟩, rfl⟩) hadj

end Hedetniemi
