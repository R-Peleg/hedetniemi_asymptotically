import Mathlib.Combinatorics.SimpleGraph.Clique

namespace Hedetniemi

/-- Passing to an induced subgraph cannot increase the independence number. -/
theorem indepNum_induce_le {V : Type*} [Finite V] (G : SimpleGraph V) (S : Set V) :
    (G.induce S).indepNum ≤ G.indepNum := by
  classical
  obtain ⟨t, ht⟩ := (G.induce S).exists_isNIndepSet_indepNum
  have ht' : G.IsNIndepSet (G.induce S).indepNum
      (t.map ⟨Subtype.val, Subtype.val_injective⟩) :=
    (SimpleGraph.isNIndepSet_induce G).mp (by
      rw [← G.induce_eq_coe_induce_top]
      exact ht)
  rw [← ht'.card_eq]
  exact ht'.isIndepSet.card_le_indepNum

end Hedetniemi
