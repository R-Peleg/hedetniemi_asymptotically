import HedetniemiAsymptotically.Graph

namespace Hedetniemi.Graph

/-- Triangle-freeness refers to three distinct vertices, so loops are ignored,
as in the application of Lemma 5 to a graph with loops added. -/
def IsTriangleFree {V : Type*} (G : Graph V) : Prop :=
  ∀ ⦃a b c⦄, a ≠ b → a ≠ c → b ≠ c →
    G.Adj a b → G.Adj a c → G.Adj b c → False

/-- Every clique in a triangle-free graph has at most two vertices. -/
theorem IsTriangleFree.card_clique_le_two {V : Type*} {G : Graph V}
    (hG : G.IsTriangleFree) (S : Finset V)
    (hS : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → G.Adj a b) : S.card ≤ 2 := by
  by_contra h
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
  exact hG hab hac hbc (hS a ha b hb hab) (hS a ha c hc hac) (hS b hb c hc hbc)

end Hedetniemi.Graph
