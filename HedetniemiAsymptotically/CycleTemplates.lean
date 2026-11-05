import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Sym.Card
import Mathlib.Data.Finset.Image

namespace Hedetniemi

/-- The edges of a cycle whose cyclic vertex order is a permutation.
The parameter `m` represents cycles of length `m+3`. -/
def cycleEdges {m : ℕ} (σ : Equiv.Perm (Fin (m + 3))) : Finset (Sym2 (Fin (m + 3))) :=
  Finset.univ.image (fun i ↦ s(σ i, σ (i + 1)))

/-- All undirected Hamiltonian cycle patterns on a fixed set of `m+3` vertices.
Taking an image automatically identifies rotations and reversals. -/
def cycleTemplates (m : ℕ) : Finset (Finset (Sym2 (Fin (m + 3)))) :=
  Finset.univ.image (cycleEdges (m := m))

set_option maxRecDepth 20000 in
theorem card_cycleTemplates_three : (cycleTemplates 0).card = 1 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem card_cycleTemplates_four : (cycleTemplates 1).card = 3 := by decide

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
theorem card_cycleTemplates_five : (cycleTemplates 2).card = 12 := by decide

end Hedetniemi
