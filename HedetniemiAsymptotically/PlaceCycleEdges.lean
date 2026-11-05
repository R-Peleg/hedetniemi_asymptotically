import HedetniemiAsymptotically.CycleTemplates
import Mathlib.Data.Finset.Sort

namespace Hedetniemi

/-- Place a cycle pattern on an ordered vertex set using its canonical
increasing enumeration. -/
def placeCycleEdges {V : Type*} [LinearOrder V] {m : ℕ} (S : Finset V)
    (hS : S.card = m + 3) (E : Finset (Sym2 (Fin (m + 3)))) : Finset (Sym2 V) :=
  E.image (Sym2.map (S.orderEmbOfFin hS))

/-- Placing a pattern preserves the number of edges because the vertex
enumeration, and therefore its action on unordered pairs, is injective. -/
theorem card_placeCycleEdges {V : Type*} [LinearOrder V] {m : ℕ} (S : Finset V)
    (hS : S.card = m + 3) (E : Finset (Sym2 (Fin (m + 3)))) :
    (placeCycleEdges S hS E).card = E.card := by
  unfold placeCycleEdges
  apply Finset.card_image_of_injOn
  intro a _ b _ hab
  exact Sym2.map.injective (S.orderEmbOfFin hS).injective hab

end Hedetniemi
