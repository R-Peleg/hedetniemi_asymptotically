import HedetniemiAsymptotically.CycleTemplates
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod

namespace Hedetniemi

/-- A candidate short cycle chooses its vertex set and an undirected
Hamiltonian pattern on that set. -/
abbrev CyclePlacement (V : Type*) (m : ℕ) :=
  {S : Finset V // S.card = m + 3} ×
    {E : Finset (Sym2 (Fin (m + 3))) // E ∈ cycleTemplates m}

/-- The number of candidate cycles is the number of vertex sets times
the number of cycle patterns. -/
theorem card_cyclePlacement (V : Type*) [Fintype V] [DecidableEq V] (m : ℕ) :
    Fintype.card (CyclePlacement V m) =
      (Fintype.card V).choose (m + 3) * (cycleTemplates m).card := by
  simp [CyclePlacement]

end Hedetniemi
