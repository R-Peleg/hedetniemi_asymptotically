import HedetniemiAsymptotically.ExponentialLift
import HedetniemiAsymptotically.SuitedColoring

namespace Hedetniemi

/-- Restrict a coloring along the natural exponential lifting from `G°`
to a strong product. -/
def restrictExponentialColoring {V W C D : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (χ : (exponentialGraph (Graph.ofSimpleGraph (strongProduct G H)) C).Coloring D) :
    (exponentialGraph (loopedGraph G) C).Coloring D :=
  ⟨fun f ↦ χ.val (exponentialLift f), fun {_ _} h ↦ χ.property h.exponentialLift⟩

/-- Restriction preserves suitedness because any color occurring in a
lifted map already occurs in the original map. -/
theorem IsSuited.restrictExponentialColoring {V W C D : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    {χ : (exponentialGraph (Graph.ofSimpleGraph (strongProduct G H)) C).Coloring (C ⊕ D)}
    (hχ : IsSuited χ) : IsSuited (restrictExponentialColoring χ) := by
  intro f b hfb
  obtain ⟨x, hx⟩ := hχ (exponentialLift f) b hfb
  exact ⟨x.1, hx⟩

end Hedetniemi
