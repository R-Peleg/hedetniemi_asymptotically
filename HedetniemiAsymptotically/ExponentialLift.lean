import HedetniemiAsymptotically.ExponentialGraph
import HedetniemiAsymptotically.StrongProduct

namespace Hedetniemi

/-- The map `φ*` in Section 4 ignores the second coordinate. -/
def exponentialLift {V W C : Type*} (f : V → C) : V × W → C := fun x ↦ f x.1

/-- Co-proper maps on `G°` lift to co-proper maps on the strong product. -/
theorem CoProper.exponentialLift {V W C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {f g : V → C} (hfg : CoProper (loopedGraph G) f g) :
    CoProper (Graph.ofSimpleGraph (strongProduct G H))
      (exponentialLift (W := W) f) (exponentialLift g) := by
  intro x y hxy
  exact hfg hxy.1

end Hedetniemi
