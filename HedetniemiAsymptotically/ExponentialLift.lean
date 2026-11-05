import HedetniemiAsymptotically.ExponentialGraph
import HedetniemiAsymptotically.StrongProduct

namespace Hedetniemi

/-- The map `φ*` in Section 4 ignores the second coordinate. -/
def exponentialLift {V W C : Type*} (f : V → C) : V × W → C := fun x ↦ f x.1

/-- Co-proper maps on `G°` lift to co-proper maps on the strong product. -/
theorem CoProper.exponentialLift {V W C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    {f g : V → C} (hfg : CoProper (loopedGraph G) f g) :
    CoProper (Graph.ofSimpleGraph (strongProduct G H))
      (Hedetniemi.exponentialLift (W := W) f) (Hedetniemi.exponentialLift g) := by
  intro x y hxy
  exact hfg hxy.1

/-- When the second factor contains an edge, co-properness of lifted maps
also implies co-properness on `G°`. -/
theorem CoProper.of_exponentialLift {V W C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hH : ∃ i j, H.Adj i j) {f g : V → C}
    (hfg : CoProper (Graph.ofSimpleGraph (strongProduct G H))
      (Hedetniemi.exponentialLift (W := W) f) (Hedetniemi.exponentialLift g)) :
    CoProper (loopedGraph G) f g := by
  obtain ⟨i, j, hij⟩ := hH
  have hne : i ≠ j := by
    intro heq
    subst j
    exact H.loopless.irrefl i hij
  intro v w hvw
  exact hfg (v := (v, i)) (w := (w, j))
    ⟨hvw, Or.inr hij, fun heq ↦ hne (congrArg Prod.snd heq)⟩

/-- Ignoring a nonempty coordinate is injective on maps. -/
theorem exponentialLift_injective {V W C : Type*} [Nonempty W] :
    Function.Injective (Hedetniemi.exponentialLift (V := V) (W := W) (C := C)) := by
  intro f g hfg
  obtain ⟨w⟩ := ‹Nonempty W›
  funext v
  exact congrFun hfg (v, w)

end Hedetniemi
