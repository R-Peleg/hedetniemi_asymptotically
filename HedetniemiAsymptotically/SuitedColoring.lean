import HedetniemiAsymptotically.ExponentialGraph

namespace Hedetniemi

/-- Colors in the left summand are primary; colors in the right are secondary.
A suited coloring uses a primary color only on maps containing it. -/
def IsSuited {V C D : Type*} {G : Graph V}
    (χ : (exponentialGraph G C).Coloring (C ⊕ D)) : Prop :=
  ∀ f b, χ.val f = Sum.inl b → b ∈ Set.range f

end Hedetniemi
