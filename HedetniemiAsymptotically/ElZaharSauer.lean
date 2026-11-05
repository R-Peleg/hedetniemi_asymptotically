import HedetniemiAsymptotically.ExponentialGraph
import HedetniemiAsymptotically.TensorProduct

/-! The evaluation coloring of El-Zahar and Sauer [3], Lemma 2 of the paper. -/
namespace Hedetniemi

/-- Lemma 2: evaluation properly colors the tensor product with its exponential.
This statement also covers graphs with loops and arbitrary color types. -/
def evaluationColoring {V C : Type*} (G : Graph V) :
    (tensorProduct G (exponentialGraph G C)).Coloring C :=
  ⟨fun x ↦ x.2 x.1, fun {_ _} h ↦ h.2 h.1⟩

end Hedetniemi
