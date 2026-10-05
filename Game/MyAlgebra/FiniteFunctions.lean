import Mathlib

namespace MyAlgebra

/-- Choose one preimage for every target of a surjective function. -/
theorem choose_preimages {A B : Type} (f : A → B) (hf : Function.Surjective f) :
    ∃ s : B → A, ∀ y, f (s y) = y :=
  hf.hasRightInverse

end MyAlgebra
