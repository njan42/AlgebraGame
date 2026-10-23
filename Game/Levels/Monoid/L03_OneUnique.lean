import Game.Levels.Monoid.L02_MulRight

World "Monoid"
Level 3

Title "Only One One"

namespace MyAlgebra

Introduction "
A monoid has an identity element `1`. Could there be another identity?
Suppose `w` acts as an identity on both sides. Show that `w = 1`.

The hypothesis gives two facts for each element. For a proof `hpq : P ∧ Q`,
`obtain ⟨hp, hq⟩ := hpq` names its two parts.
"

/--
`id_unique` is a proof that there is only one identity element in a monoid
-/
TheoremDoc MyAlgebra.id_unique as "id_unique" in "Monoid"
Statement id_unique {M} (w : M) [Monoid M] (h : ∀ (m : M), (m * w = m ∧ w * m = m)) : w = 1 := by
  Hint "Apply the identity property to `1`, then unpack the two facts with `obtain`."
  obtain ⟨h1, h2⟩ := h 1
  rw [mul_one] at h2
  rw [one_mul] at h1
  exact h1

Conclusion "Congrats!"

end MyAlgebra
