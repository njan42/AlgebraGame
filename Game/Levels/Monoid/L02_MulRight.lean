import Game.Levels.Monoid.L01_MulLeft

World "Monoid"
Level 2

Title "Right Multiplication"

namespace MyAlgebra

Introduction "
Now multiply on the right instead. The same rewriting argument should work.
"

/--
`mul_right m` preserves equality when both elements are multiplied on the right by `m`.
-/
TheoremDoc MyAlgebra.mul_right as "mul_right" in "Monoid"
@[to_additive]
Statement mul_right {M} (m : M) {m1 m2 : M} [Monoid M] : m1 = m2 → m1 * m = m2 * m := by
  intro h
  rw [h]

Conclusion "Congrats!"

end MyAlgebra
