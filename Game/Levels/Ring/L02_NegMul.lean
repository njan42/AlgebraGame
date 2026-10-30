import Game.Levels.Ring.L01_MulZero

World "Ring"
Level 2

Title "Multiplication of Negatives"

namespace MyAlgebra

Introduction "
What happens when we multiply two negatives in a ring?
Use distributivity and additive cancellation to prove that `(-a) * (-b) = a * b`.
"

/--
`neg_mul_neg` is a proof that `(-a) * (-b) = a * b`.
-/
TheoremDoc MyAlgebra.neg_mul_neg as "neg_mul_neg" in "Ring"
Statement neg_mul_neg {R} [Ring R] (a b : R) : (-a) * (-b) = a * b := by
  Hint "Add `(-a) * b` to both sides and see how to simplify the expression."
  apply add_left_cancel ((-a) * b)
  rw [← distrib_left, add_neg, mul_zero, ← distrib_right, neg_add, zero_mul]

Conclusion "Congrats!"

end MyAlgebra
