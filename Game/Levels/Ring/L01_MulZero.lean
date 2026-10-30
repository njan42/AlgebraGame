import Game.Levels.Group
import Game.MyAlgebra.Ring_Def

World "Ring"
Level 1

Title "Multiplication by Zero"

namespace MyAlgebra

Introduction "
A ring has an additive abelian group and a multiplicative monoid.
Distributivity connects the two operations. Use it with additive cancellation
to prove `a * 0 = 0`.

The additive laws switch out `*`, `1`, and inverses by `+`, `0`, and negatives.
For example, `add_left_cancel x` cancels a common summand on the left.
"

/--
`mul_zero` is a proof that `a * 0 = 0` for all `a : R` in a ring `R`. This describes
multiplication by the additive identity.
-/
TheoremDoc MyAlgebra.mul_zero as "mul_zero" in "Ring"
Statement mul_zero {R} [Ring R] (a : R) : a * 0 = 0 := by
  Hint "What happens when you expand `a * (0 + 0)` using distributivity?"
  have h : a * 0 = a * 0 + a * 0 :=
    calc a * 0 = a * (0 + 0) := by rw [add_zero]
      _ = a * 0 + a * 0 := by rw [distrib_left]
  Hint "Compare `{a} * 0 + {a} * 0` with `{a} * 0 + 0`.
  What remains after cancelling their common summand?"
  apply add_left_cancel (a * 0)
  Hint "Use `{h}` to combine the repeated sum, then simplify the additive identity."
  rw [← h]
  rw [add_zero]

/--
`zero_mul` is a proof that `0 * a = 0` for all `a : R` in a ring `R`. This describes multiplication by the additive identity.
-/
TheoremDoc MyAlgebra.zero_mul as "zero_mul" in "Ring"
theorem zero_mul {R} [Ring R] (a : R) : 0 * a = 0 := by
  have h : 0 * a = 0 * a + 0 * a :=
    calc 0 * a = (0 + 0) * a := by rw [zero_add]
      _ = 0 * a + 0 * a := by rw [distrib_right]
  apply add_left_cancel (0 * a)
  rw [← h]
  rw [add_zero]

/-- `add_zero a` is the additive identity law `a + 0 = a`. -/
TheoremDoc add_zero as "add_zero" in "Ring"
/-- `zero_add a` is the additive identity law `0 + a = a`. -/
TheoremDoc zero_add as "zero_add" in "Ring"

Conclusion "Congrats! The same argument proves `0 * a = 0`; that result is also in the inventory."

section Ring_Axioms
/-- `add_neg a` states `a + (-a) = 0`. -/
TheoremDoc MyAlgebra.AddGroup.add_neg as "add_neg" in "Ring"
/-- `neg_add a` states `(-a) + a = 0`. -/
TheoremDoc MyAlgebra.AddGroup.neg_add as "neg_add" in "Ring"
/-- `add_assoc a b c` states `(a + b) + c = a + (b + c)`. -/
TheoremDoc MyAlgebra.AddSemigroup.add_assoc as "add_assoc" in "Ring"
/-- `add_comm a b` states `a + b = b + a`. -/
TheoremDoc MyAlgebra.AddCommGroup.add_comm as "add_comm" in "Ring"
/-- `distrib_left a b c` states `a * (b + c) = a * b + a * c`. -/
TheoremDoc MyAlgebra.Ring.distrib_left as "distrib_left" in "Ring"
/-- `distrib_right a b c` states `(a + b) * c = a * c + b * c`. -/
TheoremDoc MyAlgebra.Ring.distrib_right as "distrib_right" in "Ring"
/-- `add_left_cancel a` reduces `b = c` to `a + b = a + c`.
This is the additive version of left cancellation in a group. -/
TheoremDoc MyAlgebra.add_left_cancel as "add_left_cancel" in "Ring"
/-- `add_right_cancel a` reduces `b = c` to `b + a = c + a`.
This is the additive version of right cancellation in a group. -/
TheoremDoc MyAlgebra.add_right_cancel as "add_right_cancel" in "Ring"
end Ring_Axioms

NewTheorem add_zero zero_add MyAlgebra.AddGroup.neg_add MyAlgebra.AddGroup.add_neg MyAlgebra.AddSemigroup.add_assoc
  MyAlgebra.AddCommGroup.add_comm MyAlgebra.Ring.distrib_right MyAlgebra.Ring.distrib_left
  MyAlgebra.zero_mul MyAlgebra.add_left_cancel MyAlgebra.add_right_cancel

end MyAlgebra
