import Game.Levels.PowGroup.L04_PowPred

World "Group Power"
Level 5

Title "Adding Integer Exponents"

namespace MyAlgebra

Introduction "
Prove the addition law for all integer exponents.
Integer induction has three cases: zero, one step up, and one step down.
Use `induction y using integer_induction with` and the cases `zero`,
`succ y ih`, and `pred y ih`. The step variable is an integer in both directions.
"

/-- `gpow_add g x y` states `g ^ x * g ^ y = g ^ (x + y)`. -/
TheoremDoc MyAlgebra.gpow_add as "gpow_add" in "Group Power"
Statement gpow_add {G : Type} [Group G] (g : G) (x y : ℤ) :
    g ^ x * g ^ y = g ^ (x + y) := by
  induction y using integer_induction with
  | zero =>
    Hint "`Int.add_zero x` simplifies `x + 0`."
    rw [gpow_zero, mul_one, Int.add_zero]
  | succ y ih =>
    Hint "Use the successor rule and `{ih}`.
    `Int.add_assoc` then matches the two expressions for the exponent."
    rw [gpow_succ, ← mul_assoc, ih, ← gpow_succ, Int.add_assoc]
  | pred y ih =>
    Hint "Use the predecessor rule and `{ih}`.
    `Int.add_sub_assoc x y 1` states `x + (y - 1) = (x + y) - 1`."
    rw [← gpow_pred, ← mul_assoc, ih, gpow_pred, Int.add_sub_assoc]

/-- Integer induction proves `P 0`, then `P n → P (n + 1)` and `P n → P (n - 1)`
for integer `n`. Use `induction n using integer_induction with`. -/
TheoremDoc MyAlgebra.integer_induction as "integer_induction" in "Int"
/-- `Int.add_assoc a b c` states `(a + b) + c = a + (b + c)`. -/
TheoremDoc Int.add_assoc as "Int.add_assoc" in "Int"
/-- `Int.add_zero n` states `n + 0 = n`. -/
TheoremDoc Int.add_zero as "Int.add_zero" in "Int"
/-- `Int.add_sub_assoc a b c` states `a + (b - c) = (a + b) - c`. -/
TheoremDoc Int.add_sub_assoc as "Int.add_sub_assoc" in "Int"
NewTheorem MyAlgebra.integer_induction Int.add_zero Int.add_assoc Int.add_sub_assoc

Conclusion "Congrats!"

end MyAlgebra
