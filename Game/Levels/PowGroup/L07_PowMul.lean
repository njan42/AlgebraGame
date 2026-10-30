import Game.Levels.PowGroup.L06_PowSub

World "Group Power"
Level 7

Title "Multiplying Integer Exponents"

namespace MyAlgebra

Introduction "
Prove the power-of-a-power law for integer exponents.
Use integer induction on the outer exponent, with the addition and subtraction laws.
"

/-- `gpow_mul g x y` states `g ^ (x * y) = (g ^ x) ^ y`. -/
TheoremDoc MyAlgebra.gpow_mul as "gpow_mul" in "Group Power"
Statement gpow_mul {G : Type} [Group G] (g : G) (x y : ℤ) :
    g ^ (x * y) = (g ^ x) ^ y := by
  induction y using integer_induction with
  | zero =>
    Hint "`Int.mul_zero x` simplifies `x * 0`."
    rw [Int.mul_zero, gpow_zero, gpow_zero]
  | succ y ih =>
    Hint "`Int.mul_add x y 1` expands `x * (y + 1)`; `Int.mul_one x` simplifies `x * 1`."
    rw [Int.mul_add, Int.mul_one, ← gpow_add, gpow_succ, ih]
  | pred y ih =>
    Hint "`Int.mul_sub x y 1` expands `x * (y - 1)`; then use the power subtraction law."
    rw [Int.mul_sub, Int.mul_one, ← gpow_sub, ← gpow_pred, ih]

/-- `Int.mul_zero n` states `n * 0 = 0`. -/
TheoremDoc Int.mul_zero as "Int.mul_zero" in "Int"
/-- `Int.mul_one n` states `n * 1 = n`. -/
TheoremDoc Int.mul_one as "Int.mul_one" in "Int"
/-- `Int.mul_add a b c` states `a * (b + c) = a * b + a * c`. -/
TheoremDoc Int.mul_add as "Int.mul_add" in "Int"
/-- `Int.mul_sub a b c` states `a * (b - c) = a * b - a * c`. -/
TheoremDoc Int.mul_sub as "Int.mul_sub" in "Int"
NewTheorem Int.mul_zero Int.mul_one Int.mul_add Int.mul_sub

Conclusion "Congrats!"

end MyAlgebra
