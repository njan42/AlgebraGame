import Game.Levels.Order.L05_Divisor

World "Order"
Level 6

Title "Powers of Commuting Products"

namespace MyAlgebra
open ElementOrder

Introduction "
An **abelian group** is a group in which every pair of elements commutes.
In Lean, `[CommGroup G]` adds the law `mul_comm` to the group laws.

Commutativity lets us rearrange repeated products.
Prove `(g * h) ^ n = g ^ n * h ^ n` by induction on `n`.
This formula may not necessarily hold in a noncommutative group.
"

/-- In an abelian group, powers distribute over products. -/
TheoremDoc MyAlgebra.commuting_product_power as "commuting_product_power" in "Order"
Statement commuting_product_power {G : Type} [CommGroup G] (g h : G) (n : ℕ) :
    (g * h) ^ n = g ^ n * h ^ n := by
  Branch
    induction n with
    | zero => rw [mpow_zero, mpow_zero, mpow_zero, one_mul]
    | succ n ih =>
      rw [mpow_succ_left, ih, mpow_succ_left, mpow_succ_left]
      Hint "The left-successor rule puts the new factors first.
      Regroup the product so that each new factor meets its own power."
      calc
        (g * h) * (g ^ n * h ^ n) = g * (h * (g ^ n * h ^ n)) := mul_assoc _ _ _
        _ = g * ((h * g ^ n) * h ^ n) := by rw [← mul_assoc h]
        _ = g * ((g ^ n * h) * h ^ n) := by rw [mul_comm h (g ^ n)]
        _ = (g * g ^ n) * (h * h ^ n) := by rw [mul_assoc (g ^ n), ← mul_assoc]
  Branch
    induction n with
    | zero => rw [mpow_zero, mpow_zero, mpow_zero, one_mul]
    | succ n ih =>
      rw [mpow_succ_right, ih]
      Hint "The product's power is expanded. Which rule also expands the two
      successor powers on the right?"
      rw [mpow_succ_right, mpow_succ_right]
      rw [mul_assoc, ← mul_assoc (h ^ n), mul_comm (h ^ n) g]
      Hint "The factors are now in the right order. Only their grouping differs."
      rw [mul_assoc g, ← mul_assoc]
  induction n with
  | zero => rw [mpow_zero, mpow_zero, mpow_zero, one_mul]
  | succ n ih =>
    rw [mpow_succ_right, ih, mpow_succ_right, mpow_succ_right]
    Hint "Use associativity to expose the middle factors.
    `mul_comm a b` exchanges a chosen pair of group elements."
    calc
      (g ^ n * h ^ n) * (g * h) = g ^ n * (h ^ n * (g * h)) :=
        mul_assoc _ _ _
      _ = g ^ n * ((h ^ n * g) * h) := by rw [← mul_assoc (h ^ n)]
      _ = g ^ n * ((g * h ^ n) * h) := by rw [mul_comm (h ^ n) g]
      _ = (g ^ n * g) * (h ^ n * h) := by rw [mul_assoc g, ← mul_assoc]

/-- An abelian group is a group whose multiplication commutes. -/
DefinitionDoc MyAlgebra.CommGroup as "CommGroup" in "Group"
/-- `mul_comm a b` states `a * b = b * a` in an abelian group. -/
TheoremDoc MyAlgebra.CommGroup.mul_comm as "mul_comm" in "Group"
NewDefinition MyAlgebra.CommGroup
NewTheorem MyAlgebra.CommGroup.mul_comm

Conclusion "Congrats! Commutativity lets you collect the powers of the two factors separately."

end MyAlgebra
