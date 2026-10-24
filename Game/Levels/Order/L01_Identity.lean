import Game.MyAlgebra.ElementOrder

World "Order"
Level 1

Title "The Order of the Identity"

namespace MyAlgebra
open ElementOrder

Introduction "
The **order of an element** `g` is the smallest positive natural number `n` with `g ^ n = 1`.
If no such number exists, we write `order g = 0`, indicating infinite order.
The exponent zero does not count since every element already satisfies `g ^ 0 = 1`.

The inventory contains two facts about order:
`pow_order g` gives `g ^ order g = 1`, and `order_dvd_iff g n` says
`order g ∣ n ↔ g ^ n = 1`. Type `∣` with `\\dvd`.

What is the first positive power at which the identity returns to itself?
"

/-- The identity has order one. -/
TheoremDoc MyAlgebra.order_one as "order_one" in "Order"
Statement order_one {G : Type} [Group G] : order (1 : G) = 1 := by
  Hint "`Nat.dvd_antisymm` proves two natural numbers equal by showing that each divides the other."
  apply Nat.dvd_antisymm
  Hint "Use `order_dvd_iff` to relate divisibility to a power of the identity."
  · rw [order_dvd_iff]
    Hint "Divisibility is now a power equality. Which rule simplifies a first power?"
    rw [mpow_one]
  Hint "`Nat.one_dvd` proves one divides any natural number."
  · exact Nat.one_dvd _

/-- `order g` is the least positive exponent with `g ^ n = 1`, or `0` for infinite order. -/
DefinitionDoc MyAlgebra.ElementOrder.order as "order" in "Order"
/-- `pow_order g` states `g ^ order g = 1`. -/
TheoremDoc MyAlgebra.ElementOrder.pow_order as "pow_order" in "Order"
/-- `order_dvd_iff g n` states `order g ∣ n ↔ g ^ n = 1`. -/
TheoremDoc MyAlgebra.ElementOrder.order_dvd_iff as "order_dvd_iff" in "Order"
/-- Prove `a = b` for natural numbers by proving `a ∣ b` and `b ∣ a`. -/
TheoremDoc Nat.dvd_antisymm as "Nat.dvd_antisymm" in "Nat"
/-- `Nat.one_dvd n` proves `1 ∣ n`. -/
TheoremDoc Nat.one_dvd as "Nat.one_dvd" in "Nat"
NewDefinition MyAlgebra.ElementOrder.order
NewTheorem MyAlgebra.ElementOrder.pow_order MyAlgebra.ElementOrder.order_dvd_iff
  Nat.dvd_antisymm Nat.one_dvd

Conclusion "Congrats! The identity has order one."

end MyAlgebra
