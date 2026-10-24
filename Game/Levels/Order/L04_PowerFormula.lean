import Game.Levels.Order.L03_PowerDivides

World "Order"
Level 4

Title "How Many Steps Are Skipped?"

namespace MyAlgebra
open ElementOrder

Introduction "
Suppose `g` has finite order `n`. Moving `k` steps at a time returns after
`n / gcd(n, k)` moves. For example, if `n = 12` and `k = 8`, the order is `12 / 4 = 3`.

Lean writes the greatest common divisor as `Nat.gcd n k`.
The arithmetic rule `gcd_quotient_dvd_iff` says
`n / Nat.gcd n k ∣ t ↔ n ∣ k * t` when `n ≠ 0`.
Use this rule and the power laws to identify the order.
"

/-- A power of an element of finite order has order `n / gcd(n, k)`. -/
TheoremDoc MyAlgebra.order_power as "order_power" in "Order"
Statement order_power {G : Type} [Group G] (g : G) (k : ℕ) (h : order g ≠ 0) :
    order (g ^ k) = order g / Nat.gcd (order g) k := by
  Branch
    apply Nat.dvd_antisymm
    · rw [order_dvd_iff, ← mpow_mul, ← order_dvd_iff]
      Hint "This divisibility concerns an exponent product.
      `gcd_quotient_dvd_iff` can express it using the reduced quotient instead."
      rw [← gcd_quotient_dvd_iff (order g) k _ h]
    · rw [gcd_quotient_dvd_iff _ _ _ h, order_dvd_iff, mpow_mul]
      Hint "This is a whole cycle of the powered element. Which order rule describes it?"
      exact pow_order _
  apply Nat.dvd_antisymm
  · apply (order_dvd_iff (g ^ k) _).mpr
    rw [← mpow_mul]
    apply (order_dvd_iff g _).mp
    Hint "`gcd_quotient_dvd_iff` turns the product divisibility into a quotient
    dividing itself."
    apply (gcd_quotient_dvd_iff (order g) k _ h).mp
    exact dvd_refl _
  · apply (gcd_quotient_dvd_iff (order g) k _ h).mpr
    apply (order_dvd_iff g _).mpr
    Hint "What does this exponent mean as a power of `{g} ^ {k}`?"
    rw [mpow_mul]
    exact pow_order (g ^ k)

/-- For `n ≠ 0`, `gcd_quotient_dvd_iff n k t h` states
`n / Nat.gcd n k ∣ t ↔ n ∣ k * t`. -/
TheoremDoc MyAlgebra.ElementOrder.gcd_quotient_dvd_iff as "gcd_quotient_dvd_iff" in "Nat"
/-- `dvd_refl n` states `n ∣ n`. -/
TheoremDoc dvd_refl as "dvd_refl" in "Nat"
/-- `Nat.gcd m n` is the greatest common divisor of the two natural numbers. -/
DefinitionDoc Nat.gcd as "Nat.gcd" in "Nat"
NewDefinition Nat.gcd
NewTheorem MyAlgebra.ElementOrder.gcd_quotient_dvd_iff dvd_refl

Conclusion "Congrats! Common factors of the exponent and the original order shorten the cycle."

end MyAlgebra
