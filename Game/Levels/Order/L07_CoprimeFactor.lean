import Game.Levels.Order.L06_ProductPower

World "Order"
Level 7

Title "Recovering a Factor's Order"

namespace MyAlgebra
open ElementOrder

Introduction "
Two natural numbers are **coprime** if their greatest common divisor is `1`.
Lean writes this as `Nat.Coprime m n`.

Suppose `g` and `h` belong to an abelian group and have coprime orders.
We will show that the order of `g` divides the order of `g * h`.

If repeating `g * h` returns to the identity, repeat that whole cycle `order h` times.
What happens to the contribution from `h`?
"

/-- With coprime factor orders, the first factor's order divides the product's order. -/
TheoremDoc MyAlgebra.coprime_factor_order_dvd as "coprime_factor_order_dvd" in "Order"
Statement coprime_factor_order_dvd {G : Type} [CommGroup G] (g h : G)
    (hc : Nat.Coprime (order g) (order h)) : order g ∣ order (g * h) := by
  Branch
    have hproduct : (g * h) ^ (order h * order (g * h)) = 1 := by
      rw [Nat.mul_comm, mpow_mul, pow_order, mpow_id]
    rw [commuting_product_power] at hproduct
    have hh : h ^ (order h * order (g * h)) = 1 := by
      rw [mpow_mul, pow_order, mpow_id]
    rw [hh, mul_one] at hproduct
    have hdiv := (order_dvd_iff g _).mpr hproduct
    Hint "The extra order factor in `{hdiv}` is on the left.
    `Nat.mul_comm` puts it on the side expected by coprime cancellation."
    rw [Nat.mul_comm] at hdiv
    exact hc.dvd_of_dvd_mul_right hdiv
  apply hc.dvd_of_dvd_mul_right
  rw [order_dvd_iff]
  Hint "This power can be compared with a repeated cycle of the product.
  What happens to the contribution from the second factor?"
  have hproduct : (g * h) ^ (order (g * h) * order h) = 1 := by
    rw [mpow_mul, pow_order, mpow_id]
  rw [commuting_product_power] at hproduct
  have hh : h ^ (order (g * h) * order h) = 1 := by
    rw [Nat.mul_comm, mpow_mul, pow_order, mpow_id]
  rw [hh, mul_one] at hproduct
  exact hproduct

/-- `Nat.Coprime m n` means `Nat.gcd m n = 1`. -/
DefinitionDoc Nat.Coprime as "Nat.Coprime" in "Nat"
/-- If `k` and `n` are coprime and `k ∣ m * n`,
`Nat.Coprime.dvd_of_dvd_mul_right` proves `k ∣ m`. -/
TheoremDoc Nat.Coprime.dvd_of_dvd_mul_right as "Nat.Coprime.dvd_of_dvd_mul_right" in "Nat"
NewDefinition Nat.Coprime
NewTheorem Nat.Coprime.dvd_of_dvd_mul_right

Conclusion "Congrats! Each factor order divides the product order when the orders are coprime."

end MyAlgebra
