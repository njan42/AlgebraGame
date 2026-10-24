import Game.Levels.Order.L07_CoprimeFactor

World "Order"
Level 8

Title "Coprime Orders Multiply"

namespace MyAlgebra
open ElementOrder

Introduction "
In an abelian group, prove that the order of `g * h` is `order g * order h`
when the two factor orders are coprime.

Show divisibility in both directions. One direction follows by repeating both
cycles; the other uses the separate factor orders and their coprimality.
"

/-- In an abelian group, a product of elements of coprime orders has the product order. -/
TheoremDoc MyAlgebra.order_coprime_product as "order_coprime_product" in "Order"
Statement order_coprime_product {G : Type} [CommGroup G] (g h : G)
    (hc : Nat.Coprime (order g) (order h)) :
    order (g * h) = order g * order h := by
  Branch
    have hfirst := coprime_factor_order_dvd g h hc
    have hsecond := coprime_factor_order_dvd h g hc.symm
    rw [mul_comm h g] at hsecond
    Hint "Both factor orders divide the product's order.
    Coprimality lets you combine `{hfirst}` and `{hsecond}` into one divisibility."
    have hcombined := hc.mul_dvd_of_dvd_of_dvd hfirst hsecond
    apply Nat.dvd_antisymm
    · rw [order_dvd_iff]
      rw [commuting_product_power, mpow_mul, pow_order, mpow_id, one_mul,
        Nat.mul_comm, mpow_mul, pow_order, mpow_id]
    · exact hcombined
  apply Nat.dvd_antisymm
  · apply (order_dvd_iff (g * h) _).mpr
    Hint "After expanding the power of the product, make each exponent a multiple
    of its base's order."
    rw [commuting_product_power, mpow_mul, pow_order, mpow_id, one_mul,
      Nat.mul_comm, mpow_mul, pow_order, mpow_id]
  · Hint "`Nat.Coprime.mul_dvd_of_dvd_of_dvd` combines two divisibilities when
    the divisors are coprime."
    apply hc.mul_dvd_of_dvd_of_dvd
    · exact coprime_factor_order_dvd g h hc
    · Hint "`Nat.Coprime.symm` reverses coprimality. Exchange the group factors too."
      have hh := coprime_factor_order_dvd h g hc.symm
      rw [mul_comm h g] at hh
      exact hh

/-- Coprimality is symmetric: `Nat.Coprime.symm` turns `Nat.Coprime m n`
into `Nat.Coprime n m`. -/
TheoremDoc Nat.Coprime.symm as "Nat.Coprime.symm" in "Nat"
/-- If `m` and `n` are coprime and both divide `a`,
`Nat.Coprime.mul_dvd_of_dvd_of_dvd` proves `m * n ∣ a`. -/
TheoremDoc Nat.Coprime.mul_dvd_of_dvd_of_dvd as "Nat.Coprime.mul_dvd_of_dvd_of_dvd" in "Nat"
NewTheorem Nat.Coprime.symm Nat.Coprime.mul_dvd_of_dvd_of_dvd

Conclusion "Congrats! In an abelian group, coprime factor orders multiply."

end MyAlgebra
