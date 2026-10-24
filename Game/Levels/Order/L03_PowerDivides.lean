import Game.Levels.Order.L02_Inverse

World "Order"
Level 3

Title "The Order of a Power Divides"

namespace MyAlgebra
open ElementOrder

Introduction "
Taking several steps at a time may return to the identity sooner.
Show that the order of `g ^ k` divides the order of `g`.
"

/-- The order of a natural power divides the order of its base. -/
TheoremDoc MyAlgebra.order_power_dvd as "order_power_dvd" in "Order"
Statement order_power_dvd {G : Type} [Group G] (g : G) (k : ℕ) :
    order (g ^ k) ∣ order g := by
  Branch
    rw [order_dvd_iff]
    calc
      (g ^ k) ^ order g = g ^ (k * order g) := by rw [mpow_mul]
      _ = g ^ (order g * k) := by
        Hint "These exponents differ only in the order of two natural-number factors.
        `Nat.mul_comm` lets you exchange them."
        rw [Nat.mul_comm]
      _ = (g ^ order g) ^ k := mpow_mul _ _ _
      _ = 1 := by rw [pow_order, mpow_id]
  apply (order_dvd_iff (g ^ k) (order g)).mpr
  Hint "The power of a power is the same as multiplying the powers. `Nat.mul_comm` exchanges the
  natural-number exponents."
  rw [← mpow_mul, Nat.mul_comm, mpow_mul, pow_order, mpow_id]

Conclusion "Congrats! Powers of an element have orders dividing the original order."

end MyAlgebra
