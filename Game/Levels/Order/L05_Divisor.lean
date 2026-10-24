import Game.Levels.Order.L04_PowerFormula

World "Order"
Level 5

Title "Building an Element of a Given Order"

namespace MyAlgebra
open ElementOrder

Introduction "
If `g` has finite order `n` and `d ∣ n`, which power of `g` has order `d`?
Show that taking `n / d` steps at a time gives such an element.
For a cycle of length 12, taking 3 steps at a time gives order 4.
"

/-- Taking the power `order g / d` produces an element of order `d`. -/
TheoremDoc MyAlgebra.order_power_divisor as "order_power_divisor" in "Order"
Statement order_power_divisor {G : Type} [Group G] (g : G) (d : ℕ)
    (h : order g ≠ 0) (hd : d ∣ order g) : order (g ^ (order g / d)) = d := by
  Branch
    have hquotient := Nat.div_dvd_of_dvd hd
    calc
      order (g ^ (order g / d)) = order g / Nat.gcd (order g) (order g / d) :=
        order_power _ _ h
      _ = order g / (order g / d) := by
        Hint "The quotient divides the original order by `{hquotient}`.
        What does this imply about their greatest common divisor?"
        rw [Nat.gcd_eq_right hquotient]
      _ = d := Nat.div_div_self hd h
  rw [order_power g _ h]
  Hint "`Nat.div_dvd_of_dvd` says this quotient divides the original order.
  Then `Nat.gcd_eq_right` simplifies the greatest common divisor."
  rw [Nat.gcd_eq_right (Nat.div_dvd_of_dvd hd)]
  Hint "`Nat.div_div_self hd h` simplifies `n / (n / d)` to `d` when `d ∣ n` and `n ≠ 0`."
  exact Nat.div_div_self hd h

/-- If `d ∣ n`, then `Nat.div_dvd_of_dvd` proves `n / d ∣ n`. -/
TheoremDoc Nat.div_dvd_of_dvd as "Nat.div_dvd_of_dvd" in "Nat"
/-- If `d ∣ n`, then `Nat.gcd_eq_right` proves `Nat.gcd n d = d`. -/
TheoremDoc Nat.gcd_eq_right as "Nat.gcd_eq_right" in "Nat"
/-- If `d ∣ n` and `n ≠ 0`, `Nat.div_div_self` proves `n / (n / d) = d`. -/
TheoremDoc Nat.div_div_self as "Nat.div_div_self" in "Nat"
NewTheorem Nat.div_dvd_of_dvd Nat.gcd_eq_right Nat.div_div_self

Conclusion "Congrats! The powers of an element realize every divisor of its finite order."

end MyAlgebra
