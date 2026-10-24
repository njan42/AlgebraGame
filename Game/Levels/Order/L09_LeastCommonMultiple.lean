import Game.Levels.Order.L08_CoprimeProduct

World "Order"
Level 9

Title "Building the Least Common Multiple"

namespace MyAlgebra
open ElementOrder

Introduction "
When two finite orders have common factors, `g * h` may not necessarily have their
least common multiple as its order. We can choose powers of `g` and `h` instead.

The arithmetic rule `coprime_lcm_parts` splits `Nat.lcm m n` into coprime factors
`a` and `b`, with `a ∣ m` and `b ∣ n`. For example, orders 12 and 18 allow factors 4 and 9.
The rule assigns each prime power in the least common multiple to one side.

Construct powers with orders `a` and `b`, then multiply them.
The requested order is `m * n / Nat.gcd m n`, the usual formula for the least common multiple.
"

/-- Suitable powers of two elements have a product whose order is their least common multiple. -/
TheoremDoc MyAlgebra.exists_product_power_order as "exists_product_power_order" in "Order"
Statement exists_product_power_order {G : Type} [CommGroup G] (g h : G)
    (hg : order g ≠ 0) (hh : order h ≠ 0) :
    ∃ a b : ℕ, order (g ^ a * h ^ b) =
      order g * order h / Nat.gcd (order g) (order h) := by
  Branch
    obtain ⟨a, b, parts⟩ := coprime_lcm_parts (order g) (order h) hg hh
    Hint "The facts in `{parts}` describe the two divisors, their coprimality, and their product.
    Unpack the facts needed to construct the powers."
    obtain ⟨ha, hb, hc, hab⟩ := parts
    use order g / a
    Hint "One exponent is chosen. Which power of the second element has the other chosen order?"
    use order h / b
    have hga := order_power_divisor g a hg ha
    have hhb := order_power_divisor h b hh hb
    have hcop : Nat.Coprime (order (g ^ (order g / a))) (order (h ^ (order h / b))) := by
      rw [hga, hhb]
      exact hc
    rw [order_coprime_product _ _ hcop, hga, hhb, hab]
    exact Nat.lcm_eq_mul_div _ _
  Branch
    rw [← Nat.lcm_eq_mul_div]
    Hint "The target order is now written as an LCM. Which arithmetic rule splits
    that LCM into two coprime divisors?"
    obtain ⟨a, b, ha, hb, hc, hab⟩ := coprime_lcm_parts (order g) (order h) hg hh
    use order g / a, order h / b
    Hint "Check the orders of the proposed powers before using the coprime product formula."
    have hga := order_power_divisor g a hg ha
    have hhb := order_power_divisor h b hh hb
    have hcop : Nat.Coprime (order (g ^ (order g / a))) (order (h ^ (order h / b))) := by
      rw [hga, hhb]
      exact hc
    rw [order_coprime_product _ _ hcop, hga, hhb, hab]
  Hint (strict := true) "`coprime_lcm_parts` supplies two divisors, their coprimality,
  and their product equation."
  obtain ⟨a, b, ha, hb, hc, hab⟩ := coprime_lcm_parts (order g) (order h) hg hh
  Hint "Which powers of `{g}` and `{h}` have orders `{a}` and `{b}`?"
  use order g / a, order h / b
  have hga := order_power_divisor g a hg ha
  have hhb := order_power_divisor h b hh hb
  have hcop : Nat.Coprime (order (g ^ (order g / a))) (order (h ^ (order h / b))) := by
    rw [hga, hhb]
    exact hc
  rw [order_coprime_product _ _ hcop, hga, hhb, hab]
  Hint "`Nat.lcm_eq_mul_div` expresses the least common multiple as the product divided by the GCD."
  exact Nat.lcm_eq_mul_div _ _

/-- For nonzero `m` and `n`, `coprime_lcm_parts` gives divisors `a ∣ m` and `b ∣ n`
with `Nat.Coprime a b` and `a * b = Nat.lcm m n`. -/
TheoremDoc MyAlgebra.ElementOrder.coprime_lcm_parts as "coprime_lcm_parts" in "Nat"
/-- `Nat.lcm_eq_mul_div m n` states `Nat.lcm m n = m * n / Nat.gcd m n`. -/
TheoremDoc Nat.lcm_eq_mul_div as "Nat.lcm_eq_mul_div" in "Nat"
/-- `Nat.lcm m n` is the least common multiple of the two natural numbers. -/
DefinitionDoc Nat.lcm as "Nat.lcm" in "Nat"
NewDefinition Nat.lcm
NewTheorem MyAlgebra.ElementOrder.coprime_lcm_parts Nat.lcm_eq_mul_div

Conclusion "Congrats! Suitable powers let you build an element of order equal to the LCM."

end MyAlgebra
