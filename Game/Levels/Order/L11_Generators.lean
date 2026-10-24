import Game.Levels.Order.L10_Cyclic
import Game.Levels.Functions

World "Order"
Level 11

Title "Which Powers Are Generators?"

namespace MyAlgebra
open ElementOrder

Introduction "
Let `g` generate a finite cyclic group of order `n`. Its order is also `n`,
because its powers visit every element before repeating.
An element generates this group exactly when it has that full order.
The counting rule `generates_iff_same_order` expresses this criterion.

Which powers of `g` still have the full order? Prove that `g ^ k` generates
exactly when `k` and `order g` are coprime.
For a group of order 12, the exponents 1, 5, 7, and 11 give generators.
"

/-- A power of a generator generates a finite cyclic group exactly for coprime exponents. -/
TheoremDoc MyAlgebra.generator_power_iff_coprime as "generator_power_iff_coprime" in "Order"
Statement generator_power_iff_coprime {G : Type} [Group G] [Finite G] (g : G)
    (hg : Generates g) (k : ℕ) : Generates (g ^ k) ↔ Nat.Coprime k (order g) := by
  Branch
    rw [generates_iff_same_order g (g ^ k) hg]
    Hint (strict := true) "The generator condition is now a full-order equality.
    The power-order formula requires the original order to be nonzero."
    have h0 : order g ≠ 0 := Nat.ne_of_gt (order_pos g)
    rw [order_power g k h0, Nat.div_eq_self, or_iff_right h0]
    constructor
    · intro hc
      exact Nat.Coprime.symm hc
    · intro hc
      exact hc.symm
  Hint (strict := true) "`order_pos` says an element of a finite group has positive order.
  `Nat.ne_of_gt` turns positivity into being nonzero."
  have h0 : order g ≠ 0 := Nat.ne_of_gt (order_pos g)
  rw [generates_iff_same_order g (g ^ k) hg, order_power g k h0]
  Hint "`Nat.div_eq_self` says `n / d = n ↔ n = 0 ∨ d = 1`.
  The original order is nonzero, so which possibility remains?
  `or_iff_right` removes an impossible left alternative from a disjunction."
  rw [Nat.div_eq_self, or_iff_right h0]
  constructor
  · intro hc
    Hint "Coprimality says that the GCD is `1`. How does symmetry exchange its two inputs?"
    exact Nat.Coprime.symm hc
  · intro hc
    exact hc.symm

/-- In a finite group, `order_pos g` proves `0 < order g`. -/
TheoremDoc MyAlgebra.ElementOrder.order_pos as "order_pos" in "Order"
/-- If `g` generates a finite group, `generates_iff_same_order g a hg` states
`Generates a ↔ order a = order g`: a generator must visit the whole cycle. -/
TheoremDoc MyAlgebra.ElementOrder.generates_iff_same_order as "generates_iff_same_order" in "Order"
/-- `Nat.ne_of_gt` turns `0 < n` into `n ≠ 0`. -/
TheoremDoc Nat.ne_of_gt as "Nat.ne_of_gt" in "Nat"
/-- `Nat.div_eq_self` states `n / d = n ↔ n = 0 ∨ d = 1`. -/
TheoremDoc Nat.div_eq_self as "Nat.div_eq_self" in "Nat"
/-- `Nat.div_one n` states `n / 1 = n`. -/
TheoremDoc Nat.div_one as "Nat.div_one" in "Nat"
/-- Given `h : ¬P`, `or_iff_right h` rewrites `P ∨ Q` as `Q`. -/
TheoremDoc or_iff_right as "or_iff_right" in "Logic"
NewTheorem MyAlgebra.ElementOrder.order_pos MyAlgebra.ElementOrder.generates_iff_same_order
  Nat.ne_of_gt Nat.div_eq_self Nat.div_one or_iff_right

Conclusion "Congrats! A power generates the whole finite cycle exactly when its exponent
shares no common factor greater than 1 with the cycle length."

end MyAlgebra
