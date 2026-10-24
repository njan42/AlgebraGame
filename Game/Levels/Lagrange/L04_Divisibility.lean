import Game.Levels.Lagrange.L03_CountingFormula

World "Lagrange"
Level 4

Title "Lagrange's Theorem"

namespace MyAlgebra

Introduction "
For natural numbers, `a ∣ b` means that `b = a * k` for some natural number `k`.
The symbol `∣` can be typed with `\\mid`.

Lagrange's theorem says that the order (number of elements) of a subgroup
of a finite group divides the order of the group.
Which number in the counting formula supplies the multiplier?
"

/-- The cardinality of a subgroup divides the cardinality of a finite group. -/
TheoremDoc MyAlgebra.subgroup_card_dvd as "subgroup_card_dvd" in "Lagrange"
Statement subgroup_card_dvd {G : Type} [Group G] [Finite G] (H : Subgroup G)
    : Nat.card H ∣ Nat.card G := by
  Hint "Supply the index as the multiplier."
  use H.index
  Hint "Use `lagrange_card_formula`, then use `Nat.mul_comm` to commute the natural-number factors."
  rw [lagrange_card_formula H, Nat.mul_comm]

Conclusion "A subgroup of a group with twelve elements can only have size dividing twelve:
1, 2, 3, 4, 6, or 12."

end MyAlgebra
