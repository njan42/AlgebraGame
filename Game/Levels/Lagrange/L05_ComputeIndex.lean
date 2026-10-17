import Game.Levels.Lagrange.L04_Divisibility

World "Lagrange"
Level 5

Title "How Many Cosets?"

namespace MyAlgebra

Introduction "
Suppose a group has twelve elements and a subgroup has three elements.
How many distinct left cosets does that subgroup have?

The tactic `linarith` proves consequences of linear equations and inequalities,
including multiplication by a known constant. Use it once you have established
the relevant counting equation.
"

/-- A subgroup of size three in a group of size twelve has index four. -/
TheoremDoc MyAlgebra.index_of_twelve_and_three as "index_of_twelve_and_three" in "Lagrange"
Statement index_of_twelve_and_three {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hG : Nat.card G = 12)
    (hH : Nat.card H = 3) : H.index = 4 := by
  have h := lagrange_card_formula H
  rw [hG, hH] at h
  Hint "The counting equation now involves only natural numbers. Use `linarith`."
  linarith

/-- `linarith` proves consequences of linear equations and inequalities.
Use it after establishing the algebraic facts. -/
TacticDoc linarith
NewTactic linarith

Conclusion "There are four distinct cosets, each containing three elements."

end MyAlgebra
