import Game.Levels.PowGroup.L02_PowNegOne

World "Group Power"
Level 3

Title "Subtracting One from an Exponent"

namespace MyAlgebra

Introduction "
Increasing an exponent by one multiplies by `g`.
What multiplication should undo that step? Prove the corresponding rule for subtracting one.
"

/-- `gpow_pred g n` states `g ^ n * g⁻¹ = g ^ (n - 1)`. -/
TheoremDoc MyAlgebra.gpow_pred as "gpow_pred" in "Group Power"
Statement gpow_pred {G : Type} [Group G] (g : G) (n : ℤ) : g ^ n * g⁻¹ = g ^ (n - 1) := by
  Hint "Apply `gpow_succ` at exponent `n - 1` to express `g ^ n`."
  have h := gpow_succ g (n - 1)
  Hint "`Int.sub_add_cancel n 1` simplifies `(n - 1) + 1` to `n`."
  rw [Int.sub_add_cancel] at h
  rw [h, mul_assoc, mul_inv, mul_one]

/-- `Int.sub_add_cancel a b` states `a - b + b = a`. -/
TheoremDoc Int.sub_add_cancel as "Int.sub_add_cancel" in "Int"
NewTheorem Int.sub_add_cancel

Conclusion "Congrats!"

end MyAlgebra
