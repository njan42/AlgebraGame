import Game.Levels.GroupExamples.L01_Z_mod_mZ_Id

World "Group Examples"
Level 2

Title "Inverses for Modular Addition"

namespace MyAlgebra

Introduction "
Which element undoes adding `a` modulo `m`?
Find an inverse and check addition in both orders.
Mathlib calls the additive inverse laws `add_neg_cancel` and `neg_add_cancel`.
"

/-- Inverses for Modular Addition. -/
TheoremDoc MyAlgebra.Z_mod_mZ_inv as "Z_mod_mZ_inv" in "Group Examples"
Statement Z_mod_mZ_inv (m : ℕ) (a : ZMod m) :
    ∃ b : ZMod m, a + b = 0 ∧ b + a = 0 := by
  use -a
  constructor
  · Hint "`add_neg_cancel a` states `a + (-a) = 0`."
    rw [add_neg_cancel]
  · Hint "`neg_add_cancel a` states `(-a) + a = 0`."
    rw [neg_add_cancel]

/-- `add_neg_cancel a` states `a + (-a) = 0` in an additive group. -/
TheoremDoc add_neg_cancel as "add_neg_cancel" in "Group Examples"
/-- `neg_add_cancel a` states `(-a) + a = 0` in an additive group. -/
TheoremDoc neg_add_cancel as "neg_add_cancel" in "Group Examples"
NewTheorem add_neg_cancel neg_add_cancel

Conclusion "Congrats!"

end MyAlgebra
