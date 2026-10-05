import Game.MyAlgebra.Z_mod_mZ
import Game.Levels.Group

World "Group Examples"
Level 1

Title "Z mod mZ Identity"

namespace MyAlgebra

Introduction "
  The set of integers Z = {... , −2, −1, 0, 1, 2, . . .} is a group if we use addition as the group law. It is an example of group with infinitely many elements.

  What goes wrong if we try to use multiplication as the group law?

  The set of integers modulo m (denoted Z/mZ) forms a group with addition as the group law.

  Ex. Z/12Z = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} is the group of integers modulo 12, which we use on clocks. If it's 11am and you add 1 hour, the clock wraps back to the start and it becomes 0pm (or 12pm).

  In this level, we will prove that the identity element of the group Z_mod_mZ is 0.
"

/--
`Z_mod_mZ_id` is a proof that the identity element of the group `Z_mod_mZ` is `0`.
-/
TheoremDoc MyAlgebra.Z_mod_mZ_id as "Z_mod_mZ_id" in "Group Examples"
Statement Z_mod_mZ_id (m : ℕ) (a : ZMod m) : 0 + a = a ∧ a + 0 = a := by
  -- TODO: Change the def of ZMod to make this proof more straightforward
  cases m with
  | zero =>
    exact ⟨Int.zero_add a, Int.add_zero a⟩
  | succ n =>
    exact ⟨Fin.zero_add a, Fin.add_zero a⟩

Conclusion "Congrats!"

/--
`ZMod n` is the type of integers modulo `n`.
-/
DefinitionDoc ZMod as "ZMod" in "Group Examples"

/--
`Int.zero_add` is a proof that for any integer `a`, `0 + a = a`.
-/
TheoremDoc Int.zero_add as "Int.zero_add" in "Int"

/--
`Fin.zero_add` is a proof that for any element `a` of `Fin n`, `0 + a = a`.
-/
TheoremDoc Fin.zero_add as "Fin.zero_add" in "Fin"

/--
`sub_self` is a proof that for any element `a`, `a - a = 0`.
-/
TheoremDoc sub_self as "sub_self" in "Group Examples"

/--
`sub_eq_neg_add` is a proof that `a - b = -b + a`.
-/
TheoremDoc sub_eq_neg_add as "sub_eq_neg_add" in "Group Examples"

/--
`sub_eq_add_neg` is a proof that `a - b = a + (-b)`.
-/
TheoremDoc sub_eq_add_neg as "sub_eq_add_neg" in "Group Examples"

/-- `Int.add_zero a` states `a + 0 = a` for integers. -/
TheoremDoc Int.add_zero as "Int.add_zero" in "Int"

/-- `Fin.add_zero a` states `a + 0 = a` for modular representatives. -/
TheoremDoc Fin.add_zero as "Fin.add_zero" in "Fin"

/-- `cases x with ...` splits a proof into the constructors of `x`.
Here `cases m` separates modulus zero from positive moduli. -/
TacticDoc «cases»

NewTactic «cases»
NewDefinition ZMod

NewTheorem Int.zero_add Int.add_zero Fin.zero_add Fin.add_zero sub_self sub_eq_neg_add sub_eq_add_neg
