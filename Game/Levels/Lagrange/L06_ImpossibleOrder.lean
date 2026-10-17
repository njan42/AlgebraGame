import Game.Levels.Lagrange.L05_ComputeIndex

World "Lagrange"
Level 6

Title "Ruling Out a Subgroup Size"

namespace MyAlgebra

Introduction "
Could a group with twelve elements contain a subgroup with five elements?
Use Lagrange's theorem to rule out that possibility.

The goal `Nat.card H ≠ 5` asks you to show that assuming this subgroup size
leads to a contradiction.

The tactic `omega` reasons about natural numbers and integers, including the
restriction to whole-number solutions. Use it after establishing the algebraic facts.
"

/-- A group of size twelve has no subgroup of size five. -/
TheoremDoc MyAlgebra.subgroup_card_ne_five_of_twelve as "subgroup_card_ne_five_of_twelve"
  in "Lagrange"
Statement subgroup_card_ne_five_of_twelve {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (hG : Nat.card G = 12) :
    Nat.card H ≠ 5 := by
  intro hH
  Hint "`subgroup_card_dvd H` supplies a multiplier. Unpack it to obtain the equation."
  obtain ⟨k, hk⟩ := subgroup_card_dvd H
  rw [hG, hH] at hk
  Hint "Can the equation `{hk}` hold for a natural-number multiplier? Use `omega`."
  omega

/-- `omega` proves natural-number and integer arithmetic, including linear equations,
inequalities, and restrictions to whole-number solutions. -/
TacticDoc omega
NewTactic omega

Conclusion "Lagrange's theorem rules out subgroup sizes that do not divide the group order.
It does not guarantee a subgroup for every divisor. Later, cyclic groups will
supply examples where every divisor does occur."

end MyAlgebra
