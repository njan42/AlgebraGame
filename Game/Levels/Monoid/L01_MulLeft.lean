import Game.Metadata
import Game.MyAlgebra.AddMul_Group_Def

World "Monoid"
Level 1

Title "Left Multiplication"

namespace MyAlgebra

Introduction "
Let's start with rewriting. If `m1 = m2`, multiplying both by the same element
on the left should give the same result. Prove this using `rw`.
"

/--
`mul_left` is a proof that if `m1 = m2`, then `m * m1 = m * m2` - basically `m * _` is a function.
-/
TheoremDoc MyAlgebra.mul_left as "mul_left" in "Monoid"
@[to_additive]
Statement mul_left {M} (m : M) {m1 m2 : M} [Monoid M] : m1 = m2 → m * m1 = m * m2 := by
  Hint "Start by introducing the hypothesis with `intro`."
  intro h
  Hint "Now, use `rw` to rewrite the goal using the hypothesis `{h}`."
  rw [h]

Conclusion "Congrats!"

section Basic_Tactics
/--
`rfl` proves goals of the form `X = X`.
-/
TacticDoc rfl

/--
If `h` is a proof of an equality `X = Y`, then `rw [h]` will change
all `X`s in the goal to `Y`s. It's the way to \"substitute in\".
-/
TacticDoc rw

/--
`intro h` will move a hypothesis from the goal to a new hypothesis called `h`.
-/
TacticDoc intro

/--
`apply h` will try to match the current goal against the conclusion of `h`,
-/
TacticDoc apply

/--
`have q : r := p` will add a new hypothesis called `q` with type `r` to the local context. It will need a proof `p`. Where you can use `by` to start a proof.
-/
TacticDoc «have»

/--
`obtain ⟨x, y, z⟩ := h` will destructure `h` into the variables `x`, `y`, and `z`. This is useful for when you have a hypothesis that is a tuple or a structure. You can type `⟨` using `\langle` and `⟩` using `\rangle`.
-/
TacticDoc obtain

/--
`calc` is a way to chain equalities together. It's a bit like `rw`, but you can see the whole chain of reasoning.
-/
TacticDoc «calc»

/--
`exact h` will close the goal if `h` is a proof of the goal.
-/
TacticDoc exact

/--
`simp` rewrites using known simplification rules. Use `simp only [h₁, h₂]` to choose the rules explicitly.
-/
TacticDoc simp

/--
`repeat t` repeatedly applies the tactic `t` to the goal. You don't need to use this tactic, it just speeds things up sometimes.
-/
TacticDoc «repeat»

/--
If `h : X = Y` and there are several `X`s in the goal, then `nth_rewrite 3 [h]` will just change the third `X` to a `Y`.
-/
TacticDoc nth_rewrite

/--
The theorem `Iff.intro` is used to prove a goal of the form `P ↔ Q`. It splits the goal into two subgoals: `P → Q` and `Q → P`.
-/
TheoremDoc Iff.intro as "Iff.intro" in "Basic"

/--
The `constructor` tactic can be used to prove goals that are inductive types with a single constructor. For example, it can be used to prove `P ↔ Q` by proving both `P → Q` and `Q → P`, or to prove `P ∧ Q` by splitting the goal into proving `P` and `Q`.
-/
TacticDoc «constructor»

/--
If `h : X = Y` and there are several `X`s in the goal, then `nth_rw 3 [h]` will just change the third `X` to a `Y`.
-/
TacticDoc nth_rw

/--
`cases' h with h1 h2 ... hn` is a tactic that splits `h` into cases and adds them as hypotheses `h1 h2 ... hn`
-/
TacticDoc cases'

/--
`use x` supplies a witness for an existential goal, such as `∃ x, P x`, and leaves `P x` to prove.
-/
TacticDoc use

NewTactic rfl rw intro apply «have» obtain «calc» exact simp «repeat» nth_rewrite «constructor» nth_rw cases' use
end Basic_Tactics

section Monoid_Axioms
/--
`mul_one` states `m * 1 = m` (right identity).
-/
TheoremDoc mul_one as "mul_one" in "Monoid"
/--
`one_mul` states `1 * m = m` (left identity).
-/
TheoremDoc one_mul as "one_mul" in "Monoid"

/--
`mul_assoc` is a proof that for all `m1 m2 m3 : M`, `(m1 * m2) * m3 = m1 * (m2 * m3)` (Associative Law).
-/
TheoremDoc MyAlgebra.Semigroup.mul_assoc as "mul_assoc" in "Monoid"
end Monoid_Axioms

/--
`And.left` and `And.right` are theorems that split an `And` into its left and right components
-/
TheoremDoc And.left as "And.left" in "Basic"
/--
`And.left` and `And.right` are theorems that split an `And` into its left and right components
-/
TheoremDoc And.right as "And.right" in "Basic"

/--
`And.intro` is a theorem that takes two proofs `h1 : P` and `h2 : Q` and returns a proof `h : P ∧ Q`
-/
TheoremDoc And.intro as "And.intro" in "Basic"


/-- `add_zero a` is the additive identity law `a + 0 = a`. -/
TheoremDoc add_zero as "add_zero" in "Monoid"
/-- `zero_add a` is the additive identity law `0 + a = a`. -/
TheoremDoc zero_add as "zero_add" in "Monoid"
/-- `Nat.mul_comm a b` states `a * b = b * a` for natural numbers. -/
TheoremDoc Nat.mul_comm as "Nat.mul_comm" in "Nat"
NewTheorem mul_one one_mul MyAlgebra.Semigroup.mul_assoc And.left And.right And.intro Iff.intro
  add_zero zero_add Nat.mul_comm

end MyAlgebra
