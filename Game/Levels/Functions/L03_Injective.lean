import Game.Levels.Functions.L02_Composition

World "Functions"
Level 3

Title "Injectivity Is Cancellation"

namespace MyAlgebra

Introduction "
A function is **injective** if equal outputs imply equal inputs:
`Function.Injective f` means `∀ a b, f a = f b → a = b`.

We've already seen this idea. In a group, left multiplication by a fixed element `g`
is injective because we can cancel `g`.

The expression `fun x : G => g * x` describes the function sending `x` to `g * x`.
"

/-- Left multiplication by a fixed group element is injective. -/
TheoremDoc MyAlgebra.left_mul_injective as "left_mul_injective" in "Functions"
Statement left_mul_injective {G : Type} [Group G] (g : G) :
    Function.Injective (fun x : G => g * x) := by
  Hint "What must you show about two inputs with equal outputs?"
  intro a b h
  Hint "Which group cancellation law applies to `{h}`?"
  exact mul_left_cancel g h

/-- `Function.Injective f` means `∀ a b, f a = f b → a = b`.
If `hf : Function.Injective f` and `h : f a = f b`, then `hf h` proves `a = b`. -/
DefinitionDoc Function.Injective as "Function.Injective" in "Functions"

NewDefinition Function.Injective

Conclusion "Cancellation says that multiplying on the left loses no information.
Injectivity names the same property for a general function."

end MyAlgebra
