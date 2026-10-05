import Game.Levels.Functions.L06_SurjectiveComposition

World "Functions"
Level 7

Title "A Perfect Pairing"

namespace MyAlgebra

Introduction "
A **bijection** is both injective and surjective. Every target has exactly one preimage.
In Lean, `Function.Bijective f` is the conjunction
`Function.Injective f ∧ Function.Surjective f`.

Finite sets related by a bijection have the same number of elements.
"

/-- Left multiplication is a bijection on a group. -/
TheoremDoc MyAlgebra.left_mul_bijective as "left_mul_bijective" in "Functions"
Statement left_mul_bijective {G : Type} [Group G] (g : G) :
    Function.Bijective (fun x : G => g * x) := by
  Hint "Use `constructor` to separate injectivity and surjectivity."
  constructor
  · exact left_mul_injective g
  · exact left_mul_surjective g

/-- `Function.Bijective f` means `Function.Injective f ∧ Function.Surjective f`.
Use `constructor` to prove both parts. -/
DefinitionDoc Function.Bijective as "Function.Bijective" in "Functions"

NewDefinition Function.Bijective

Conclusion "A bijective group homomorphism is called a group isomorphism."

end MyAlgebra
