import Game.Levels.Functions.L04_InjectiveComposition

World "Functions"
Level 5

Title "Every Target Has a Preimage"

namespace MyAlgebra

Introduction "
A function is **surjective** if it reaches every element of its target:
`Function.Surjective f` means `∀ y, ∃ x, f x = y`.
The input `x` is called a preimage of `y`.

Consider the map `x ↦ g * x`. Where does it send the identity `1`?
Where does it send `g⁻¹`? What do these examples suggest about reaching other targets?
"

/-- Left multiplication by a fixed group element reaches every target. -/
TheoremDoc MyAlgebra.left_mul_surjective as "left_mul_surjective" in "Functions"
Statement left_mul_surjective {G : Type} [Group G] (g : G) :
    Function.Surjective (fun x : G => g * x) := by
  Hint "Start with an arbitrary target element. What does surjectivity ask you to find?"
  intro y
  Hint "Which input is sent to `{y}`? How can you undo left multiplication by `{g}`?"
  use g⁻¹ * y
  Hint "Use `change` to express the function's value as a product."
  change g * (g⁻¹ * y) = y
  Hint "Regroup the product so `{g}` and its inverse are adjacent."
  rw [← mul_assoc, mul_inv, one_mul]

/-- `Function.Surjective f` means `∀ y, ∃ x, f x = y`.
Introduce a target with `intro y`, then supply a preimage with `use x`. -/
DefinitionDoc Function.Surjective as "Function.Surjective" in "Functions"

NewDefinition Function.Surjective

Conclusion "Surjectivity is an existence statement: every target has at least one preimage.
Injectivity tells us that there is at most one."

end MyAlgebra
