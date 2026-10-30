import Game.Levels.GroupHom.L02_HomPreservesInv

World "GroupHom"
Level 3

Title "The Identity Function Is a Homomorphism"

namespace MyAlgebra

Introduction "
The identity function sends each element to itself.
Check that it preserves multiplication.
"

Statement {G : Type} [Group G] : ∀ a b : G, id (a * b) = id (a) * id (b)  := by
  intro a b
  Hint "What does the identity function return? Compare the expressions on the two sides."
  Branch
    rfl
  rw [id]
  rw [id]
  rw [id]

Conclusion "Congrats!"

/--
`id x` is the identity function, which returns `x` itself.
-/
DefinitionDoc id as "id" in "GroupHom"

NewDefinition id

end MyAlgebra
