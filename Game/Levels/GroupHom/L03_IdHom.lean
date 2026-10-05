import Game.Levels.GroupHom.L02_HomPreservesInv

World "GroupHom"
Level 3

Title "The Identity Function is a Homomorphism"

namespace MyAlgebra

Introduction "
  Let's check out an example of a homomorphism. Here's a simple one: the identity function.
"


Statement {G : Type} [Group G] : ∀ a b : G, id (a * b) = id (a) * id (b)  := by
  intro a b
  Hint "`rfl` automatically solves this case, but you can also use `rw [id]`"
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
