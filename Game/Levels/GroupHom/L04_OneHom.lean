import Game.Levels.GroupHom.L03_IdHom

World "GroupHom"
Level 4

Title "The Trivial Homomorphism"

namespace MyAlgebra

Introduction "
  Let's check out another example of a homomorphism. Send every element of `G` to the identity of `H`. The target `H` can be any group; the image has only one element. This is called the trivial homomorphism.

  We will denote the trivial homomorphism by oneFunction. It is defined by `oneFunction G H g = 1` for all `g ∈ G`, where the function maps the group `G` to the group `H`.
"

def oneFunction (G H : Type) [Group G] [Group H] : G → H := λ _ => 1

/--
`hom_trivial` is a proof that the 𝟭 function is a homomorphism.
-/
TheoremDoc MyAlgebra.hom_trivial as "hom_trivial" in "Group"
Statement hom_trivial {G H : Type} [Group G] [Group H] : ∀ a b : G, oneFunction G H (a * b) = oneFunction G H (a) * oneFunction G H (b)  := by
  intro a b
  rw [oneFunction]
  rw [oneFunction]
  rw [oneFunction]
  rw [mul_one]

Conclusion "Congrats!"

/--
`MyAlgebra.oneFunction G H` is the trivial group homomorphism from group `G` to group `H`,
mapping every element `g : G` to the identity element `1 : H`.
-/
DefinitionDoc MyAlgebra.oneFunction as "oneFunction" in "GroupHom"

NewDefinition MyAlgebra.oneFunction
