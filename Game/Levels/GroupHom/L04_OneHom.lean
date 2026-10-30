import Game.Levels.GroupHom.L03_IdHom

World "GroupHom"
Level 4

Title "The Trivial Homomorphism"

namespace MyAlgebra

Introduction "
Send every element of `G` to the identity of `H`. This is the trivial homomorphism.
We write the function as `oneFunction G H`; it sends every input to `1`.
Show that it preserves multiplication.
"

def oneFunction (G H : Type) [Group G] [Group H] : G → H := λ _ => 1

/--
`hom_trivial` proves that the function sending every element to `1` preserves multiplication.
-/
TheoremDoc MyAlgebra.hom_trivial as "hom_trivial" in "GroupHom"
Statement hom_trivial {G H : Type} [Group G] [Group H] :
    ∀ a b : G, oneFunction G H (a * b) = oneFunction G H a * oneFunction G H b := by
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

end MyAlgebra
