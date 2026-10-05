import Game.Levels.Functions
import Game.MyAlgebra.Group_Hom_Def

World "GroupHom"
Level 1

Title "Homomorphisms preserve the identity"

namespace MyAlgebra

Introduction "
  In Functions, you studied injectivity, surjectivity, and composition. We now ask
  for a different property: preserving the group operation. A homomorphism need
  not be injective or surjective. Here we'll prove that it preserves the identity element.

  We define a homomorphism as a function `f` that satisfies the following property:
  `∀ a b : G, f (a * b) = f a * f b`

  And we can access this property by using `f.hom` where `f.hom a b : f (a * b) = f a * f b`.

  We can also use the homomorphism as a function by using `f` directly. Example: `f a`.
"

/--
`hom_preserves_one` is a proof that a homomorphism preserves the identity element.
-/
TheoremDoc MyAlgebra.hom_preserves_one as "hom_preserves_one" in "Group"
-- @[to_additive]
Statement hom_preserves_one {G H} [Group G] [Group H] (f : GroupHom G H) : f 1 = 1 := by
  Hint "We probably want to use f.hom with terms that have f 1 to match with the goal"
  Hint "Remember that f.hom is a function that takes two arguments"
  have q := f.hom 1 1
  rw [one_mul] at q
  apply mul_right_cancel (f 1)
  rw [one_mul]
  rw [←q]
Conclusion "Congrats!"
