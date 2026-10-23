import Game.Levels.Functions
import Game.MyAlgebra.Group_Hom_Def

World "GroupHom"
Level 1

Title "Homomorphisms preserve the identity"

namespace MyAlgebra

Introduction "
A group homomorphism is a function that preserves multiplication:
`f (a * b) = f a * f b`. It may not necessarily be injective or surjective.

A `GroupHom G H` stores the function and this law. Write `f a` to apply it,
and use `f.hom a b` for its multiplication law.
Does preserving multiplication force it to preserve the identity too?
"

/--
`hom_preserves_one` is a proof that a homomorphism preserves the identity element.
-/
TheoremDoc MyAlgebra.hom_preserves_one as "hom_preserves_one" in "Group"
Statement hom_preserves_one {G H} [Group G] [Group H] (f : GroupHom G H) : f 1 = 1 := by
  Hint "`f.hom 1 1` describes the image of the product of two identity elements."
  have q := f.hom 1 1
  rw [one_mul] at q
  Hint "Compare `{f} 1 * {f} 1` with `1 * {f} 1`.
  What remains after cancelling their common right factor?"
  apply mul_right_cancel (f 1)
  Hint "Use the identity law and `{q}` to show that these products are equal."
  rw [one_mul]
  rw [←q]
Conclusion "Congrats!"

end MyAlgebra
