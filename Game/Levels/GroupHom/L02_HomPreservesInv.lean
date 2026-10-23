import Game.Levels.GroupHom.L01_HomPreservesOne

World "GroupHom"
Level 2

Title "Homomorphisms preserve inverses"

namespace MyAlgebra

Introduction "
Does a multiplication-preserving map also preserve inverses?
Consider the image of `a * a⁻¹`, and use the identity result from the last level.
"

/--
`hom_preserves_inv` is a proof that a homomorphism preserves inverses.
-/
TheoremDoc MyAlgebra.hom_preserves_inv as "hom_preserves_inv" in "Group"
Statement hom_preserves_inv {G H : Type} [Group G] [Group H]
    (f : GroupHom G H) {a : G} : (f a)⁻¹ = f a⁻¹ := by
  Hint "`f.hom a a⁻¹` relates the product of the two images to the image of their product."
  have q := f.hom a (a⁻¹)
  rw [mul_inv] at q
  rw [hom_preserves_one f] at q
  apply mul_left_cancel (f a)
  rw [mul_inv]
  exact q

Conclusion "Congrats!"

end MyAlgebra
