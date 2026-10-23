import Game.Levels.GroupHom.L04_OneHom

World "GroupHom"
Level 5

Title "Composing Homomorphisms"

namespace MyAlgebra

Introduction "
We have two homomorphisms, `f1 : GroupHom G H` and `f2 : GroupHom H J`.
Their composite sends `x` to `f2 (f1 x)`.
Does it preserve multiplication? Build a `GroupHom G J` for this composite.
"

/--
`hom_comp_hom` is a proof that composition of homomorphisms is also a homomorphism.
-/
TheoremDoc MyAlgebra.hom_comp_hom as "hom_comp_hom" in "Group"
/-- `hom_comp_hom f g` constructs the homomorphism sending `x` to `g (f x)`. -/
DefinitionDoc MyAlgebra.hom_comp_hom as "hom_comp_hom" in "GroupHom"
Statement hom_comp_hom {G H J : Type} [Group G] [Group H] [Group J]
    (f1 : GroupHom G H) (f2 : GroupHom H J) : GroupHom G J := by
  Hint "A `GroupHom` needs a function and a proof that it preserves multiplication.
  Which function applies `{f1}` first and `{f2}` second?"
  use f2 ∘ f1
  intro a b
  Hint "The fields `{f1}.hom` and `{f2}.hom` describe how each map treats a product.
  How do their equations fit together?"
  have h1 := f1.hom a b
  have h2 := f2.hom (f1 a) (f1 b)
  rw [← h1] at h2
  exact h2
Conclusion "Congrats!"

end MyAlgebra
