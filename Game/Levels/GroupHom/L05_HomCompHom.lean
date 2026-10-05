import Game.Levels.GroupHom.L04_OneHom

World "GroupHom"
Level 5

Title "Composing Homomorphisms"

namespace MyAlgebra

Introduction "
  We have seen that the identity function is a homomorphism. Now we will see that the composition of two homomorphisms is also a homomorphism.

  `GroupHom` is defined as a structure with a proof that the function is a homomorphism, and the function itself. To create a new `GroupHom` instance, we need to provide the function and the proof.

  A `GroupHom G J` contains a function `G → J` and a proof that it preserves multiplication. Here `use f2 ∘ f1` supplies that function; the remaining goal asks you to prove its multiplication law.

  Furthermore, you can construct functions using `λ` notation and ∘ (written \"\\circ\"). For example, `fun x y => x + y` is the function that takes `x, y` to `x + y`. And `f ∘ g` is the function that takes `x` to `f (g x)`.
"

/--
`hom_comp_hom` is a proof that composition of homomorphisms is also a homomorphism.
-/
TheoremDoc MyAlgebra.hom_comp_hom as "hom_comp_hom" in "Group"
/-- `hom_comp_hom f g` constructs the homomorphism sending `x` to `g (f x)`. -/
DefinitionDoc MyAlgebra.hom_comp_hom as "hom_comp_hom" in "GroupHom"
Statement hom_comp_hom {G H J} [Group G] [Group H] [Group J] (f1 : GroupHom G H) (f2 : GroupHom H J) : GroupHom G J := by
  Hint "Use the `use` tactic with the form `use f` where `f` is the function you want to use."
  Hint "Use `λ` notation and/or `∘` (written \"\\circ\") to construct functions"
  use f2 ∘ f1
  intro a b
  have h1 := f1.hom a b
  have h2 := f2.hom (f1 a) (f1 b)
  rw [← h1] at h2
  exact h2
Conclusion "Congrats!"
