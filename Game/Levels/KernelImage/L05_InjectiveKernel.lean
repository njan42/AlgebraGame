import Game.Levels.KernelImage.L04_ImageSubgroup

World "KernelImage"
Level 5

Title "An Injective Map Has a Trivial Kernel"

namespace MyAlgebra

Introduction "
An injective function cannot send two different inputs to the same output.
For a group homomorphism, the identity already maps to the identity.

If `f` is injective, can any other element belong to its kernel?
Show that every kernel element equals `1`.
"

/-- Every kernel element of an injective homomorphism equals the identity. -/
TheoremDoc MyAlgebra.injective_kernel_trivial as "injective_kernel_trivial" in "Kernels and Images"
Statement injective_kernel_trivial {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    (hf : Function.Injective f)
    (a : G) (ha : a ∈ f.kernelSet) : a = 1 := by
  Hint "By injectivity, it is enough to compare the outputs of `{a}` and `1`."
  apply hf
  change f a = 1 at ha
  rw [hom_preserves_one f]
  exact ha

/-- Package the image closure proofs as a subgroup of the target. -/
def GroupHom.image {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    : Subgroup H :=
  Subgroup.ofSet f.imageSet (image_isSubgroupSet f)

/-- `f.image` is the subgroup with carrier `f.imageSet`. -/
DefinitionDoc MyAlgebra.GroupHom.image as "GroupHom.image" in "Kernels and Images"
NewDefinition MyAlgebra.GroupHom.image

Conclusion "An injective homomorphism has kernel consisting only of the identity.
Is that condition also sufficient?"

end MyAlgebra
