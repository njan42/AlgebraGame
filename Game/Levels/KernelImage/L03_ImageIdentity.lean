import Game.Levels.KernelImage.L02_KernelSubgroup

World "KernelImage"
Level 3

Title "Which Outputs Are Reached?"

namespace MyAlgebra

Introduction "
The image of `f : GroupHom G H` is the set of values `f x`.
We write `f.imageSet` for this set in the target group `H`.
Membership `y ∈ f.imageSet` means `∃ x : G, f x = y`.
This is the image of the whole source group, so every input is allowed.

The image may not necessarily be the whole target. For example, the trivial homomorphism
reaches only `1`, although its target may contain other elements.

Is the target identity reached?
"

/-- The target identity belongs to the image of a homomorphism. -/
TheoremDoc MyAlgebra.image_one_mem as "image_one_mem" in "Kernels and Images"
Statement image_one_mem {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    : (1 : H) ∈ f.imageSet := by
  Hint "Find an input whose output is the target identity."
  use 1
  exact hom_preserves_one f

/-- Package the kernel closure proofs as a subgroup of the source. -/
def GroupHom.kernel {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    : Subgroup G :=
  Subgroup.ofSet f.kernelSet (kernel_isSubgroupSet f)

/-- `f.kernel` is the subgroup with carrier `f.kernelSet`. -/
DefinitionDoc MyAlgebra.GroupHom.kernel as "GroupHom.kernel" in "Kernels and Images"
/-- `y ∈ f.imageSet` means `∃ x, f x = y`; the image set lives in the target group. -/
DefinitionDoc MyAlgebra.GroupHom.imageSet as "GroupHom.imageSet" in "Kernels and Images"
NewDefinition MyAlgebra.GroupHom.kernel MyAlgebra.GroupHom.imageSet

Conclusion "The image contains the target identity.
The kernel is a subset of the source; the image is a subset of the target."

end MyAlgebra
