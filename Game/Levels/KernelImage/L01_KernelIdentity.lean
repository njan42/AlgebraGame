import Game.Levels.Subgroups
import Game.MyAlgebra.GroupHom_Sets

World "KernelImage"
Level 1

Title "What Gets Sent to the Identity?"

namespace MyAlgebra

Introduction "
The kernel of a homomorphism `f : GroupHom G H` is the set of inputs sent to
the identity of `H`. We write its carrier as `f.kernelSet`:
`x ∈ f.kernelSet` means `f x = 1`.

The kernel is a set in the source group `G`. It is the preimage of the set
containing only the identity of the target group.
For example, the trivial homomorphism sends every input to `1`, so its kernel
is the whole source group.

You might have heard of kernel used in the context of a linear map, the set
of vectors sent to the zero vector (aka null space).

Does the identity of `G` belong to the kernel?
"

/-- The source identity belongs to the kernel of a homomorphism. -/
TheoremDoc MyAlgebra.kernel_one_mem as "kernel_one_mem" in "Kernels and Images"
Statement kernel_one_mem {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    : (1 : G) ∈ f.kernelSet := by
  Hint "Express kernel membership as an equation using `change`."
  change f 1 = 1
  exact hom_preserves_one f

/-- `x ∈ f.kernelSet` means `f x = 1`; the kernel set lives in the source group. -/
DefinitionDoc MyAlgebra.GroupHom.kernelSet as "GroupHom.kernelSet" in "Kernels and Images"
NewDefinition MyAlgebra.GroupHom.kernelSet

Conclusion "The source identity lies in the kernel.
Could other elements also be sent to the target identity?"

end MyAlgebra
