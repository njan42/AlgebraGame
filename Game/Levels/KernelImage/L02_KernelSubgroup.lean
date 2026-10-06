import Game.Levels.KernelImage.L01_KernelIdentity

World "KernelImage"
Level 2

Title "The Kernel Is a Subgroup"

namespace MyAlgebra

Introduction "
To show that the kernel is a subgroup of `G`, check its three closure conditions.

If two elements map to `1`, where does their product map?
Where does the inverse of either element map?
"

/-- The kernel set satisfies identity, multiplication, and inverse closure. -/
TheoremDoc MyAlgebra.kernel_isSubgroupSet as "kernel_isSubgroupSet" in "Kernels and Images"
Statement kernel_isSubgroupSet {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    : IsSubgroupSet f.kernelSet := by
  constructor
  · exact kernel_one_mem f
  constructor
  · intro a b ha hb
    Hint "Write the kernel memberships as equations, then use `{f}.hom` on the product."
    change f a = 1 at ha
    change f b = 1 at hb
    change f (a * b) = 1
    rw [f.hom, ha, hb, one_mul]
  · intro a ha
    change f a = 1 at ha
    change f a⁻¹ = 1
    Hint "How does `hom_preserves_inv` relate the output of an inverse to the original output?
    What is the inverse of the identity?"
    rw [← hom_preserves_inv f, ha, ← inv_id]

Conclusion "The kernel is always a subgroup,
even when the homomorphism is neither injective nor surjective."

end MyAlgebra
