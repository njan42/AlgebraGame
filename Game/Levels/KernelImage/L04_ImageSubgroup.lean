import Game.Levels.KernelImage.L03_ImageIdentity

World "KernelImage"
Level 4

Title "The Image Is a Subgroup"

namespace MyAlgebra

Introduction "
Check that the image is a subgroup of the target group.
Each membership hypothesis says that some source element reaches the given output.

If inputs reach `a` and `b`, which input reaches `a * b`?
If an input reaches `a`, which input could reach `a⁻¹`?
"

/-- The image set satisfies identity, multiplication, and inverse closure. -/
TheoremDoc MyAlgebra.image_isSubgroupSet as "image_isSubgroupSet" in "Kernels and Images"
Statement image_isSubgroupSet {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    : IsSubgroupSet f.imageSet := by
  constructor
  · exact image_one_mem f
  constructor
  · intro a b ha hb
    Hint "Unpack both membership hypotheses to name inputs and their output equations."
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    Hint "Which input could map to the product of these outputs?
    The field `{f}.hom` describes the image of a product."
    use x * y
    rw [f.hom, hx, hy]
  · intro a ha
    obtain ⟨x, hx⟩ := ha
    Hint "Which input could map to the inverse of this output?
    Which homomorphism law could verify your choice?"
    use x⁻¹
    rw [← hom_preserves_inv f, hx]

Conclusion "Outputs reached by a homomorphism form a subgroup of its target."

end MyAlgebra
