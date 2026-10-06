import Game.Levels.KernelImage.L06_TrivialKernelInjective

World "KernelImage"
Level 7

Title "Surjectivity Means Reaching the Whole Target"

namespace MyAlgebra

Introduction "
Surjectivity means that every target element has an input mapping to it.
Image membership also asks for such an input.

Prove that `f` is surjective exactly when its image is `Set.univ`.
"

/-- A homomorphism is surjective exactly when its image is the whole target. -/
TheoremDoc MyAlgebra.surjective_iff_image_univ as "surjective_iff_image_univ"
  in "Kernels and Images"
Statement surjective_iff_image_univ {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    :
    Function.Surjective f ↔ f.imageSet = Set.univ := by
  constructor
  · intro hf
    Hint "`Set.ext` reduces set equality to membership equivalence.
    Compare image membership with membership in the whole target."
    apply Set.ext
    intro y
    constructor
    · intro hy
      exact True.intro
    · intro hy
      Hint "What does surjectivity tell you about preimages of `{y}`?"
      exact hf y
  · intro himage
    intro y
    Hint "Every target element belongs to `Set.univ`. Use `{himage}` to put `{y}` in the image."
    have hy : y ∈ f.imageSet := by
      rw [himage]
      exact True.intro
    exact hy

Conclusion "The kernel detects injectivity, and the image detects surjectivity.
A bijective homomorphism is called an isomorphism. A homomorphism from a group
to itself is an endomorphism; it may not necessarily be bijective."

end MyAlgebra
