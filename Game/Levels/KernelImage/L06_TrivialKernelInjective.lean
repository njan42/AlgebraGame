import Game.Levels.KernelImage.L05_InjectiveKernel

World "KernelImage"
Level 6

Title "A Trivial Kernel Forces Injectivity"

namespace MyAlgebra

Introduction "
Suppose the only element sent to `1` is `1` itself.
To prove injectivity, consider two inputs `a` and `b` with the same output.

What does `f` do to `a * b⁻¹`? What would membership of this element in the
kernel tell you about the relationship between `a` and `b`?
"

/-- A homomorphism whose kernel contains only the identity is injective. -/
TheoremDoc MyAlgebra.trivial_kernel_injective as "trivial_kernel_injective" in "Kernels and Images"
Statement trivial_kernel_injective {G H : Type} [Group G] [Group H] (f : GroupHom G H)
    (hker : ∀ x, x ∈ f.kernelSet → x = 1) :
    Function.Injective f := by
  intro a b hab
  Hint "First show that `{a} * {b}⁻¹` belongs to the kernel."
  have hk : a * b⁻¹ ∈ f.kernelSet := by
    change f (a * b⁻¹) = 1
    rw [f.hom, ← hom_preserves_inv f, hab, mul_inv]
  have hprod := hker (a * b⁻¹) hk
  Hint "Which common right factor could help you compare the inputs?
  The kernel condition gives a product equal to `1`."
  apply mul_right_cancel b⁻¹
  rw [hprod, mul_inv]

Conclusion "A group homomorphism is injective exactly when its kernel contains only the identity."

end MyAlgebra
