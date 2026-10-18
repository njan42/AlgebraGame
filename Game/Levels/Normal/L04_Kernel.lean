import Game.Levels.Normal.L03_Abelian

World "Normal"
Level 4

Title "Kernels Are Normal"

namespace MyAlgebra

Introduction "
The kernel of a homomorphism consists of inputs sent to `1`.
Its subgroup is written `f.kernel`.

If `f n = 1`, where does `f` send `g * n * g⁻¹`?
Show that the kernel is normal without assuming that either group is abelian.
"

/-- The kernel of a group homomorphism is normal. -/
TheoremDoc MyAlgebra.kernel_isNormal as "kernel_isNormal" in "Normal Subgroups"
Statement kernel_isNormal {G H : Type} [Group G] [Group H] (f : GroupHom G H) :
    f.kernel.IsNormal := by
  intro g n hn
  change f n = 1 at hn
  change f (g * n * g⁻¹) = 1
  Hint "Apply the multiplication and inverse laws of `{f}`, then use `{hn}`."
  rw [f.hom, f.hom, ← hom_preserves_inv f, hn, mul_one, mul_inv]

Conclusion "Every kernel is a normal subgroup. This is true even when the groups
are not abelian."

end MyAlgebra
