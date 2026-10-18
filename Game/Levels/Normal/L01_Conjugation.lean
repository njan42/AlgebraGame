import Game.Levels.Cosets
import Game.Levels.KernelImage
import Game.MyAlgebra.Normal_Def

World "Normal"
Level 1

Title "Conjugating the Identity"

namespace MyAlgebra

Introduction "
Conjugating an element `n` by `g` means forming `g * n * g⁻¹`.
A subgroup `N` is called normal when every such conjugate of a member stays in `N`,
for every `g` in the whole group. We write this property as `N.IsNormal`.

What happens when you conjugate the identity?
"

/-- Conjugation fixes the identity. -/
TheoremDoc MyAlgebra.conjugation_one as "conjugation_one" in "Normal Subgroups"
Statement conjugation_one {G : Type} [Group G] (g : G) : g * 1 * g⁻¹ = 1 := by
  rw [mul_one, mul_inv]

/-- `N.IsNormal` means `∀ g n, n ∈ N → g * n * g⁻¹ ∈ N`. -/
DefinitionDoc MyAlgebra.Subgroup.IsNormal as "Subgroup.IsNormal" in "Normal Subgroups"
NewDefinition MyAlgebra.Subgroup.IsNormal

Conclusion "Conjugation fixes the identity. Normality asks for closure under conjugation
by all elements of the ambient group, including those outside the subgroup."

end MyAlgebra
