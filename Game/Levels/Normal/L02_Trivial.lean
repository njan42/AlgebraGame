import Game.Levels.Normal.L01_Conjugation

World "Normal"
Level 2

Title "The Trivial Subgroup Is Normal"

namespace MyAlgebra

Introduction "
The subgroup `Subgroup.trivial G` contains only `1`.
You checked the closure conditions for this set in Subgroups.

Can conjugation take an element of this subgroup outside it?
"

/-- The trivial subgroup is normal. -/
TheoremDoc MyAlgebra.trivial_isNormal as "trivial_isNormal" in "Normal Subgroups"
Statement trivial_isNormal {G : Type} [Group G] : (Subgroup.trivial G).IsNormal := by
  intro g n hn
  change n = 1 at hn
  change g * n * g⁻¹ = 1
  rw [hn]
  exact conjugation_one g

/-- `Subgroup.trivial G` is the subgroup with carrier `{x : G | x = 1}`. -/
DefinitionDoc MyAlgebra.Subgroup.trivial as "Subgroup.trivial" in "Subgroups"
NewDefinition MyAlgebra.Subgroup.trivial

Conclusion "Every group has a normal trivial subgroup. The whole group is also normal,
since every product and inverse already belongs to it."

end MyAlgebra
