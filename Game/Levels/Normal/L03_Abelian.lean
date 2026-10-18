import Game.Levels.Normal.L02_Trivial

World "Normal"
Level 3

Title "Subgroups of Abelian Groups"

namespace MyAlgebra

Introduction "
A group is abelian when `a * b = b * a` for every pair of elements;
that is, the group operation is commutative.
With `[CommGroup G]`, you can use this law as `mul_comm`.

How does commutativity simplify `g * n * g⁻¹`?
Show that every subgroup of an abelian group is normal.
"

/-- Every subgroup of an abelian group is normal. -/
TheoremDoc MyAlgebra.subgroup_isNormal_of_comm as "subgroup_isNormal_of_comm" in "Normal Subgroups"
Statement subgroup_isNormal_of_comm {G : Type} [CommGroup G] (N : Subgroup G) : N.IsNormal := by
  intro g n hn
  Hint "Commute `{g}` and `{n}`."
  rw [mul_comm g n, mul_assoc, mul_inv, mul_one]
  exact hn

/-- An abelian group is a group with `a * b = b * a` for all elements. -/
DefinitionDoc MyAlgebra.CommGroup as "CommGroup" in "Group"
/-- `mul_comm a b` states `a * b = b * a` in an abelian group. -/
TheoremDoc MyAlgebra.CommGroup.mul_comm as "mul_comm" in "Group"
NewDefinition MyAlgebra.CommGroup
NewTheorem MyAlgebra.CommGroup.mul_comm

Conclusion "In an abelian group, conjugation leaves every element unchanged.
Normal subgroups also occur in nonabelian groups; kernels provide a source of examples."

end MyAlgebra
