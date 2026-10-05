import Game.Levels.Sets
import Game.MyAlgebra.Subgroup_Def

World "Subgroups"
Level 1

Title "A Subgroup Has an Element"

namespace MyAlgebra

Introduction "
A subgroup is a set of elements of a group that contains the identity and is
closed under multiplication and inverses. It uses the same operations as the
group it's a subgroup of.

Here `H : Subgroup G` names a subgroup, while `x : G` names an element.
The notation `x ∈ H` says that the element belongs to its carrier.
`H.one_mem` is the proof that `1 ∈ H`.

Could a subgroup be empty? Prove that it has an element.
"

/-- A Subgroup Has an Element. -/
TheoremDoc MyAlgebra.subgroup_nonempty as "subgroup_nonempty" in "Subgroups"
Statement subgroup_nonempty {G : Type} [Group G] (H : Subgroup G) : ∃ x : G, x ∈ H := by
  Hint "Which element does every subgroup contain?"
  use 1
  exact H.one_mem

/-- A subgroup is a carrier set containing the identity and closed under products and inverses. -/
DefinitionDoc MyAlgebra.Subgroup as "Subgroup" in "Subgroups"
/-- `H.one_mem` proves that the identity belongs to `H`. -/
TheoremDoc MyAlgebra.Subgroup.one_mem as "Subgroup.one_mem" in "Subgroups"
NewDefinition MyAlgebra.Subgroup
NewTheorem MyAlgebra.Subgroup.one_mem

Conclusion "Every subgroup contains the identity; nonemptiness is part of its structure."

end MyAlgebra
