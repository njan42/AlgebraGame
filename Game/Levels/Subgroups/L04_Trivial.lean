import Game.Levels.Subgroups.L03_InvClosure

World "Subgroups"
Level 4

Title "Just the Identity"

namespace MyAlgebra

Introduction "
The trivial subgroup contains only the identity. Its carrier is `{x : G | x = 1}`.

`IsSubgroupSet S` means that `S` contains `1`, is closed under multiplication,
and is closed under inverses. These conditions form a conjunction.
`Subgroup.ofSet S` constructs a subgroup from proofs of these conditions.

Is the set containing only the identity closed under both operations?
"

/-- Just the Identity. -/
TheoremDoc MyAlgebra.trivial_isSubgroupSet as "trivial_isSubgroupSet" in "Subgroups"
Statement trivial_isSubgroupSet {G : Type} [Group G] : IsSubgroupSet {x : G | x = 1} := by
  constructor
  · rfl
  constructor
  · intro a b ha hb
    Hint "Use `change` to express memberships as equalities."
    change a = 1 at ha
    change b = 1 at hb
    change a * b = 1
    rw [ha, hb, one_mul]
  · intro a ha
    change a = 1 at ha
    change a⁻¹ = 1
    rw [ha, inv_one]

/-- `IsSubgroupSet S` is the conjunction of identity, multiplication, and inverse closure. -/
DefinitionDoc MyAlgebra.IsSubgroupSet as "IsSubgroupSet" in "Subgroups"
/-- `Subgroup.ofSet S hS` constructs a subgroup with carrier `S` from its closure proofs. -/
DefinitionDoc MyAlgebra.Subgroup.ofSet as "Subgroup.ofSet" in "Subgroups"
NewDefinition MyAlgebra.IsSubgroupSet MyAlgebra.Subgroup.ofSet

Conclusion "Every group has a trivial subgroup, even when the group itself has many elements."

end MyAlgebra
