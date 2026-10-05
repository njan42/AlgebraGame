import Game.Levels.Subgroups.L05_Whole

World "Subgroups"
Level 6

Title "Common Elements"

namespace MyAlgebra

Introduction "
The set `H.carrier ∩ K.carrier` consists of elements belonging to both subgroups.

Do the identity, products, and inverses remain in both subgroups?
Check the three conditions for their intersection.
"

/-- Common Elements. -/
TheoremDoc MyAlgebra.intersection_isSubgroupSet as "intersection_isSubgroupSet" in "Subgroups"
Statement intersection_isSubgroupSet {G : Type} [Group G] (H K : Subgroup G) :
    IsSubgroupSet (H.carrier ∩ K.carrier) := by
  constructor
  · exact ⟨H.one_mem, K.one_mem⟩
  constructor
  · intro a b ha hb
    Hint "Each membership has two parts. Apply each subgroup's closure field separately."
    exact ⟨H.mul_closure ha.1 hb.1, K.mul_closure ha.2 hb.2⟩
  · intro a ha
    exact ⟨H.inv_closure ha.1, K.inv_closure ha.2⟩

Conclusion "Intersections are always subgroups. Unions may not necessarily be:
a mixed product may leave both sets."

end MyAlgebra
