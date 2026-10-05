import Game.Levels.Subgroups.L04_Trivial

World "Subgroups"
Level 5

Title "The Whole Group"

namespace MyAlgebra

Introduction "
The set `Set.univ` contains every element of `G`. Membership in it means `True`:
there is no restriction on the element. The proof `True.intro` establishes `True`.

Does the whole group satisfy all three subgroup conditions?
"

/-- The Whole Group. -/
TheoremDoc MyAlgebra.univ_isSubgroupSet as "univ_isSubgroupSet" in "Subgroups"
Statement univ_isSubgroupSet {G : Type} [Group G] : IsSubgroupSet (Set.univ : Set G) := by
  constructor
  · Hint "Membership in `Set.univ` is `True`, proved by `True.intro`."
    exact True.intro
  constructor
  · intro a b ha hb
    exact True.intro
  · intro a ha
    exact True.intro

/-- `Set.univ` contains every element of its ambient type. -/
DefinitionDoc Set.univ as "Set.univ" in "Sets"
/-- `True.intro` proves the proposition `True`. -/
TheoremDoc True.intro as "True.intro" in "Logic"
NewDefinition Set.univ
NewTheorem True.intro

Conclusion "The whole group is a subgroup of itself. A subgroup may not necessarily be a proper subset."

end MyAlgebra
