import Game.Levels.GroupHom

World "Sets"
Level 1

Title "Membership Means a Property"

namespace MyAlgebra

Introduction "
A set `S : Set G` is a collection of elements of `G`. The statement `x ∈ S` says
that `x` belongs to it. Type `∈` with `\\in`.

We can describe a set by a property: `{x : G | x * g = g * x}` consists of the elements
that commute with a fixed element `g`. Note, this might not be the entire group.

Prove that the identity does belong. Use `change (1 : G) * g = g * 1` to display
the membership condition, then apply the identity laws. The annotation `(1 : G)`
tells Lean which type contains this identity.
"

/-- The identity commutes with every group element. -/
TheoremDoc MyAlgebra.one_mem_commuting_set as "one_mem_commuting_set" in "Sets"
Statement one_mem_commuting_set {G : Type} [Group G] (g : G) :
    (1 : G) ∈ {x : G | x * g = g * x} := by
  Hint "What property defines this set? Use `change` to express membership as that property."
  change (1 : G) * g = g * 1
  rw [one_mul, mul_one]

/-- `Set A` is the type of sets of elements of `A`.
The notation `{x : A | P x}` describes the set of elements satisfying `P`;
`a ∈ {x : A | P x}` means `P a`. Type `∈` with `\in`. -/
DefinitionDoc Set as "Set" in "Sets"

NewDefinition Set

Conclusion "To prove membership in a set described by a property, prove that property.
Subgroups will be sets whose membership is preserved by the group operations."

end MyAlgebra
