import Game.Levels.Cosets
import Game.MyAlgebra.FiniteCounting

World "Lagrange"
Level 1

Title "Counting a Coset"

namespace MyAlgebra

Introduction "
For a finite type `A`, `Nat.card A` is its number of elements.
The assumption `[Finite G]` says that the group has finitely many elements;
its subgroups and cosets are finite too.

The type `H` consists of the elements of the subgroup. The type
`{x : G // x ∈ H.leftCoset g}` consists of the elements of its coset.
Bijections between finite sets imply equal cardinalities of the sets.
In Lean, this is expressed by `Nat.card_eq_of_bijective`.

How does the size of `gH` compare with the size of `H`?
"

/-- Every left coset of a subgroup in a finite group has the same cardinality as the subgroup. -/
TheoremDoc MyAlgebra.coset_card_eq as "coset_card_eq" in "Lagrange"
Statement coset_card_eq {G : Type} [Group G] [Finite G] (H : Subgroup G)
    (g : G) :
    Nat.card {x : G // x ∈ H.leftCoset g} = Nat.card H := by
  Hint "Use the bijection `H.leftCosetMap {g}` proved in Cosets."
  Hint "`Nat.card_eq_of_bijective` turns the bijection into an equality of cardinalities."
  have hsize := Nat.card_eq_of_bijective (H.leftCosetMap g) (leftCosetMap_bijective H g)
  rw [hsize]

/-- For a finite type `A`, `Nat.card A` counts its elements. -/
DefinitionDoc Nat.card as "Nat.card" in "Counting"
/-- `Finite A` asserts that the type has finitely many elements. -/
DefinitionDoc Finite as "Finite" in "Counting"
/-- A bijection `f : A → B` proves `Nat.card A = Nat.card B`. -/
TheoremDoc Nat.card_eq_of_bijective as "Nat.card_eq_of_bijective" in "Counting"
NewDefinition Nat.card Finite
NewTheorem Nat.card_eq_of_bijective

Conclusion "Every left coset has the same number of elements as the subgroup."

end MyAlgebra
