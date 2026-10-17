import Game.Levels.Cosets.L08_Disjoint

World "Cosets"
Level 9

Title "A Coset Has as Many Elements as the Subgroup"

namespace MyAlgebra

Introduction "
Left multiplication sends each element of `H` to an element of `gH`.
`H.leftCosetMap g` is this function, with domain and target restricted to those sets.

An element of a restricted set has a value `x.val` and a membership proof `x.property`.
The pair `⟨h, hh⟩` gives an element and a proof that it belongs to the subgroup.
`Subtype.ext` proves two such elements equal by comparing their values.
`congrArg k heq` applies a function `k` to both sides of an equality `heq`.

Is left multiplication injective on `H`? Does it reach every element of `gH`?
Prove that this restricted function is bijective.
"

/-- Left multiplication is a bijection from the subgroup to its left coset. -/
TheoremDoc MyAlgebra.leftCosetMap_bijective as "leftCosetMap_bijective" in "Cosets"
Statement leftCosetMap_bijective {G : Type} [Group G] (H : Subgroup G)
    (g : G) : Function.Bijective (H.leftCosetMap g) := by
  constructor
  · intro a b hab
    Hint "Compare values using `Subtype.ext`, then cancel left multiplication by `{g}`."
    apply Subtype.ext
    apply mul_left_cancel g
    Hint "The function `Subtype.val` extracts an underlying value.
    The theorem `congrArg` lets you apply a function to both sides of an equality."
    have hval := congrArg Subtype.val hab
    exact hval
  · intro y
    Hint "Unpack `{y}.property`: coset membership already supplies an input from `{H}`."
    obtain ⟨h, hh, hy⟩ := y.property
    use ⟨h, hh⟩
    apply Subtype.ext
    change g * h = y.val
    rw [hy]

/-- `H.leftCosetMap g` sends `h` in `H` to `g * h` in its left coset.
The membership proof is built into the function. -/
DefinitionDoc MyAlgebra.Subgroup.leftCosetMap as "Subgroup.leftCosetMap" in "Cosets"
/-- `x.val` is the underlying value of an element paired with a membership proof. -/
DefinitionDoc Subtype.val as "Subtype.val" in "Sets"
/-- `x.property` is the membership proof accompanying the value `x.val`. -/
DefinitionDoc Subtype.property as "Subtype.property" in "Sets"
/-- `Subtype.ext` proves equality of elements with membership proofs
from equality of their values. -/
TheoremDoc Subtype.ext as "Subtype.ext" in "Sets"
/-- `congrArg k h` applies the function `k` to both sides of the equality `h`. -/
TheoremDoc congrArg as "congrArg" in "Logic"
NewDefinition MyAlgebra.Subgroup.leftCosetMap Subtype.val Subtype.property
NewTheorem Subtype.ext congrArg

Conclusion "Left multiplication pairs the elements of a subgroup
with the elements of each left coset.
For finite groups this will let us count equal-sized pieces and prove Lagrange's theorem."

end MyAlgebra
