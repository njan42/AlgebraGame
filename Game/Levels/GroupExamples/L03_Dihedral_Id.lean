import Game.Levels.GroupExamples.L02_Z_mod_mZ_Inv
import Game.MyAlgebra.Dihedral

World "Group Examples"
Level 3

Title "The Identity Symmetry"

namespace MyAlgebra
namespace Dihedral

Introduction "
The dihedral group describes rotations and reflections of a regular polygon.
For `n ≥ 3`, it has `n` rotations and `n` reflections.

For example, a square has eight symmetries:
```
1-----2
|     |
4-----3
```

`r i` is a rotation and `sr i` is a reflection, with `i : ZMod n`.
The four multiplication rules are in the inventory as `r_mul_r`, `r_mul_sr`,
`sr_mul_r`, and `sr_mul_sr`. Multiplication means composition of symmetries.

Which symmetry changes nothing? Find it and check both identity products.
Use `cases a with | r i => ... | sr i => ...` to consider each kind of symmetry.
"

/-- The Identity Symmetry. -/
TheoremDoc MyAlgebra.Dihedral.Dihedral_id as "Dihedral_id" in "Group Examples"
Statement Dihedral_id (n : ℕ) (a : Dihedral n) :
    ∃ b : Dihedral n, a * b = a ∧ b * a = a := by
  use r 0
  cases a with
  | r i =>
    Hint "The rule `r_mul_r` reduces a product of rotations to addition in `ZMod n`."
    constructor
    · rw [r_mul_r, add_zero]
    · rw [r_mul_r, zero_add]
  | sr i =>
    Hint "Use `sr_mul_r` and `r_mul_sr` for the mixed products.
    Mathlib's `sub_zero i` simplifies `i - 0`."
    constructor
    · rw [sr_mul_r, add_zero]
    · rw [r_mul_sr, sub_zero]

/-- `r i` is the rotation with index `i`. -/
DefinitionDoc MyAlgebra.Dihedral.r as "r" in "Group Examples"
/-- `sr i` is the reflection with index `i`. -/
DefinitionDoc MyAlgebra.Dihedral.sr as "sr" in "Group Examples"
/-- `r i * r j = r (i + j)`. -/
TheoremDoc MyAlgebra.Dihedral.r_mul_r as "r_mul_r" in "Group Examples"
/-- `r i * sr j = sr (j - i)`. -/
TheoremDoc MyAlgebra.Dihedral.r_mul_sr as "r_mul_sr" in "Group Examples"
/-- `sr i * r j = sr (i + j)`. -/
TheoremDoc MyAlgebra.Dihedral.sr_mul_r as "sr_mul_r" in "Group Examples"
/-- `sr i * sr j = r (j - i)`. -/
TheoremDoc MyAlgebra.Dihedral.sr_mul_sr as "sr_mul_sr" in "Group Examples"
/-- `sub_zero a` states `a - 0 = a`. -/
TheoremDoc sub_zero as "sub_zero" in "Group Examples"
/-- `cases a with | r i => ... | sr i => ...` considers the two kinds of symmetry. -/
TacticDoc «cases»
NewDefinition MyAlgebra.Dihedral.r MyAlgebra.Dihedral.sr
NewTheorem MyAlgebra.Dihedral.r_mul_r MyAlgebra.Dihedral.r_mul_sr
  MyAlgebra.Dihedral.sr_mul_r MyAlgebra.Dihedral.sr_mul_sr sub_zero
NewTactic «cases»

Conclusion "Congrats!"

end Dihedral
end MyAlgebra
