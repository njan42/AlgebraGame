import Game.Levels.GroupExamples.L03_Dihedral_Id

World "Group Examples"
Level 4

Title "Inverses of Symmetries"

namespace MyAlgebra
namespace Dihedral

Introduction "
How do you undo a rotation? What happens when you apply a reflection twice?
Find inverses in each case using the multiplication rules.
"

/-- Inverses of Symmetries. -/
TheoremDoc MyAlgebra.Dihedral.Dihedral_inv as "Dihedral_inv" in "Group Examples"
Statement Dihedral_inv (n : ℕ) (a : Dihedral n) :
    ∃ b : Dihedral n, a * b = r 0 ∧ b * a = r 0 := by
  cases a with
  | r i =>
    use r (-i)
    constructor
    · rw [r_mul_r, add_neg_cancel]
    · rw [r_mul_r, neg_add_cancel]
  | sr i =>
    use sr i
    Hint "The product of a reflection with itself uses `sr_mul_sr`.
    Mathlib's `sub_self i` states `i - i = 0`."
    constructor
    · rw [sr_mul_sr, sub_self]
    · rw [sr_mul_sr, sub_self]

/-- `sub_self a` states `a - a = 0`. -/
TheoremDoc sub_self as "sub_self" in "Group Examples"
NewTheorem sub_self

Conclusion "Congrats!"

end Dihedral
end MyAlgebra
