import Game.MyAlgebra.Z_mod_mZ
import Game.MyAlgebra.AddMul_Group_Def

namespace MyAlgebra

inductive Dihedral (n : ℕ) : Type
  | r : ZMod n → Dihedral n
  | sr : ZMod n → Dihedral n
  deriving DecidableEq

namespace Dihedral

variable {n : ℕ}

def mul : Dihedral n → Dihedral n → Dihedral n
  | r i, r j => r (i + j)
  | r i, sr j => sr (j - i)
  | sr i, r j => sr (i + j)
  | sr i, sr j => r (j - i)

instance : Group (Dihedral n) where
  mul := mul
  one := r 0
  inv := fun a => match a with | r i => r (-i) | sr i => sr i
  mul_assoc := by
    intro a b c
    change mul (mul a b) c = mul a (mul b c)
    cases a <;> cases b <;> cases c <;> simp only [mul]
    all_goals congr 1 <;> abel
  one_mul := by
    intro a
    change mul (r 0) a = a
    cases a <;> simp [mul]
  mul_one := by
    intro a
    change mul a (r 0) = a
    cases a <;> simp [mul]
  inv_mul := by
    intro a
    cases a with
    | r i => change r (-i + i) = r 0; rw [neg_add_cancel]
    | sr i => change r (i - i) = r 0; rw [sub_self]
  mul_inv := by
    intro a
    cases a with
    | r i => change r (i + -i) = r 0; rw [add_neg_cancel]
    | sr i => change r (i - i) = r 0; rw [sub_self]

lemma r_mul_r (i j : ZMod n) : r i * r j = r (i + j) := rfl
lemma r_mul_sr (i j : ZMod n) : r i * sr j = sr (j - i) := rfl
lemma sr_mul_r (i j : ZMod n) : sr i * r j = sr (i + j) := rfl
lemma sr_mul_sr (i j : ZMod n) : sr i * sr j = r (j - i) := rfl

end Dihedral
end MyAlgebra
