import Game.Levels.Group
import Game.Levels.PowMonoid

namespace MyAlgebra

/-- Integer powers extend natural powers using inverses for negative exponents. -/
def gpow {G : Type} [Group G] (x : G) : ℤ → G
  | Int.ofNat n => mpow x n
  | Int.negSucc n => mpow x⁻¹ (n + 1)

instance {G : Type} [Group G] : HPow G ℤ G where
  hPow := gpow

@[simp]
lemma gpow_eq_hpow (g : G) (n : ℤ) [Group G] : gpow g n = g ^ n := rfl

@[simp]
lemma gpow_ofNat (g : G) (n : ℕ) [Group G] : g ^ (n : ℤ) = g ^ n := rfl

@[simp]
lemma gpow_negSucc (g : G) (n : ℕ) [Group G] :
    g ^ (Int.negSucc n) = (g⁻¹) ^ (n + 1) := rfl

@[simp]
lemma inv_mpow (g : G) (n : ℕ) [Group G] : (g ^ n)⁻¹ = (g⁻¹) ^ n := by
  induction n with
  | zero => rw [mpow_zero, mpow_zero, inv_one]
  | succ n ih =>
    rw [mpow_succ_right, ← inv_anticomm, ih, mpow_succ_left]

@[simp]
lemma gpow_zero (g : G) [Group G] : g ^ (0 : ℤ) = 1 := rfl

@[simp]
lemma gpow_one (g : G) [Group G] : g ^ (1 : ℤ) = g := by
  change mpow g 1 = g
  exact mpow_one g

/-- The negative-exponent clause without integer constructor notation. -/
lemma gpow_neg_nat (g : G) (n : ℕ) [Group G] :
    g ^ (-(n : ℤ)) = (g⁻¹) ^ n := by
  cases n <;> rfl

/-- The recursive power rule, valid on both sides of zero. -/
lemma gpow_succ (g : G) (n : ℤ) [Group G] : g ^ (n + 1) = g ^ n * g := by
  cases n with
  | ofNat n => rfl
  | negSucc n =>
    have h : Int.negSucc n + 1 = -(n : ℤ) := by omega
    rw [h, gpow_neg_nat, gpow_negSucc, mpow_succ_right, mul_assoc, inv_mul, mul_one]

/-- Integer induction with integer-valued successor and predecessor cases. -/
@[elab_as_elim]
theorem integer_induction (n : ℤ) {P : ℤ → Prop} (zero : P 0)
    (succ : ∀ k : ℤ, P k → P (k + 1)) (pred : ∀ k : ℤ, P k → P (k - 1)) : P n := by
  induction n using Int.induction_on with
  | zero => exact zero
  | succ n ih => exact succ n ih
  | pred n ih => exact pred (-(n : ℤ)) ih

end MyAlgebra
