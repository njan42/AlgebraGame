import Game.Levels.PowGroup
import Mathlib


namespace MyAlgebra.ElementOrder

private def OrderModel (G : Type) := G
private instance {G : Type} [Group G] : _root_.Group (OrderModel G) where
  mul := fun a b => (show G from a) * (show G from b)
  one := (1 : G)
  inv := fun a => @Inv.inv G _ a
  mul_assoc := fun a b c => @MyAlgebra.Semigroup.mul_assoc G _ a b c
  one_mul := fun a => @one_mul G _ a
  mul_one := fun a => @mul_one G _ a
  inv_mul_cancel := fun a => @MyAlgebra.Group.inv_mul G _ a
  npow := fun n g => @mpow G _ g n
  npow_zero := fun _ => rfl
  npow_succ := fun _ _ => rfl
  zpow := fun n g => @gpow G _ g n
  zpow_zero' := fun _ => rfl
  zpow_succ' := fun _ _ => rfl
  zpow_neg' := fun n g => (@inv_mpow G g (n + 1) inferInstance).symm

private instance {G : Type} [Finite G] : Finite (OrderModel G) :=
  inferInstanceAs (Finite G)

/-- The least positive exponent returning to `1`, or `0` for infinite order. -/
noncomputable def order {G : Type} [Group G] (g : G) : ℕ :=
  orderOf (show OrderModel G from g)

lemma pow_order {G : Type} [Group G] (g : G) : g ^ order g = 1 :=
  pow_orderOf_eq_one (show OrderModel G from g)

lemma order_dvd_iff {G : Type} [Group G] (g : G) (n : ℕ) :
    order g ∣ n ↔ g ^ n = 1 :=
  @orderOf_dvd_iff_pow_eq_one (OrderModel G) _ (show OrderModel G from g) n

lemma order_pos {G : Type} [Group G] [Finite G] (g : G) : 0 < order g :=
  _root_.orderOf_pos (show OrderModel G from g)

/-- Remove the common factor before testing divisibility of a product. -/
lemma gcd_quotient_dvd_iff (n k t : ℕ) (hn : n ≠ 0) :
    n / Nat.gcd n k ∣ t ↔ n ∣ k * t := by
  rw [Nat.div_dvd_iff_dvd_mul (Nat.gcd_dvd_left n k)
    (Nat.gcd_pos_of_pos_left k (Nat.pos_of_ne_zero hn)), Nat.dvd_gcd_mul_iff_dvd_mul]

/-- Allocate each prime power in the LCM to one of the two numbers. -/
lemma coprime_lcm_parts (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ a b, a ∣ m ∧ b ∣ n ∧ Nat.Coprime a b ∧ a * b = Nat.lcm m n := by
  exact ⟨Nat.factorizationLCMLeft m n, Nat.factorizationLCMRight m n,
    Nat.factorizationLCMLeft_dvd_left m n, Nat.factorizationLCMRight_dvd_right m n,
    Nat.coprime_factorizationLCMLeft_factorizationLCMRight m n,
    Nat.factorizationLCMLeft_mul_factorizationLCMRight hm hn⟩

/-- Every element is an integer power of the generator. -/
def Generates {G : Type} [Group G] (g : G) : Prop :=
  ∀ x : G, ∃ n : ℤ, g ^ n = x

/-- A cyclic group has a generator. -/
def Cyclic (G : Type) [Group G] : Prop := ∃ g : G, Generates g

private lemma generates_iff_card {G : Type} [Group G] [Finite G] (g : G) :
    Generates g ↔ order g = Nat.card G := by
  have hz : Generates g ↔ _root_.Subgroup.zpowers (show OrderModel G from g) = ⊤ := by
    constructor
    · intro hg
      apply (_root_.Subgroup.eq_top_iff' _).mpr
      intro x
      exact hg x
    · intro hg x
      exact (_root_.Subgroup.eq_top_iff' _).mp hg x
  rw [hz, ← _root_.Subgroup.card_eq_iff_eq_top, Nat.card_zpowers]
  rfl

/-- In a finite cyclic group, generators are exactly the elements of full order. -/
lemma generates_iff_same_order {G : Type} [Group G] [Finite G] (g a : G)
    (hg : Generates g) : Generates a ↔ order a = order g := by
  rw [generates_iff_card, (generates_iff_card g).mp hg]

end MyAlgebra.ElementOrder
