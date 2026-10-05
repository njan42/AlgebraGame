import Game.Levels.Group

namespace MyAlgebra

@[ext]
structure Subgroup (G : Type) [Group G] where
  carrier : Set G
  one_mem : 1 ∈ carrier
  mul_closure : ∀ {a b : G}, a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  inv_closure : ∀ {a : G}, a ∈ carrier → a⁻¹ ∈ carrier

variable {G : Type} [Group G]


instance : Coe (Subgroup G) (Set G) := ⟨λ H ↦ H.carrier⟩
instance : CoeSort (Subgroup G) (Type _) := ⟨λ H ↦ H.carrier⟩
instance : Membership G (Subgroup G) := ⟨λ H g ↦ g ∈ H.carrier⟩

attribute [coe] Subgroup.carrier

instance {H : Subgroup G} : Group H where
  mul := λ ⟨a, ha⟩ ⟨b, hb⟩ ↦ ⟨a * b, H.mul_closure ha hb⟩
  mul_assoc := by intros; ext; apply mul_assoc
  one := ⟨1, H.one_mem⟩
  one_mul := by intros; ext; apply one_mul
  mul_one := by intros; ext; apply mul_one
  inv := λ ⟨a, ha⟩ ↦ ⟨a⁻¹, H.inv_closure ha⟩
  inv_mul := by intros; ext; apply inv_mul
  mul_inv := by intros; ext; apply mul_inv

/-- The three closure conditions that make a set a subgroup. -/
def IsSubgroupSet (S : Set G) : Prop :=
  1 ∈ S ∧ (∀ a b, a ∈ S → b ∈ S → a * b ∈ S) ∧ (∀ a, a ∈ S → a⁻¹ ∈ S)

/-- Package verified closure conditions as a subgroup with the chosen carrier. -/
def Subgroup.ofSet (S : Set G) (hS : IsSubgroupSet S) : Subgroup G where
  carrier := S
  one_mem := hS.1
  mul_closure := hS.2.1 _ _
  inv_closure := hS.2.2 _

/-- A nonempty set closed under `x * y⁻¹` is a subgroup. -/
def Subgroup_Criterion (S : Set G) (he : ∃ s, s ∈ S)
    (hc : ∀ x y, x ∈ S → y ∈ S → x * y⁻¹ ∈ S) : Subgroup G := by
  have h1 : 1 ∈ S := by
    obtain ⟨s, hs⟩ := he
    have h := hc s s hs hs
    rw [mul_inv] at h
    exact h
  have hi : ∀ a, a ∈ S → a⁻¹ ∈ S := by
    intro a ha
    have h := hc 1 a h1 ha
    rw [one_mul] at h
    exact h
  apply Subgroup.ofSet S
  constructor
  · exact h1
  constructor
  · intro a b ha hb
    have h := hc a b⁻¹ ha (hi b hb)
    rw [← inv_inv] at h
    exact h
  · exact hi

end MyAlgebra
