import Mathlib

namespace MyAlgebra

/-- Nonempty sets covering a type, with any two intersecting pieces equal. -/
def IsPartition {A : Type} (parts : Set (Set A)) : Prop :=
  (∀ S ∈ parts, S.Nonempty) ∧
  (∀ x, ∃ S ∈ parts, x ∈ S) ∧
  (∀ S ∈ parts, ∀ T ∈ parts, ∀ x, x ∈ S → x ∈ T → S = T)

/-- A finite type partitioned into equal-sized pieces has size: number of pieces times size. -/
theorem card_partition {A : Type} [Finite A] (parts : Set (Set A)) (n : ℕ)
    (hp : IsPartition parts) (hs : ∀ S ∈ parts, Nat.card S = n) :
    Nat.card A = Nat.card parts * n := by
  classical
  letI := Fintype.ofFinite parts
  have hb : Function.Bijective (fun p : Σ S : parts, S.val => p.2.val) := by
    constructor
    · intro x y hxy
      obtain ⟨⟨S, hS⟩, ⟨x, hx⟩⟩ := x
      obtain ⟨⟨T, hT⟩, ⟨y, hy⟩⟩ := y
      change x = y at hxy
      subst y
      have hST := hp.2.2 S hS T hT x hx hy
      subst T
      rfl
    · intro x
      obtain ⟨S, hS, hx⟩ := hp.2.1 x
      exact ⟨⟨⟨S, hS⟩, ⟨x, hx⟩⟩, rfl⟩
  have heq := Nat.card_eq_of_bijective _ hb
  rw [Nat.card_sigma] at heq
  have hs' : ∀ S : parts, Nat.card S.val = n := fun S => hs S.val S.property
  simp only [hs', Finset.sum_const, Finset.card_univ, smul_eq_mul] at heq
  rw [← Nat.card_eq_fintype_card] at heq
  exact heq.symm

end MyAlgebra
