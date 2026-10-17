import Game.Levels.Cosets.L02_Identity

World "Cosets"
Level 3

Title "Testing Coset Membership"

namespace MyAlgebra

Introduction "
Multiplying by `g⁻¹` on the left undoes multiplication by `g`.

Can you test whether `x` belongs to `gH` by checking a membership in `H`?
Prove the equivalence below without changing the order of the factors.
"

/-- Membership in `gH` is equivalent to `g⁻¹ * x ∈ H`. -/
TheoremDoc MyAlgebra.mem_leftCoset_iff as "mem_leftCoset_iff" in "Cosets"
Statement mem_leftCoset_iff {G : Type} [Group G] (H : Subgroup G)
    (g x : G) :
    x ∈ H.leftCoset g ↔ g⁻¹ * x ∈ H := by
  constructor
  · intro hx
    obtain ⟨h, hh, hx⟩ := hx
    Hint "Replace `{x}` using `{hx}`, then associate the inverse with `{g}`."
    rw [hx, ← mul_assoc, inv_mul, one_mul]
    exact hh
  · intro hx
    Hint "Which element remains after undoing left multiplication by `{g}`? Use it as a witness."
    use g⁻¹ * x
    constructor
    · exact hx
    · rw [← mul_assoc, mul_inv, one_mul]

Conclusion "Left-coset membership is equivalent to `g⁻¹ * x ∈ H`.
For right cosets the order would be different since groups may not necessarily be commutative."

end MyAlgebra
