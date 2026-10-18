import Game.Levels.Normal.L05_LeftToRight

World "Normal"
Level 6

Title "Left and Right Cosets Agree"

namespace MyAlgebra

Introduction "
Finish comparing the left and right cosets of a normal subgroup.
The previous level proved one inclusion.

If `x = n * g`, which element of `N` could express `x` as `g * m`?
Normality applies to `g⁻¹` as well as to `g`.
"

/-- A normal subgroup has equal left and right cosets for every representative. -/
TheoremDoc MyAlgebra.normal_leftCoset_eq_rightCoset as "normal_leftCoset_eq_rightCoset"
  in "Normal Subgroups"
Statement normal_leftCoset_eq_rightCoset {G : Type} [Group G] (N : Subgroup G)
    (hN : N.IsNormal) (g : G) : N.leftCoset g = N.rightCoset g := by
  apply Set.ext
  intro x
  constructor
  · intro hx
    exact normal_leftCoset_subset_rightCoset N hN g hx
  · intro hx
    obtain ⟨n, hn, hx⟩ := hx
    Hint "Conjugate `{n}` by `{g}⁻¹`. Simplify its double inverse with `← inv_inv`."
    have hm := hN g⁻¹ n hn
    rw [← inv_inv] at hm
    use g⁻¹ * n * g
    constructor
    · exact hm
    · rw [hx, ← mul_assoc, ← mul_assoc, mul_inv, one_mul]

Conclusion "For a normal subgroup, `gN = Ng` for every `g`.
These sets can agree even though individual elements do not commute."

end MyAlgebra
