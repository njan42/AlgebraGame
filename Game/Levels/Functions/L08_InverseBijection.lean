import Game.Levels.Functions.L07_Bijective

World "Functions"
Level 8

Title "Inversion Pairs the Elements"

namespace MyAlgebra

Introduction "
Now consider the map `fun x : G => x⁻¹`. Is it a bijection?
Which facts from the Group world could help you check the two required properties?
"

/-- Inversion is a bijection on any group. -/
TheoremDoc MyAlgebra.inverse_bijective as "inverse_bijective" in "Functions"
Statement inverse_bijective {G : Type} [Group G] :
    Function.Bijective (fun x : G => x⁻¹) := by
  constructor
  · intro a b h
    Hint "Use `change` to express `{h}` as an equality of inverses."
    change a⁻¹ = b⁻¹ at h
    Hint "Compare the double inverses using `{h}`, then use `inv_inv`."
    calc
      a = a⁻¹⁻¹ := inv_inv a
      _ = b⁻¹⁻¹ := by rw [h]
      _ = b := by rw [← inv_inv]
  · intro y
    Hint "Which input has inverse `{y}`?"
    use y⁻¹
    Hint "What does the function return at your chosen input?
    The theorem `inv_inv` relates an element to its double inverse."
    change y⁻¹⁻¹ = y
    rw [← inv_inv]

Conclusion "Inversion is always a bijection, but in general it reverses the order of a product:
`(a * b)⁻¹ = b⁻¹ * a⁻¹`. Being bijective and preserving multiplication are different properties.
"

end MyAlgebra
