import Game.Levels.Order.L01_Identity

World "Order"
Level 2

Title "An Element and Its Inverse"

namespace MyAlgebra
open ElementOrder

Introduction "
If repeating a move `n` times returns to the identity, what happens when we repeat
the reverse move `n` times? Show that an element and its inverse have the same order.
This includes elements of infinite order.
"

/-- An element and its inverse have the same order. -/
TheoremDoc MyAlgebra.order_inverse as "order_inverse" in "Order"
Statement order_inverse {G : Type} [Group G] (g : G) : order g⁻¹ = order g := by
  Branch
    apply Nat.dvd_antisymm
    · rw [order_dvd_iff, ← inv_mpow]
      Hint "The inverse is outside the whole power. What is the power inside it?"
      rw [pow_order, inv_one]
    · rw [order_dvd_iff]
      have hcycle := pow_order g⁻¹
      rw [← inv_mpow] at hcycle
      Hint "The equation `{hcycle}` says the inverse of this power is the identity.
      What does taking inverses again tell you?"
      calc
        g ^ order g⁻¹ = (g ^ order g⁻¹)⁻¹⁻¹ := inv_inv _
        _ = (1 : G)⁻¹ := by rw [hcycle]
        _ = 1 := by rw [inv_one]
  apply Nat.dvd_antisymm
  · apply (order_dvd_iff g⁻¹ (order g)).mpr
    Hint "How does `inv_mpow` relate this power to the inverse of a power of `{g}`?"
    rw [← inv_mpow, pow_order, inv_one]
  · apply (order_dvd_iff g (order g⁻¹)).mpr
    Hint "Compare inverses using `inv_inj`. Which power of `{g}⁻¹` is the identity?"
    apply (inv_inj (g ^ order g⁻¹) 1).mp
    rw [inv_mpow, inv_one]
    exact pow_order g⁻¹

Conclusion "Congrats! An element and its inverse have the same order."

end MyAlgebra
