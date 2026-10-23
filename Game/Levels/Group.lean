import Game.Levels.Group.L01_MulInv
import Game.Levels.Group.L02_CancelLeft
import Game.Levels.Group.L03_CancelRight
import Game.Levels.Group.L04_InvUnique
import Game.Levels.Group.L05_CombinedInv
import Game.Levels.Group.L06_CombinedInv2
import Game.Levels.Group.L07_InvId
import Game.Levels.Group.L08_InvInv
import Game.Levels.Group.L09_InvInj


World "Group"
Title "Group World"

Introduction "
A group is a monoid with an inverse `g⁻¹` for every element `g`.
The monoid laws `mul_assoc`, `one_mul`, and `mul_one` still apply.
The inverse laws are:

- `inv_mul`: `g⁻¹ * g = 1`
- `mul_inv`: `g * g⁻¹ = 1`

Type the inverse symbol with `\\inv`.
We will prove cancellation and uniqueness of inverses, then study inverses of products.
Multiplication may not necessarily be commutative.
"
