import Game.MyAlgebra.Z_mod_mZ
import Game.Levels.Group

World "Group Examples"
Level 1

Title "Addition Modulo a Number"

namespace MyAlgebra

Introduction "
The integers form a group under addition, with identity `0` and inverse `-a`.
They do not form a group under multiplication: which integer could be the inverse of `0`?

What goes wrong if we try to use multiplication as the group law?

`ZMod m` is the group of integers modulo `m`, again using addition.
For example, `11 + 1 = 0` in `ZMod 12`, just as on a clock.
For positive `m`, there are `m` elements. The convention `ZMod 0 = ℤ` includes the integers.

Check that `0` is the identity for addition. The generic identity laws apply for every modulus.
"

/-- Addition Modulo a Number. -/
TheoremDoc MyAlgebra.Z_mod_mZ_id as "Z_mod_mZ_id" in "Group Examples"
Statement Z_mod_mZ_id (m : ℕ) (a : ZMod m) : 0 + a = a ∧ a + 0 = a := by
  constructor
  · Hint "`zero_add a` states `0 + a = a`, including for modular addition."
    rw [zero_add]
  · Hint "`add_zero a` states `a + 0 = a`."
    rw [add_zero]

/-- `ZMod m` is the type of integers modulo `m`; `ZMod 0` is the integers. -/
DefinitionDoc ZMod as "ZMod" in "Group Examples"
NewDefinition ZMod

Conclusion "Congrats!"

end MyAlgebra
