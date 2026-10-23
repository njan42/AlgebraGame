import Game.Levels.PowMonoid.L01_PowOne
import Game.Levels.PowMonoid.L02_PowSuccLeft
import Game.Levels.PowMonoid.L03_PowAdd
import Game.Levels.PowMonoid.L04_PowMul
import Game.Levels.PowMonoid.L05_PowId
import Game.Levels.PowMonoid.L06_PowCommMul
import Game.Levels.PowMonoid.L07_PowCommPow


World "Monoid Power"
Title "Monoid Power World"

Introduction "
Powers repeat the monoid operation. We use `m ^ n` for natural-number exponents.
The definition gives two rules:

- `mpow_zero`: `m ^ 0 = 1`
- `mpow_succ_right`: `m ^ (n + 1) = m ^ n * m`

Use these rules and the monoid laws to prove the familiar exponent laws.
Some proofs use natural-number induction, as in the Natural Number Game.
"
