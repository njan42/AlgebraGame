import Game.Levels.PowGroup.L01_PowNegNat
import Game.Levels.PowGroup.L02_PowNegOne
import Game.Levels.PowGroup.L03_PowPred
import Game.Levels.PowGroup.L04_PowAdd
import Game.Levels.PowGroup.L05_PowNeg
import Game.Levels.PowGroup.L06_PowSub
import Game.Levels.PowGroup.L07_PowMul



World "Group Power"
Title "Group Power World"

Introduction "
Group inverses let us extend powers to integer exponents.
We keep the notation `g ^ n`, now with `n : ℤ`.

```
def gpow {G : Type} [Group G] (x : G) : ℤ → G
| Int.ofNat n => mpow x n
| Int.negSucc n => mpow (x⁻¹) (n+1)
```

- `gpow_zero`: `g ^ (0 : ℤ) = 1`
- `gpow_succ`: `g ^ (n + 1) = g ^ n * g`
- `gpow_neg_nat`: `g ^ (-(n : ℤ)) = (g⁻¹) ^ n` for natural `n`

We will use these rules to prove addition, subtraction, and multiplication laws.
Integer induction starts at zero and takes steps both up and down.
"
