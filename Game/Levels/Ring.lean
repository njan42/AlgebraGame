import Game.Levels.Ring.L01_MulZero
import Game.Levels.Ring.L02_NegMul


World "Ring"
Title "Ring World"

Introduction "
A ring has two operations. Addition is an abelian group operation, with identity `0`
and inverse `-a`. Multiplication is a monoid operation, with identity `1`.

The distributive laws connect them:

- `distrib_left`: `a * (b + c) = a * b + a * c`
- `distrib_right`: `(a + b) * c = a * c + b * c`

Multiplication may not necessarily be commutative, and elements may not necessarily
have multiplicative inverses. We will start by studying multiplication by zero and negatives.
"
