import Game.Levels.Monoid.L01_MulLeft
import Game.Levels.Monoid.L02_MulRight
import Game.Levels.Monoid.L03_OneUnique


World "Monoid"
Title "Monoid World"

Introduction "
A monoid has a multiplication `*` and an identity `1`.
The operation is associative:

- `mul_assoc`: `(a * b) * c = a * (b * c)`
- `one_mul`: `1 * a = a`
- `mul_one`: `a * 1 = a`

The natural numbers form a monoid under addition, with identity `0`,
and under multiplication, with identity `1`. For additive notation,
the identity laws are called `zero_add` and `add_zero`.
A monoid may not necessarily have inverses or cancellation.
"
