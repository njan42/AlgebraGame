import Game.Levels.Order.L01_Identity
import Game.Levels.Order.L02_Inverse
import Game.Levels.Order.L03_PowerDivides
import Game.Levels.Order.L04_PowerFormula
import Game.Levels.Order.L05_Divisor
import Game.Levels.Order.L06_ProductPower
import Game.Levels.Order.L07_CoprimeFactor
import Game.Levels.Order.L08_CoprimeProduct
import Game.Levels.Order.L09_LeastCommonMultiple
import Game.Levels.Order.L10_Cyclic
import Game.Levels.Order.L11_Generators

World "Order"
Title "Orders and Generators"

Introduction "
Consider the equation $g^n = 1$ in a group. The smallest positive integer
$n$ for which this equation holds is called the order of the element $g$.

The order of an element might be infinite (e.g. $1 ∈ \\mathbb{Z}$ under addition) in
which case we say that $g$ has order $0$.

We will study how orders change under inverses, powers, and products.
For products, commutativity and common factors between the orders make a difference.
Finally, we will study cyclic groups: groups whose elements are all powers of one generator.
"
