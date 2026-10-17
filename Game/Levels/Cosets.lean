import Game.Levels.Cosets.L01_Representative
import Game.Levels.Cosets.L02_Identity
import Game.Levels.Cosets.L03_Membership
import Game.Levels.Cosets.L04_Reflexive
import Game.Levels.Cosets.L05_Symmetric
import Game.Levels.Cosets.L06_Transitive
import Game.Levels.Cosets.L07_CommonElement
import Game.Levels.Cosets.L08_Disjoint
import Game.Levels.Cosets.L09_Bijection

World "Cosets"
Title "Cosets"

Introduction "
Consider the even integers under addition. Translating them by `1` gives the
odd integers, while translating them by `0` gives the even integers again.
Translating by `2` also gives the even integers: different translations can
describe the same set. These two sets (the set of even integers, and the set
of odd integers) are the cosets of the even integers. Note that the even
integers are a subgroup while odd integers are a coset, but not a subgroup:
they do not contain the identity, `0`.

Our levels use multiplicative notation. For a subgroup `H`, the left coset `gH`
is the set of products `g * h` with `h ∈ H`. We will cover membership, show that
cosets partition the group, and pair each coset with the subgroup itself.
"
