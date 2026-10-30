import Game.Levels.GroupHom.L01_HomPreservesOne
import Game.Levels.GroupHom.L02_HomPreservesInv
import Game.Levels.GroupHom.L03_IdHom
import Game.Levels.GroupHom.L04_OneHom
import Game.Levels.GroupHom.L05_HomCompHom
import Game.Levels.GroupHom.L06_HomMulHom

World "GroupHom"
Title "Group Homomorphisms"

Introduction "
A group homomorphism is a function that preserves multiplication:
`f (a * b) = f a * f b`.
We will prove that it also preserves the identity and inverses, then study
some examples, composition, and pointwise products into abelian groups.
"
