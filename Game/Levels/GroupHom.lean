import Game.Levels.GroupHom.L01_HomPreservesOne
import Game.Levels.GroupHom.L02_HomPreservesInv
import Game.Levels.GroupHom.L03_IdHom
import Game.Levels.GroupHom.L04_OneHom
import Game.Levels.GroupHom.L05_HomCompHom

World "GroupHom"
Title "Group Homomorphisms"

Introduction "
  A group homomorphism is a function that preserves multiplication. These maps let us compare groups while keeping track of their algebraic structure.

  So what makes up the group structure? Well, we have a set `α`, a binary operation `*`, an identity element `1`, and inverses. Therefore, we need to define a function that preserves these aspects.

  It turns out that we only need the binary operation to be preserved. And in the next two levels we get the other two for free.
"
