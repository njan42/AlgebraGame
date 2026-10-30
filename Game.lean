import Game.Levels.Monoid
import Game.Levels.Group
import Game.Levels.PowMonoid
import Game.Levels.PowGroup
import Game.Levels.Functions
import Game.Levels.GroupHom
import Game.Levels.Sets
import Game.Levels.Subgroups
import Game.Levels.KernelImage
import Game.Levels.Cosets
import Game.Levels.Lagrange
import Game.Levels.Normal
import Game.Levels.Ring
import Game.Levels.GroupExamples
import Game.Levels.Order


Title "Algebra Game"
Introduction "
# Welcome to the Algebra Game

Learn about monoids, groups, and rings by proving their basic properties in Lean.
The game also covers functions, sets, subgroups, cosets, and element orders.

This game assumes some experience with Lean. If you're new to Lean, start with the
[Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4).
"

Info "An abstract algebra game built with Lean 4 and the Lean Game Server."

Languages "English"
CaptionShort "Introduction to basic algebra"
CaptionLong "Prove basic results about monoids, groups, functions, subgroups, cosets, and rings in Lean."

-- World prerequisites.
Dependency Group → Ring
Dependency Group → «Group Examples»
Dependency Group → Functions → GroupHom → Sets → Subgroups → KernelImage
Dependency Subgroups → Cosets → Lagrange
Dependency «Group Power» → Order
Dependency «Group Examples» → Order
Dependency Functions → Order

Dependency Cosets → Normal
Dependency KernelImage → Normal

MakeGame
