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


-- Here's what we'll put on the title screen
Title "Algebra Game"
Introduction
"
# Welcome to the Algebra Game
#### An introduction to algebraic structures.

Explore abstract algebra through monoids, groups, functions, sets, subgroups,
cosets, powers, homomorphisms, and rings.
This game is a work in progress: the current worlds introduce group theory and the first ring laws.

Start with the [Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/NNG4)
to learn rewriting, implications, and induction. New algebra concepts are introduced as you play.
"

Info "
Built with Lean 4 and the Lean Game Server. This is an introductory course under development.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Introduction to basic algebra"
CaptionLong "An introduction to abstract algebra after the Natural Number Game. Explore monoids, groups, functions, homomorphisms, sets, subgroups, powers, examples, and initial ring laws."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

-- Ring proofs use the additive versions of cancellation learned in Group.
Dependency Group → Ring
Dependency Group → «Group Examples»
-- Functions prepares the notation and proof techniques used by homomorphisms.
-- Sets then prepares subgroups and the two branches studying maps and cosets.
Dependency Group → Functions → GroupHom → Sets → Subgroups → KernelImage
Dependency Subgroups → Cosets → Lagrange
Dependency «Group Power» → Order
Dependency «Group Examples» → Order
Dependency Functions → Order

/-! Build the game. Show's warnings if it found a problem with your game. -/
Dependency Cosets → Normal
Dependency KernelImage → Normal

MakeGame
