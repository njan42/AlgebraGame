import Game.MyAlgebra.Group_Hom_Def
import Game.MyAlgebra.Subgroup_Def

namespace MyAlgebra

variable {G H : Type} [Group G] [Group H]

/-- The kernel set consists of inputs sent to the identity of the target group. -/
def GroupHom.kernelSet (f : GroupHom G H) : Set G := {x | f x = 1}

/-- The image set consists of outputs reached by the homomorphism. -/
def GroupHom.imageSet (f : GroupHom G H) : Set H := {y | ∃ x, f x = y}

end MyAlgebra
