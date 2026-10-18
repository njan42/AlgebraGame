import Game.Levels.Subgroups
import Game.MyAlgebra.Coset_Def

namespace MyAlgebra

variable {G : Type} [Group G]

/-- A subgroup is normal when it is closed under conjugation by every ambient group element. -/
def Subgroup.IsNormal (N : Subgroup G) : Prop :=
  ∀ g n : G, n ∈ N → g * n * g⁻¹ ∈ N

/-- The subgroup containing only the identity. -/
def Subgroup.trivial (G : Type) [Group G] : Subgroup G :=
  Subgroup.ofSet {x : G | x = 1} trivial_isSubgroupSet

/-- The right coset `Ng` consists of products `n * g` with `n ∈ N`. -/
def Subgroup.rightCoset (N : Subgroup G) (g : G) : Set G :=
  {x | ∃ n, n ∈ N ∧ x = n * g}

end MyAlgebra
