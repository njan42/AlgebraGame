import Game.MyAlgebra.Subgroup_Def

namespace MyAlgebra

variable {G : Type} [Group G]

/-- The left coset `gH` consists of the products `g * h` with `h ∈ H`. -/
def Subgroup.leftCoset (H : Subgroup G) (g : G) : Set G :=
  {x | ∃ h, h ∈ H ∧ x = g * h}

/-- Left multiplication restricted to the subgroup and its left coset. -/
def Subgroup.leftCosetMap (H : Subgroup G) (g : G) :
    H → {x : G // x ∈ H.leftCoset g} :=
  fun h => ⟨g * h.val, h.val, h.property, rfl⟩

/-- The set of distinct left cosets. -/
def Subgroup.leftCosets (H : Subgroup G) : Set (Set G) := Set.range H.leftCoset

/-- For a finite group, the index counts the distinct left cosets. -/
noncomputable def Subgroup.index (H : Subgroup G) : ℕ := Nat.card H.leftCosets

end MyAlgebra
