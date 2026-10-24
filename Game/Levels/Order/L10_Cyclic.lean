import Game.Levels.Order.L09_LeastCommonMultiple

World "Order"
Level 10

Title "One Element Generates the Group"

namespace MyAlgebra
open ElementOrder

Introduction "
An element `g` **generates** a group if every element is an integer power of `g`.
We write `Generates g` for `∀ x, ∃ n : ℤ, g ^ n = x`.
A group with a generator is called **cyclic**: `Cyclic G` means `∃ g : G, Generates g`.

For example, repeated rotations by one vertex generate all rotations of a polygon.
They do not generate the reflections, so they do not generate the whole dihedral group.

Prove that a cyclic group is abelian.
"

/-- Every cyclic group is abelian. -/
TheoremDoc MyAlgebra.cyclic_commutative as "cyclic_commutative" in "Order"
Statement cyclic_commutative {G : Type} [Group G] :
    Cyclic G → ∀ a b : G, a * b = b * a := by
  Branch
    intro hG
    obtain ⟨g, hg⟩ := hG
    Hint "The generator is chosen. Consider two arbitrary elements and express both as its powers."
    intro a b
    obtain ⟨m, hm⟩ := hg a
    obtain ⟨n, hn⟩ := hg b
    calc
      a * b = g ^ m * g ^ n := by rw [hm, hn]
      _ = g ^ (m + n) := gpow_add _ _ _
      _ = g ^ (n + m) := by
        Hint "The group calculation has become a comparison of integer exponents.
        Which addition law exchanges their order?"
        rw [Int.add_comm]
      _ = g ^ n * g ^ m := by rw [gpow_add]
      _ = b * a := by rw [hn, hm]
  intro hG a b
  obtain ⟨g, hg⟩ := hG
  Hint "Write both elements as integer powers of the generator."
  obtain ⟨m, hm⟩ := hg a
  obtain ⟨n, hn⟩ := hg b
  Hint "What happens when you combine powers of the same base?
  `Int.add_comm` exchanges the two integer exponents."
  rw [← hm, ← hn, gpow_add, gpow_add, Int.add_comm]

/-- `Generates g` means `∀ x, ∃ n : ℤ, g ^ n = x`. -/
DefinitionDoc MyAlgebra.ElementOrder.Generates as "Generates" in "Order"
/-- `Cyclic G` means that `G` has a generator: `∃ g : G, Generates g`. -/
DefinitionDoc MyAlgebra.ElementOrder.Cyclic as "Cyclic" in "Order"
/-- `Int.add_comm m n` states `m + n = n + m`. -/
TheoremDoc Int.add_comm as "Int.add_comm" in "Int"
NewDefinition MyAlgebra.ElementOrder.Generates MyAlgebra.ElementOrder.Cyclic
NewTheorem Int.add_comm

Conclusion "Congrats! All elements of a cyclic group are powers of one element, so they commute."

end MyAlgebra
