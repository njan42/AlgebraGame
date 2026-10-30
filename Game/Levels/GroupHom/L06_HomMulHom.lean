import Game.Levels.GroupHom.L05_HomCompHom

World "GroupHom"
Level 6

Title "Multiplying Homomorphisms"

namespace MyAlgebra

Introduction "
When the target group is abelian, we can multiply two homomorphisms pointwise:
the new map sends `a` to `f1 a * f2 a`.
Commutativity in the target lets us rearrange the factors needed to prove
that this map preserves multiplication. The source group need not be abelian.

Prove that this map preserves multiplication. Use `mul_comm` to exchange factors in the target.
"

/-- Pointwise multiplication of homomorphisms into an abelian group gives a homomorphism. -/
TheoremDoc MyAlgebra.hom_mul_hom as "hom_mul_hom" in "GroupHom"
Statement hom_mul_hom {G H : Type} [Group G] [CommGroup H]
    (f1 f2 : GroupHom G H) :
    ∀ a b, f1 (a * b) * f2 (a * b) = (f1 a * f2 a) * (f1 b * f2 b) := by
  intro a b
  rw [f1.hom, f2.hom]
  rw [mul_assoc, ← mul_assoc (f1 b), mul_comm (f1 b) (f2 a),
    mul_assoc (f2 a), ← mul_assoc]

/-- An abelian group is a group whose multiplication is commutative. -/
DefinitionDoc MyAlgebra.CommGroup as "CommGroup" in "Group"
/-- `mul_comm a b` states `a * b = b * a` in an abelian group. -/
TheoremDoc MyAlgebra.CommGroup.mul_comm as "mul_comm" in "Group"
NewDefinition MyAlgebra.CommGroup
NewTheorem MyAlgebra.CommGroup.mul_comm

Conclusion "The pointwise product preserves multiplication because the target is abelian."

end MyAlgebra
