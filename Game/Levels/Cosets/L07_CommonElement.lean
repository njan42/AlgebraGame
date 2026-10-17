import Game.Levels.Cosets.L06_Transitive

World "Cosets"
Level 7

Title "One Common Element Is Enough"

namespace MyAlgebra

Introduction "
Two sets can overlap without being equal. Can two left cosets of the same subgroup do that?
Suppose `x` belongs to both `aH` and `bH`. Show that the cosets are equal.

A proved equivalence `h : P ↔ Q` has two directions: `h.mp` takes a proof of `P`
to a proof of `Q`, while `h.mpr` takes a proof of `Q` to a proof of `P`.
You can use these with the coset membership test.
"

/-- Two left cosets of the same subgroup sharing an element are equal. -/
TheoremDoc MyAlgebra.leftCoset_eq_of_common as "leftCoset_eq_of_common" in "Cosets"
Statement leftCoset_eq_of_common {G : Type} [Group G] (H : Subgroup G)
    (a b x : G)
    (hax : x ∈ H.leftCoset a) (hbx : x ∈ H.leftCoset b) :
    H.leftCoset a = H.leftCoset b := by
  Hint "Translate the two memberships into relations using `mem_leftCoset_iff`."
  have hax' := (mem_leftCoset_iff H a x).mp hax
  have hbx' := (mem_leftCoset_iff H b x).mp hbx
  Hint "Reverse the relation from `{b}` to `{x}`, then combine it with the relation from `{a}`."
  have hab := coset_related_trans H a x b hax' (coset_related_symm H b x hbx')
  Hint "`Set.ext` reduces coset equality to comparing membership of an arbitrary element."
  apply Set.ext
  intro y
  constructor
  · intro hy
    apply (mem_leftCoset_iff H b y).mpr
    Hint "Relate `{b}` to `{a}`, then `{a}` to `{y}`."
    exact coset_related_trans H b a y (coset_related_symm H a b hab)
      ((mem_leftCoset_iff H a y).mp hy)
  · intro hy
    apply (mem_leftCoset_iff H a y).mpr
    exact coset_related_trans H a b y hab ((mem_leftCoset_iff H b y).mp hy)

Conclusion "A coset can have many representatives.
A single shared element forces two cosets to be equal."

end MyAlgebra
