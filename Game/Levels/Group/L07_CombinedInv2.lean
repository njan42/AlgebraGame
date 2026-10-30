import Game.Levels.Group.L06_CombinedInv

World "Group"
Level 7

Title "Inverse of a List Product"

namespace MyAlgebra

Introduction "
Does the same reversal rule work for a list of factors?
`prod_list` multiplies the list in order. `prod_list_inv` multiplies the inverses
in reverse order. Both return `1` for the empty list.

Use list induction: the cases are `nil` and `cons a l ih`.
In the second case, `a` is the first element, `l` is the remaining list,
and `ih` is the result for `l`.
"

/-- `prod_list` multiplies the elements of a monoid list in order, with empty product `1`. -/
DefinitionDoc MyAlgebra.prod_list as "prod_list" in "Group"
def prod_list {G : Type} [Monoid G]: List G → G
  | [] => 1
  | (g::l) => g * (prod_list l)

/-- `prod_list_inv` multiplies the inverses in reverse order, with empty product `1`. -/
DefinitionDoc MyAlgebra.prod_list_inv as "prod_list_inv" in "Group"
def prod_list_inv {G : Type} [Group G] : List G → G
  | [] => 1
  | (a::l) => (prod_list_inv l) * (a⁻¹)
NewDefinition MyAlgebra.prod_list MyAlgebra.prod_list_inv

/-- The inverse of a list product is the product of inverses in reverse order. -/
Statement {G} (l : List G) [Group G] : (prod_list_inv l) = (prod_list l)⁻¹ := by
  induction l with
  | nil =>
    Hint "What do `prod_list` and `prod_list_inv` return for the empty list?
    Rewrite their defining equations, then simplify the inverse of the identity."
    rw [prod_list, prod_list_inv, inv_one]
  | cons a l ih =>
    Hint "Expand the two list products, then use `{ih}` and `inv_anticomm`."
    rw [prod_list, prod_list_inv, ih, inv_anticomm]

Conclusion "Congrats!"


/--
```
induction l with
| nil => ...
| cons fst rst => ...
```
proves the empty-list case and the case of adding a first element `fst` to the list `rst`.
-/
TacticDoc induction

NewTactic induction

end MyAlgebra
