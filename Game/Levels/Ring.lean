import Game.Levels.Ring.L01_MulZero
import Game.Levels.Ring.L02_NegMul


World "Ring"
Title "Ring World"

Introduction "
  A ring is a set R together with two binary operations `+` and `*` satisfying the following axioms:

  ### The set R together with the binary operation `+` is an abelian group with identity element 0.

  #### Additive Identity Axiom
   There is an element `0 ∈ R` such that

    - zero_add : ∀ r : R, 0 + r = r
    - add_zero : ∀ r : R, r + 0 = r

  #### Additive Inverse Axiom
   For every `r ∈ R` there is an element `s ∈ R` such that

    - add_neg : ∀ r : R, r + (-r) = 0
    - neg_add : ∀ r : R, (-r) + r = 0

  #### Additive Associative Law
   For all `r1, r2, r3 ∈ R`, the associative law holds:

    - add_assoc : ∀ r1 r2 r3 : R, (r1 + r2) + r3 = r1 + (r2 + r3)

  #### Additive Commutative Law
   For all `r1, r2 ∈ R`, the commutative law holds:

    - add_comm : ∀ r1 r2 : R, r1 + r2 = r2 + r1

  ### The set R together with the binary operation `*` is a monoid with identity element 1.

  #### Multiplicative Identity Axiom
   There is an element `1 ∈ R` such that

    - one_mul : ∀ r : R, 1 * r = r
    - mul_one : ∀ r : R, r * 1 = r

  #### Multiplicative Associative Law
   For all `r1, r2, r3 ∈ R`, the associative law holds:

    - mul_assoc : ∀ r1 r2 r3 : R, (r1 * r2) * r3 = r1 * (r2 * r3)

  ### The two binary operations `+` and `*` satisfy the following distributive laws:

  #### Distributing a Factor on the Right
   For all `r1, r2, r3 ∈ R`, distributing the factor on the right gives:

    - distrib_right : ∀ r1 r2 r3 : R, (r1 + r2) * r3 = (r1 * r3) + (r2 * r3)

  #### Distributing a Factor on the Left
   For all `r1, r2, r3 ∈ R`, distributing the factor on the left gives:

    - distrib_left : ∀ r1 r2 r3 : R, r1 * (r2 + r3) = (r1 * r2) + (r1 * r3)
"
