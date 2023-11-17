import Mathlib.Tactic.Default
import Algebra.Ring.Equiv

#align_import section09bijections_and_isomorphisms.sheet4

-- ring isomorphisms
-- ring isomorphisms
/-

# Isomorphisms (of groups, rings, etc)

If `X` and `Y` are types, we have a type `X ≃ Y` of bijections
from `X` to `Y`. If `X` and `Y` additionally have the structure
of groups, or rings, or orders, or topological spaces, or...
then we can furthermore ask that the bijections preserves this
structure. 

Just like in the homomorphism case, we don't do this by making
new predicates like `is_group_isomorphism : G ≃ H → Prop`, we do this
by making totally new types called things like `G ≃* H` (group
isomorphisms), `A ≃+* B` (ring isomorphisms) and so on.
 
-/
/-

# Isomorphisms (of groups, rings, etc)

If `X` and `Y` are types, we have a type `X ≃ Y` of bijections
from `X` to `Y`. If `X` and `Y` additionally have the structure
of groups, or rings, or orders, or topological spaces, or...
then we can furthermore ask that the bijections preserves this
structure. 

Just like in the homomorphism case, we don't do this by making
new predicates like `is_group_isomorphism : G ≃ H → Prop`, we do this
by making totally new types called things like `G ≃* H` (group
isomorphisms), `A ≃+* B` (ring isomorphisms) and so on.
 
-/
-- let A and B be rings
-- let A and B be rings
variable (A B : Type) [Ring A] [Ring B]

-- Here's the set of all ring isomorphisms from A to B
example : Type :=
  A ≃+* B

-- `A ≃+* B` is notation for `ring_equiv A B`. 
-- A ring isomorphism is magically a function
example (φ : A ≃+* B) (a : A) : B :=
  φ a

-- if you use this in a proof it will say ⇑φ a
-- A ring isomorphism is magically a ring homomorphism
example (φ : A ≃+* B) (x y : A) : φ (x + y) = φ x + φ y :=
  map_add φ x y

-- You can compose two ring isomorphisms using ring_equiv.trans
-- let C be another ring
variable (C : Type) [Ring C]

-- here using the power of dot notation
example (φ : A ≃+* B) (ψ : B ≃+* C) : A ≃+* C :=
  φ.trans ψ

-- How do you make a ring isomorphism from two invertible ring homomorphisms?
example (φ : A →+* B) (ψ : B →+* A) (h1 : ∀ a, ψ (φ a) = a) (h2 : ∀ b, φ (ψ b) = b) : A ≃+* B :=
  { toFun := φ
    invFun := ψ
    left_inv := h1
    right_inv := h2
    map_add' := φ.map_add
    map_mul' := φ.map_hMul }

-- Notice that `ring_equiv` *extends* `equiv`, so you need to fill in the `equiv` fields and then
-- add in the proofs that `φ(a+b)=φ(a)+φ(b)` and `φ(ab)=φ(a)φ(b)`.
-- Note that we never used that ψ was a ring homomorphism! It follows from the fact that ψ is a bijection
-- whose inverse is a ring homomorphism. But of course Lean knows that the inverse of a ring
-- isomorphism is a ring homomorphism -- it's just a theorem, rather than an axiom.
example (φ : A ≃+* B) (x y : B) : φ.symm (x * y) = φ.symm x * φ.symm y :=
  map_mul φ.symm x y

