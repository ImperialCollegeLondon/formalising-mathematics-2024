/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

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

Let's see how this works in practice.

-/

-- let A and B be rings
variable (A B : Type) [Ring A] [Ring B]

-- Here's the type (i.e. the set) of all ring isomorphisms from A to B
example : Type :=
  A ≃+* B

-- `A ≃+* B` is notation for `RingEquiv A B`.
-- A ring isomorphism is magically a function (there is a secret coercion going on)
example (φ : A ≃+* B) (a : A) : B :=
  φ a

-- A ring isomorphism is magically a ring homomorphism
example (φ : A ≃+* B) (x y : A) : φ (x + y) = φ x + φ y :=
  map_add φ x y

-- let C be another ring
variable (C : Type) [Ring C]

-- You can compose two ring isomorphisms using RingEquiv.trans
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
    map_mul' := φ.map_mul }

-- Notice that `RingEquiv` *extends* `Equiv`, so you need to fill in the `Equiv` fields and then
-- add in the proofs that `φ(a+b)=φ(a)+φ(b)` and `φ(ab)=φ(a)φ(b)`.
-- Note that we never used that ψ was a ring homomorphism! It follows from the fact that ψ is
-- a bijection whose inverse is a ring homomorphism. But of course Lean knows that the inverse of a
-- ring isomorphism is a ring homomorphism -- it's just a theorem, rather than an axiom.
example (φ : A ≃+* B) (x y : B) : φ.symm (x * y) = φ.symm x * φ.symm y :=
  map_mul φ.symm x y
