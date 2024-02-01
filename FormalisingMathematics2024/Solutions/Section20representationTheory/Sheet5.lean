/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.RepresentationTheory.FdRep
-- finite-dimensional representations

/-

Here is a fourth way of doing undergraduate representation theory in Lean ;-)

# Finite dimensional representations via category theory

As well as the category `Rep k G` there's the full subcategory of finite-dimensional
representations `FdRep k G`. Let's see it in action!

-/

variable {k : Type} [Field k] {G : Type} [Group G]

/-

The category of representations of G on finite-dimensional k-vector spaces is called `FdRep k G`

-/
example : Type 1 :=
  FdRep k G

/-

Given `V : FdRep k G` here's how to recover the `Representation`:

-/
noncomputable example (V : FdRep k G) : Representation k G V :=
  V.ρ
-- note: the type is `representation k G ↥V`

/-

Conversely, given a finite-dimensional `Representation` we can make an object
of the category.

-/
noncomputable example (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : FdRep k G :=
  FdRep.of ρ

-- Here's how to say that a finite-dimensional representation is irreducible:
open CategoryTheory

example (V : FdRep k G) : Prop :=
  Simple V

-- this is `CategoryTheory.simple`
-- Here's Schur's lemma, stated and proved in the `FdRep` language:
open FiniteDimensional

open scoped Classical

-- if k is alg closed and V,W are irreducible then Hom(V,W) has dimension 1
-- if V ≅ W, and 0 otherwise.
example [IsAlgClosed k] (V W : FdRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  FdRep.finrank_hom_simple_simple V W
