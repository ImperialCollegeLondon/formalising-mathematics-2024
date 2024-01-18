/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# `Finset X` is a lattice

Recall that a lattice is just a partially ordered set where every pair {a,b} of elements has
an inf `a ⊓ b` and a sup `a ⊔ b`. The type of finite subsets of `X`, ordered by inclusion,
has this property (because the union or intersection of two finite sets is finite).
This lattice structure is inbuilt in Lean.

-/

-- Let X be a type
variable (X : Type)

-- Assume the law of the excluded middle (i.e. that every statement is either true or false)
open scoped Classical

-- Don't worry about whether functions are computable
noncomputable section

-- Then, finally, the type of finite subsets of X has a lattice structure
example : Lattice (Finset X) :=
  inferInstance

-- the system knows this fact automatically so this just works:
example (a b : Finset X) : Finset X :=
  a ⊔ b

-- sups (and infs) make sense

-- The lattice also has a `⊥`, the smallest finite subset of `X`, namely the empty set.
example : Finset X :=
  ⊥

-- But for general `X` it does not have a `⊤`, because if `X` is infinite then it doesn't
-- have a largest finite subset
-- example : Finset X := ⊤ -- uncomment for error

-- If `Y` is another type, then you can push finsets forward along maps from X to Y
variable (Y : Type) (f : X → Y)

example (S : Finset X) : Finset Y :=
  Finset.image f S

-- You can use dot notation to make this shorter
example (S : Finset X) : Finset Y :=
  S.image f

-- See if you can prove these. You'll have to figure out the basic API
-- for `Finset.image`. These theorems are in the library -- your job is simply to find them.
example (S : Finset X) (y : Y) : y ∈ S.image f ↔ ∃ x ∈ S, f x = y := by
  apply Finset.mem_image

example (S : Finset X) (x : X) (hx : x ∈ S) : f x ∈ S.image f := by
  apply Finset.mem_image_of_mem
  exact hx

-- Check that `Finset.image` preserves `≤` (which remember is defined to mean `⊆`)
-- You might have to prove this one directly, using the stuff you discovered above
example (S T : Finset X) (h : S ≤ T) : S.image f ≤ T.image f := by
  intro x -- I couldn't find it :-/ note defeq abuse here
  simp only [Finset.mem_image] -- repeated rewrite
  rintro ⟨a, haS, rfl⟩
  refine ⟨a, ?_, rfl⟩
  apply h
  exact haS
