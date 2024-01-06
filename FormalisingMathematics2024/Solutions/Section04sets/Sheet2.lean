/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, example sheet 2 : "the" empty set and the "universal set".

Lean notation for the empty subset of `X` is `∅`. Unlike in
set theory, there is more than one empty set in Lean! Every
type has an empty subset, and it *doesn't even make sense*
to ask if `∅ : set ℕ` and `∅ : set ℤ` are equal, because
they have different types.

At the other extreme, the subset of `X` containing all the terms of type `X`
is...well...mathematicians would just call it `X`, but `X` is a type not a subset.
The subset of `X` consisting of every element of `X` is called `Set.univ : Set X`,
or just `univ : Set X` if we have opened the `Set` namespace. Let's do that now.

-/

open Set

/-

## Definition of ∅ and univ

`x ∈ ∅` is *by definition* equal to `False` and `x ∈ univ` is *by definition*
equal to `True`. You can use the `change` tactic to make these changes
if you like. But you don't have to. Remember that `triv` proves `True`
and `cases h` will solve a goal if `h : False` (because there are no cases!)

-/

-- set up variables
variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

open Set

example : x ∈ (univ : Set X) := by triv

example : x ∈ (∅ : Set X) → False :=
  id

example : A ⊆ univ := by
  intro x hxA
  triv

example : ∅ ⊆ A := by
  -- rintro x ⟨⟩ -- solves goal in one line
  intro x hx
  change False at hx -- unnecessary line
  exfalso
  exact hx
