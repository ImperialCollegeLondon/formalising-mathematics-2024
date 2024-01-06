/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Sets in Lean, sheet 3 : not in (`∉`) and complement `Aᶜ`

The definition in Lean of `x ∉ A` is `¬ (x ∈ A)`. In other words,
`x ∉ A`, `¬ (x ∈ A)` and `(x ∈ A) → False` are all equal *by definition*
in Lean.

The complement of a subset `A` of `X` is the subset `Aᶜ`; it's the terms of
type `X` which aren't in `A`. The *definition* of `x ∈ Aᶜ` is `x ∉ A`.

For example, if you have a hypothesis `h : x ∈ Aᶜ` and your goal
is `False`, then `apply h` will work and will change the goal to `x ∈ A`.
Think a bit about why, it's a good logic exercise.

-/


open Set

variable (X : Type) -- Everything will be a subset of `X`
  (A B C D E : Set X) -- A,B,C,D,E are subsets of `X`
  (x y z : X) -- x,y,z are elements of `X` or, more precisely, terms of type `X`

example : x ∉ A → x ∈ A → False := by
  intro h
  exact h

example : x ∈ A → x ∉ A → False := by
  intro h1 h2
  exact h2 h1

example : A ⊆ B → x ∉ B → x ∉ A := by
  intro hAB hB hA
  apply hB
  exact hAB hA

-- Lean couldn't work out what I meant when I wrote `x ∈ ∅` so I had
-- to give it a hint by telling it the type of `∅`.
example : x ∉ (∅ : Set X) := by
  intro h
  exact h

example : x ∈ Aᶜ ↔ x ∉ A := by rfl

example : (∀ x, x ∈ A) ↔ ¬∃ x, x ∈ Aᶜ := by
  -- `exact?` works, as does `hint` (which looks for terms or tactics which
  -- solve the goal in one line).
  -- `simp` and `aesop` both work.
  -- also `exact not_exists_not.symm` works
  -- Here's a proof by hand
  constructor
  · rintro h1 ⟨x, hx⟩
    exact hx (h1 x)
  · intro h x
    by_contra h2
    apply h
    exact ⟨x, h2⟩

example : (∃ x, x ∈ A) ↔ ¬∀ x, x ∈ Aᶜ := by aesop -- OK so I got lazy
-- The `aesop` tactic is a general purpose tactic for goals like this.
