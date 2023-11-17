/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import solutions.section05sets.sheet5

/-!

# Sets in Lean, sheet 5 : equality of sets

Sets are extensional objects to mathematicians, which means that
if two sets have the same elements, then they are equal. 

## Tactics 

Tactics you will need to know for this sheet:

* `ext`

### The `ext` tactic

If the goal is `⊢ A = B` where `A` and `B` are subsets of `X`, then
the tactic `ext x,` will create a hypothesis `x : X` and change
the goal to `x ∈ A ↔ x ∈ B`.

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
open Set

variable (X : Type)
  -- Everything will be a subset of `X`
  (A B C D E : Set X)
  -- A,B,C,D,E are subsets of `X`
  (x y z : X)

-- x,y,z are elements of `X` or, more precisely, terms of type `X`
example : A ∪ A = A := by
  ext x
  constructor
  · rintro (hA | hA) <;> exact hA
  · intro h
    left
    exact h

example : A ∩ A = A :=
  inter_self A

-- found with `squeeze_simp`
example : A ∩ ∅ = ∅ := by
  ext x
  constructor
  · rintro ⟨hx, ⟨⟩⟩
  · rintro ⟨⟩

example : A ∪ univ = univ := by simp

--set_option pp.notation false
example : A ⊆ B → B ⊆ A → A = B :=
  by
  -- library_search works
  intro hAB hBA
  ext x
  exact ⟨@hAB x, @hBA x⟩

example : A ∩ B = B ∩ A :=
  inter_comm A B

-- found with library_search
example : A ∩ (B ∩ C) = A ∩ B ∩ C := by
  symm
  exact inter_assoc A B C

-- I guessed the name!
example : A ∪ (B ∪ C) = A ∪ B ∪ C := by
  ext x
  constructor
  · rintro (hA | hB | hC)
    · left; left; assumption
    · left; right; assumption
    · right; assumption
  · rintro ((hA | hB) | hC)
    · left; assumption
    · right; left; assumption
    · right; right; assumption

example : A ∪ B ∩ C = (A ∪ B) ∩ (A ∪ C) :=
  union_distrib_left A B C

-- thanks library_search
example : A ∩ (B ∪ C) = A ∩ B ∪ A ∩ C :=
  inter_distrib_left A B C

-- guessed what this
-- was called on basis of previous answer
