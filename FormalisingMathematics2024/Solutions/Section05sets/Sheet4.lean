/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default
import Data.Real.Basic

#align_import solutions.section05sets.sheet4

/-!

# Sets in Lean, sheet 4 : making sets from predicates

If we define

`def is_even (n : ℕ) : Prop := ∃ t, n = 2 * t`

then for `n` a natural, `is_even n` is a true-false statement,
i.e., a proposition. This means that `is_even : ℕ → Prop` is
a function taking naturals to true-false statements (also known as
a "predicate" on naturals), so we should be able to make the subset
of naturals where this predicate is true. In Lean the syntax for
this is

`{ n : ℕ | is_even n }`

The big question you would need to know about sets constructed in this
way is: how do you get from `t ∈ { n : ℕ | is_even n }` to `is_even t`?
And the answer is that these are equal by definition.

The general case: if you have a type `X` and a predicate `P : X → Prop`
then the subset of `X` consisting of the terms where the predicate is
true, is `{ x : X | P x }`, and the proof that `a ∈ { x : X | P x } ↔ P a` is `refl`.
Let's check:
-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- the reals
-- the reals
theorem mem_def (X : Type) (P : X → Prop) (a : X) : a ∈ {x : X | P x} ↔ P a := by rfl

/-

If you want, you can `rw mem_def` instead.

-/
open Set

def IsEven (n : ℕ) : Prop :=
  ∃ t, n = 2 * t

-- note that this is *syntactically* equal to `is_even : ℕ → Prop := λ n, ∃ t, n = 2 * t`
-- but the way I've written it is perhaps easier to follow.
example : 74 ∈ {n : ℕ | IsEven n} :=
  by
  change ∃ t : ℕ, 74 = 2 * t
  -- exact ⟨37, by norm_num⟩, -- works
  use 37
  norm_num

-- Let's develop a theory of even real numbers
def Real.IsEven (r : ℝ) :=
  ∃ t : ℝ, r = 2 * t

-- Turns out it's not interesting
example : ∀ x, x ∈ {r : ℝ | Real.IsEven r} := by
  intro x
  use x / 2
  ring

-- likewise, the theory of positive negative real numbers is not interesting
example : ∀ x, x ∉ {r : ℝ | 0 < r ∧ r < 0} :=
  by
  -- quick way to change the type of `hx` to something definitionally equal
  rintro x (hx : 0 < x ∧ x < 0)
  -- `linarith` is happy to use ∧ hypotheses
  linarith

