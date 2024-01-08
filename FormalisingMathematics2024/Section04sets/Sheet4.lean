/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-!

# Sets in Lean, sheet 4 : making sets from predicates

If we define

`def IsEven (n : ℕ) : Prop := ∃ t, n = 2 * t`

then for `n` a natural, `IsEven n` is a true-false statement,
i.e., a proposition. This means that `IsEven : ℕ → Prop` is
a function taking naturals to true-false statements (also known as
a "predicate" on naturals), so we should be able to make the subset
of naturals where this predicate is true. In Lean the syntax for
this is

`{ n : ℕ | IsEven n }`

The big question you would need to know about sets constructed in this
way is: how do you get from `t ∈ { n : ℕ | IsEven n }` to `IsEven t`?
And the answer is that these are equal by definition.

The general case: if you have a type `X` and a predicate `P : X → Prop`
then the subset of `X` consisting of the terms where the predicate is
true, is `{ x : X | P x }`, and the proof that `a ∈ { x : X | P x } ↔ P a` is `rfl`.

Let's check:
-/

namespace Section4sheet4

theorem mem_def (X : Type) (P : X → Prop) (a : X) :
    a ∈ {x : X | P x} ↔ P a := by
  rfl

/-

Of course, now we've proved this theorem, you can
`rw [mem_def]` if you don't want to (ab)use definitional equality.

-/
open Set

def IsEven (n : ℕ) : Prop :=
  ∃ t, n = 2 * t

-- note that this is *syntactically* equal to `IsEven : ℕ → Prop := fun n ↦ ∃ t, n = 2 * t`
-- but the way I've written it is perhaps easier to follow.

example : 74 ∈ {n : ℕ | IsEven n} := by
  sorry

-- Let's develop a theory of even real numbers
def Real.IsEven (r : ℝ) :=
  ∃ t : ℝ, r = 2 * t

-- Turns out it's not interesting
example : ∀ x, x ∈ {r : ℝ | Real.IsEven r} := by
  sorry

-- likewise, the theory of positive negative real numbers is not interesting
example : ∀ x, x ∉ {r : ℝ | 0 < r ∧ r < 0} := by
  sorry
