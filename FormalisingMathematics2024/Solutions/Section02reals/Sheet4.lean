/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
/-

# Figuring out how to use the reals

## The `exact?` tactic

We saw in the previous sheet that we couldn't even prove something
as simple as "if `aₙ → L` then `-aₙ → -L`" because when you write down
the proof carefully, it relies on the fact that `|x - y| = |y - x|`
or, equivalently, that `|(-x)| = |x|`. I say "equivalently" because
`ring` will prove that `-(x - y) = y - x`.

You don't want to be proving stuff like `|x - y| = |y - x|` from first
principles. Someone else has already done all the hard work for you.
All you need to do is to learn how to find out the names of the lemmas.
The `exact?` tactic tells you the names of all these lemmas.
See where it says "try this" -- click there and Lean will replace
`exact?` with the actual name of the lemma. Once you've done
that, hover over the lemma name to see in what generality it holds.

## The `linarith` tactic

Some of the results below are bare inequalities which are too complex
to be in the library. The library contains "natural" or "standard"
results, but it doesn't contain a random inequality fact just because
it happens to be true -- the library just contains "beautiful" facts.
However `linarith` doesn't know about anything other than `=`, `≠`,
`<` and `≤`, so don't expect it to prove any results about `|x|` or
`max A B`.

Experiment with the `exact?` and `linarith` tactics below.
Try and learn something about the naming convention which Lean uses;
see if you can start beginning to guess what various lemmas should be called.

-/

example (x : ℝ) : |-x| = |x| := by exact?
-- click where it says "try this" to replace
-- `exact?` with an "exact" proof
-- Why do this? Because it's quicker!

example (x y : ℝ) : |x - y| = |y - x| := by exact?


-- Hmm. What would a theorem saying "the max is
-- less-or-equal to something iff something else
-- be called, according to Lean's naming conventions?"
example (A B C : ℕ) : max A B ≤ C ↔ A ≤ C ∧ B ≤ C := by exact?

-- abs of something less than something...
example (x y : ℝ) : |x| < y ↔ -y < x ∧ x < y := by exact?

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 2 := by linarith

-- or linarith, or guess the name...
example (a b x y : ℝ) (h1 : a < x) (h2 : b < y) : a + b < x + y := by exact?

example (ε : ℝ) (hε : 0 < ε) : 0 < ε / 3 := by linarith

-- This is too obscure for the library
example (a b c d x y : ℝ) (h1 : a + c < x) (h2 : b + d < y) : a + b + c + d < x + y := by linarith

-- note that add_lt_add doesn't work because
-- ((a+b)+c)+d and (a+c)+(b+d) are not definitionally equal
