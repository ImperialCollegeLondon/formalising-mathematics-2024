/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section15Sheet3
/-

# Prove that there exists infinitely many positive integers n such that
# 4n² + 1 is divisible both by 5 and 13.

This is the third question in Sierpinski's book "250 elementary problems
in number theory".

Maths proof: if n=4 then 4n^2+1=65 is divisible by both 5 and 13
so if n is congruent to 4 mod 5 and mod 13 (i.e if n=4+65*t)
then this will work.

There are various ways to formalise the statement that some set
of naturals is infinite. We suggest two here (although proving
they're the same is fiddly)

-/

-- The number-theoretic heart of the argument.
-- Note that "divides" is `\|` not `|`
theorem divides_of_cong_four (t : ℕ) :
    5 ∣ 4 * (65 * t + 4) ^ 2 + 1 ∧ 13 ∣ 4 * (65 * t + 4) ^ 2 + 1 := sorry

-- There are arbitrarily large solutions to `5 ∣ 4*n²+1 ∧ 13 ∣ 4*n²+1`
theorem arb_large_soln :
    ∀ N : ℕ, ∃ n > N, 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1 := sorry

#check Set.Infinite

-- This is not number theory any more, it's switching between two
-- interpretations of "this set of naturals is infinite"
theorem infinite_iff_arb_large (S : Set ℕ) :
    S.Infinite ↔ ∀ N, ∃ n > N, n ∈ S := sorry

-- Another way of stating the question (note different "|" symbols:
-- there's `|` for "such that" in set theory and `\|` for "divides" in number theory)
theorem infinite_setOf_solutions :
    {n : ℕ | 5 ∣ 4 * n ^ 2 + 1 ∧ 13 ∣ 4 * n ^ 2 + 1}.Infinite := by
  rw [infinite_iff_arb_large]
  exact arb_large_soln

end Section15Sheet3
