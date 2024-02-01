/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.NumberTheory.Divisors


-- added to make Bhavik's proof work

namespace Section15sheet2Solutions

/-

# Find all integers x ≠ 3 such that x - 3 divides x³ - 3

This is the second question in Sierpinski's book "250 elementary problems
in number theory".

My solution: x - 3 divides x^3-27, and hence if it divides x^3-3
then it also divides the difference, which is 24. Conversely,
if x-3 divides 24 then because it divides x^3-27 it also divides x^3-3.
But getting Lean to find all the integers divisors of 24 is a nightmare!
Bhavik (last year) managed to figure out how to do this.

-/
-- This isn't so hard
theorem lemma1 (x : ℤ) : x - 3 ∣ x ^ 3 - 3 ↔ x - 3 ∣ 24 := by
  have h : x - 3 ∣ x ^ 3 - 27
  · use x ^ 2 + 3 * x + 9
    ring
  constructor
  · intro h1
    have h2 := dvd_sub h1 h
    convert h2
    ring
  · intro h1
    convert dvd_add h h1 using 1
    ring


theorem int_dvd_iff (x : ℤ) (n : ℤ) (hn : n ≠ 0) : x ∣ n ↔ x.natAbs ∈ n.natAbs.divisors := by
  simp [hn]

theorem lemma2 (x : ℤ) :
    x ∣ 24 ↔
    x ∈ ({-24, -12, -8, -6, -4, -3, -2, -1, 1, 2, 3, 4, 6, 8, 12, 24} : Set ℤ) :=
  by
  suffices : x ∣ 24 ↔ x.natAbs ∈ ({1, 2, 3, 4, 6, 8, 12, 24} : Finset ℕ)
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    simp only [Finset.mem_insert, Int.natAbs_eq_iff, Nat.cast_one,
      Nat.cast_ofNat, Finset.mem_singleton] at this
    tauto
  exact int_dvd_iff _ 24 (by norm_num)


-- This seems much harder :-) (it's really a computer science question, not a maths question,
-- feel free to skip)
example (x : ℤ) :
    x - 3 ∣ x ^ 3 - 3 ↔
    x ∈ ({-21, -9, -5, -3, -1, 0, 1, 2, 4, 5, 6, 7, 9, 11, 15, 27} : Set ℤ) := by
  rw [lemma1]
  rw [lemma2]
  simp only [Set.mem_insert_iff, sub_eq_neg_self, Set.mem_singleton_iff,
    sub_eq_iff_eq_add]
  norm_num

end Section15sheet2Solutions
