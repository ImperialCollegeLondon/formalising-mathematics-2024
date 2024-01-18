/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/
import Mathlib.Tactic.Default
import Topology.SubsetProperties
import RingTheory.Int.Basic


namespace Section10sheet2

/-!
# Proof of infinitude of prime numbers using topology

This file contains an interesting proof of infinitude of prime numbers.

Define a topology on `ℤ` by declaring a set `U` is open if and only if 
for every `x ∈ U`, there exists an `1 ≤ m` such that `mk + x ∈ U` for all `k`. 

Then one can see that every nonempty open set is infinite and every arithmetic
progression `{mk + a | k ∈ ℤ}` is both open and closed where `1 ≤ m`.

Then suppose there are only finitely many prime numbers, then `⋃_p {pk | k ∈ ℤ}`
is a finite union of arithmetic progression thus closed, so its complement is open.
However, the complement of `⋃_p {pk | k ∈ ℤ}` is precisely `{-1, 1}` which cannot
be open because it is nonempty but finite.
-/


open TopologicalSpace

def ContainsArithProgression (U : Set ℤ) : Prop :=
  ∀ x : ℤ, x ∈ U → ∃ m : ℤ, 1 ≤ m ∧ ∀ k : ℤ, m * k + x ∈ U

theorem univ_containsArithProgression : ContainsArithProgression Set.univ :=
  sorry

theorem inter_containsArithProgression (s t : Set ℤ) (hs : ContainsArithProgression s)
    (ht : ContainsArithProgression t) : ContainsArithProgression (s ∩ t) :=
  sorry

theorem sUnion_containsArithProgression (s : Set (Set ℤ))
    (hs : ∀ i ∈ s, ContainsArithProgression i) : ContainsArithProgression (⋃₀ s) :=
  sorry

instance weirdTopOnInt : TopologicalSpace ℤ
    where
  IsOpen := ContainsArithProgression
  isOpen_univ := univ_containsArithProgression
  isOpen_inter := inter_containsArithProgression
  isOpen_sUnion := sUnion_containsArithProgression

theorem isOpen_iff_weird (s : Set ℤ) : IsOpen s ↔ ContainsArithProgression s :=
  Iff.rfl

theorem nonempty_open_is_infinite (s : Set ℤ) (hs1 : IsOpen s) (hs2 : s.Nonempty) : s.Infinite :=
  sorry

def arithProgression (a m : ℤ) :=
  {z : ℤ | ∃ k, m * k + a = z}

theorem arithProgression_open (a m : ℤ) (hm : 1 ≤ m) : IsOpen (arithProgression a m) :=
  sorry

theorem arithProgression_closed (a m : ℤ) (hm : 1 ≤ m) : IsClosed (arithProgression a m) :=
  sorry

theorem arithProgression_clopen (a m : ℤ) (hm : 1 ≤ m) : IsClopen (arithProgression a m) :=
  sorry

theorem seteq1 : (⋃ (p : ℕ) (hp : Nat.Prime p), arithProgression 0 p)ᶜ = {1, -1} :=
  sorry

theorem not_closed : ¬IsClosed (⋃ (p : ℕ) (hp : Nat.Prime p), arithProgression 0 p) :=
  sorry

theorem not_closed' : ¬IsClosed (⋃ p : setOf Nat.Prime, arithProgression 0 (p : ℤ)) :=
  sorry

theorem infinite_prime : (setOf Nat.Prime).Infinite :=
  sorry

end Section10sheet2

