/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/
import Mathbin.Tactic.Default
import Topology.SubsetProperties
import RingTheory.Int.Basic

#align_import solutions.section10topological_stuffs.sheet2

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

theorem univ_containsArithProgression : ContainsArithProgression Set.univ := fun x _ =>
  ⟨1, le_refl _, fun _ => ⟨⟩⟩

theorem inter_containsArithProgression (s t : Set ℤ) (hs : ContainsArithProgression s)
    (ht : ContainsArithProgression t) : ContainsArithProgression (s ∩ t) :=
  by
  choose fs hfs1 hfs2 using hs
  choose ft hft1 hft2 using ht
  rintro x ⟨hx1, hx2⟩
  refine' ⟨fs _ hx1 * ft _ hx2, _, fun k => ⟨_, _⟩⟩
  · specialize hfs1 x hx1
    specialize hft1 x hx2
    have ineq := mul_le_mul hfs1 hft1 _ _
    · rwa [one_mul] at ineq 
    all_goals linarith
  · rw [mul_assoc]; apply hfs2
  · rw [mul_comm (fs _ hx1), mul_assoc]; apply hft2

theorem sUnion_containsArithProgression (s : Set (Set ℤ))
    (hs : ∀ i ∈ s, ContainsArithProgression i) : ContainsArithProgression (⋃₀ s) :=
  by
  rintro x ⟨i, hi1, hi2⟩
  obtain ⟨m, hm1, hm2⟩ := hs i hi1 x hi2
  refine' ⟨m, hm1, fun k => Set.mem_sUnion_of_mem (hm2 k) hi1⟩

instance weirdTopOnInt : TopologicalSpace ℤ
    where
  IsOpen := ContainsArithProgression
  isOpen_univ := univ_containsArithProgression
  isOpen_inter := inter_containsArithProgression
  isOpen_sUnion := sUnion_containsArithProgression

theorem isOpen_iff_weird (s : Set ℤ) : IsOpen s ↔ ContainsArithProgression s :=
  Iff.rfl

theorem nonempty_open_is_infinite (s : Set ℤ) (hs1 : IsOpen s) (hs2 : s.Nonempty) : s.Infinite :=
  by
  rw [isOpen_iff_weird] at hs1 
  cases' hs2 with x hx
  obtain ⟨m, hm1, hm2⟩ := hs1 x hx
  set f : ℤ → s := fun z => ⟨_, hm2 z⟩ with f_eq
  haveI infinite1 := Infinite.of_injective f _
  on_goal 2 =>
    rintro a b hab
    rw [f_eq, Subtype.ext_iff_val] at hab 
    dsimp only at hab 
    rwa [add_left_inj, mul_right_inj'] at hab 
    linarith
  rwa [Set.infinite_coe_iff] at infinite1 

def arithProgression (a m : ℤ) :=
  {z : ℤ | ∃ k, m * k + a = z}

theorem arithProgression_open (a m : ℤ) (hm : 1 ≤ m) : IsOpen (arithProgression a m) :=
  by
  rw [isOpen_iff_weird]
  rintro _ ⟨k, rfl⟩
  exact ⟨m, hm, fun k' => ⟨k + k', by ring⟩⟩

theorem arithProgression_closed (a m : ℤ) (hm : 1 ≤ m) : IsClosed (arithProgression a m) :=
  by
  rw [← isOpen_compl_iff, isOpen_iff_weird]
  intro x hx
  rw [arithProgression, Set.mem_compl_iff, Set.mem_setOf_eq, not_exists] at hx 
  refine' ⟨m, hm, fun k r => _⟩
  obtain ⟨k', hk'⟩ := r
  refine' hx (k' - k) _
  rw [← sub_eq_zero] at hk' ⊢
  rw [← hk']
  ring

theorem arithProgression_clopen (a m : ℤ) (hm : 1 ≤ m) : IsClopen (arithProgression a m) :=
  { left := arithProgression_open _ _ hm
    right := arithProgression_closed _ _ hm }

def PrimeInt : Type :=
  Subtype (Prime : ℤ → Prop)

theorem seteq1 : (⋃ (p : ℕ) (hp : Nat.Prime p), arithProgression 0 p)ᶜ = {1, -1} := by
  classical
  ext1 x
  constructor
  · intro hx
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists, add_zero, Set.mem_setOf_eq] at hx 
    by_cases ne0 : x = 0
    · rw [ne0] at *
      exfalso
      specialize hx 2 Nat.prime_two
      refine' hx ⟨0, by norm_num⟩
    by_contra r
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at r 
    have ineq1 : x.nat_abs ≠ 1 := by intro rid;
      rw [Int.natAbs_eq_iff, show (↑(1 : ℕ) : ℤ) = 1 from rfl] at rid ; tauto
    specialize hx x.nat_abs.min_fac (Nat.minFac_prime ineq1)
    obtain ⟨r, hr⟩ := x.nat_abs.min_fac_dvd
    rcases Int.natAbs_eq x with (hx' | hx')
    · refine' hx ⟨r, _⟩
      rw [add_zero]
      conv_rhs => rw [hx']
      exact_mod_cast hr.symm
    · refine' hx _
      refine' ⟨-r, _⟩
      replace hx' := hx'.symm
      rw [neg_eq_iff_eq_neg] at hx' 
      rw [add_zero, mul_neg, neg_eq_iff_eq_neg, ← hx']
      exact_mod_cast hr.symm
  · intro r
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at r 
    rcases r with (rfl | rfl)
    all_goals
      simp_rw [Set.mem_compl_iff, Set.mem_iUnion, arithProgression, Set.mem_setOf_eq, add_zero]
      push_neg
      intro i hi1 k r
      try rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at r 
      try rw [Int.mul_eq_neg_one_iff_eq_one_or_neg_one] at r 
      rcases r with (⟨hi, rfl⟩ | ⟨hi, rfl⟩)
      · norm_cast at hi 
        rw [hi] at hi1 
        exact Nat.not_prime_one hi1
      · have := Int.coe_nat_nonneg i; linarith

theorem not_closed : ¬IsClosed (⋃ (p : ℕ) (hp : Nat.Prime p), arithProgression 0 p) :=
  by
  rw [← is_open_compl_iff.not, seteq1]
  intro r
  have h1 := nonempty_open_is_infinite {1, -1} r ⟨1, by simp⟩
  have h2 : ({1, -1} : Set ℤ).Finite := by simp
  rw [← Set.not_infinite] at h2 
  exact h2 h1

theorem not_closed' : ¬IsClosed (⋃ p : setOf Nat.Prime, arithProgression 0 (p : ℤ)) :=
  by
  simp only [coe_coe, Set.mem_setOf_eq, Subtype.coe_mk, Set.iUnion_coe_set]
  exact not_closed

theorem infinite_prime : (setOf Nat.Prime).Infinite :=
  by
  by_contra r
  rw [Set.not_infinite] at r 
  refine' not_closed' _
  have : Finite (setOf Nat.Prime) := set.finite_coe_iff.mpr r
  refine' isClosed_iUnion_of_finite fun i => arithProgression_closed _ _ _
  norm_cast
  linarith [show (2 : ℕ) ≤ i by exact_mod_cast Nat.Prime.two_le i.2]

