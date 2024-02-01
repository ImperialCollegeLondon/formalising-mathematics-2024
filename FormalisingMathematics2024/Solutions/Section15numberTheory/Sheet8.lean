/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Algebra
import Mathlib.NumberTheory.Wilson

namespace Section15Sheet7Solutions

open scoped BigOperators

theorem factorial_eq_prod (n : ℕ) : n.factorial = ∏ i in Finset.Icc 1 n, i :=
  by
  induction' n with d hd
  · rfl
  · rw [Nat.factorial_succ, hd]
    rw [Finset.Icc_eq_cons_Ico (show 1 ≤ d + 1 by linarith)]
    rw [Finset.prod_cons]
    congr

theorem wilson_theorem {p n : ℕ} (hp : Nat.Prime p) (hn : p = 4 * n + 1) :
    ∏ j : ℕ in Finset.Icc 1 (4 * n), (j : ZMod p) = -1 := by
  have := (Nat.prime_iff_fac_equiv_neg_one (?_ : p ≠ 1)).1 hp
  · rw [← this, hn]
    norm_cast
    congr
    simp
    rw [factorial_eq_prod, Nat.cast_prod]
    -- Somehow `norm_cast` forget to pick up `Nat.cast_prod`
  · exact Nat.Prime.ne_one hp

theorem exists_sqrt_neg_one_of_one_mod_four
    (p : ℕ) (hp : p.Prime) (hp2 : ∃ n, p = 4 * n + 1) :
    ∃ i : ZMod p, i ^ 2 = -1 := by
  cases' hp2 with n hn
  set i := ∏ j in Finset.Icc 1 (2 * n), (j : ZMod p) with hi
  have h1 : ∏ j in Finset.Icc 1 (2 * n), (-1 : ZMod p) = 1
  · rw [Finset.prod_const]
    simp only [Nat.add_succ_sub_one, add_zero, Nat.card_Icc]
    rw [pow_mul, neg_one_pow_two, one_pow]
  have h2 : ∏ j in Finset.Icc 1 (2 * n), (-j : ZMod p) = i
  · conv_lhs => rhs; ext; rw [neg_eq_neg_one_mul]
    rw [Finset.prod_mul_distrib, h1, one_mul]
  have h3 : ∏ j in Finset.Icc (2 * n + 1) (4 * n), (j : ZMod p) = i
  · rw [← h2]
    apply Finset.prod_bij' (fun j _ => p - j) (fun j _ => p - j)  <;>
    rintro a ha <;>
    rw [Finset.mem_Icc] at *
    rotate_right
    suffices : a + (p - a) = p
    · rw [eq_neg_iff_add_eq_zero]
      norm_cast
      simp [this]
    all_goals omega
  use i
  rw [pow_two]
  nth_rw 1 [hi]
  rw [← h3]
  rw [← Finset.prod_union]
  · convert_to ∏ j in Finset.Icc 1 (4 * n), (j : ZMod p) = -1
    · congr
      ext x
      rw [Finset.mem_union]
      simp only [Finset.mem_Icc]
      constructor <;>
      · intros
        omega
    · apply wilson_theorem hp hn
  · rw [disjoint_iff_inf_le]
    rintro x (hx : x ∈ _ ∩ _)
    rw [Finset.mem_inter, Finset.mem_Icc, Finset.mem_Icc] at hx
    rcases hx with ⟨⟨_, _⟩, _, _⟩
    linarith

end Section15Sheet7Solutions
