/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic


/-

# Prove that 19 ∣ 2^(2⁶ᵏ⁺²) + 3 for k = 0,1,2,...


This is the fifth question in Sierpinski's book "250 elementary problems
in number theory".

thoughts

if a(k)=2^(2⁶ᵏ⁺²)
then a(k+1)=2^(2⁶*2⁶ᵏ⁺²)=a(k)^64

Note that 16^64 is 16 mod 19 according to a brute force calculation
and so all of the a(k) are 16 mod 19 and we're done

-/

namespace Section15Sheet5Solutions

theorem sixteen_pow_sixtyfour_mod_nineteen : (16 : ZMod 19) ^ 64 = 16 := by rfl

example (k : ℕ) : 19 ∣ 2 ^ 2 ^ (6 * k + 2) + 3 := by
  induction' k with d hd
  · rfl
  have h : 2 ^ 2 ^ (6 * d.succ + 2) = (2 ^ 2 ^ (6 * d + 2)) ^ 64
  · rw [Nat.succ_eq_add_one]
    ring
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd, Nat.cast_add,
    add_eq_zero_iff_eq_neg] at hd ⊢
  rw [h, Nat.cast_pow, hd]
  convert sixteen_pow_sixtyfour_mod_nineteen

end Section15Sheet5Solutions
