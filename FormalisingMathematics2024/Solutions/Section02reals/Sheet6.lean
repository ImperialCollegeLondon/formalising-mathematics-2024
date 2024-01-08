/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics
import FormalisingMathematics2024.Solutions.Section02reals.Sheet5 -- import a bunch of previous stuff

namespace Section2sheet6Solutions

open Section2sheet3solutions Section2sheet5solutions

/-

# Harder questions

Here are some harder questions. Don't feel like you have
to do them. We've seen enough techniques to be able to do
all of these, but the truth is that we've seen a ton of stuff
in this course already, so probably you're not on top of all of
it yet, and furthermore we have not seen
some techniques which will enable you to cut corners. If you
want to become a real Lean expert then see how many of these
you can do. I will go through them all in class,
so if you like you can try some of them and then watch me
solving them.

Good luck!
-/
/-- If `a(n)` tends to `t` then `37 * a(n)` tends to `37 * t`-/
theorem tendsTo_thirtyseven_mul (a : ℕ → ℝ) (t : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ 37 * a n) (37 * t) := by
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / 37) (by linarith)
  use X
  intro n hn
  specialize hX n hn
  simp
  rw [← mul_sub, abs_mul, abs_of_nonneg] <;> linarith

/-- If `a(n)` tends to `t` and `c` is a positive constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_pos_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : 0 < c) :
    TendsTo (fun n ↦ c * a n) (c * t) := by
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / c) (div_pos hε hc)
  use X
  intro n hn
  specialize hX n hn
  simp
  rw [← mul_sub, abs_mul, abs_of_pos hc]
  exact (lt_div_iff' hc).mp hX

/-- If `a(n)` tends to `t` and `c` is a negative constant then
`c * a(n)` tends to `c * t`. -/
theorem tendsTo_neg_const_mul {a : ℕ → ℝ} {t : ℝ} (h : TendsTo a t) {c : ℝ} (hc : c < 0) :
    TendsTo (fun n ↦ c * a n) (c * t) :=
  by
  have hc' : 0 < -c := neg_pos.mpr hc
  intro ε hε
  obtain ⟨X, hX⟩ := h (ε / -c) (div_pos hε hc')
  use X
  intro n hn
  specialize hX n hn
  simp
  rw [← mul_sub, abs_mul, abs_of_neg hc]
  exact (lt_div_iff' hc').mp hX

/-- If `a(n)` tends to `t` and `c` is a constant then `c * a(n)` tends
to `c * t`. -/
theorem tendsTo_const_mul {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ c * a n) (c * t) :=
  by
  obtain hc | rfl | hc := lt_trichotomy 0 c
  · exact tendsTo_pos_const_mul h hc
  · simpa using tendsTo_const 0
  · exact tendsTo_neg_const_mul h hc

/-- If `a(n)` tends to `t` and `c` is a constant then `a(n) * c` tends
to `t * c`. -/
theorem tendsTo_mul_const {a : ℕ → ℝ} {t : ℝ} (c : ℝ) (h : TendsTo a t) :
    TendsTo (fun n ↦ a n * c) (t * c) := by simpa [mul_comm] using tendsTo_const_mul c h

-- another proof of this result, showcasing some tactics
-- which I've not covered yet.
theorem tendsTo_neg' {a : ℕ → ℝ} {t : ℝ} (ha : TendsTo a t) : TendsTo (fun n ↦ -a n) (-t) := by
  simpa using tendsTo_const_mul (-1) ha

/-- If `a(n)-b(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)` tends to `t + u`. -/
theorem tendsTo_of_tendsTo_sub {a b : ℕ → ℝ} {t u : ℝ} (h1 : TendsTo (fun n ↦ a n - b n) t)
    (h2 : TendsTo b u) : TendsTo a (t + u) := by simpa using tendsTo_add h1 h2

/-- If `a(n)` tends to `t` then `a(n)-t` tends to `0`. -/
theorem tendsTo_sub_lim_iff {a : ℕ → ℝ} {t : ℝ} : TendsTo a t ↔ TendsTo (fun n ↦ a n - t) 0 :=
  by
  constructor
  · intro h
    simpa using tendsTo_sub h (tendsTo_const t)
  · intro h
    simpa using tendsTo_add h (tendsTo_const t)

/-- If `a(n)` and `b(n)` both tend to zero, then their product tends
to zero. -/
theorem tendsTo_zero_mul_tendsTo_zero {a b : ℕ → ℝ} (ha : TendsTo a 0) (hb : TendsTo b 0) :
    TendsTo (fun n ↦ a n * b n) 0 := by
  intro ε hε
  obtain ⟨X, hX⟩ := ha ε hε
  obtain ⟨Y, hY⟩ := hb 1 zero_lt_one
  use max X Y
  intro n hn
  specialize hX n (le_of_max_le_left hn)
  specialize hY n (le_of_max_le_right hn)
  simpa [abs_mul] using mul_lt_mul'' hX hY

/-- If `a(n)` tends to `t` and `b(n)` tends to `u` then
`a(n)*b(n)` tends to `t*u`. -/
theorem tendsTo_mul (a b : ℕ → ℝ) (t u : ℝ) (ha : TendsTo a t) (hb : TendsTo b u) :
    TendsTo (fun n ↦ a n * b n) (t * u) :=
  by
  -- suffices a(n)b(n)-tu -> 0
  rw [tendsTo_sub_lim_iff] at *
  -- rewrite as (a(n)-t)*(b(n)-u)+t(b(n)-u)+(a(n)-t)u ->0
  have h : ∀ n, a n * b n - t * u = (a n - t) * (b n - u) + t * (b n - u) + (a n - t) * u := by
    intro n; ring
  simp [h]
  rw [show (0 : ℝ) = 0 + t * 0 + 0 * u by simp]
  refine' tendsTo_add (tendsTo_add _ _) _
  · exact tendsTo_zero_mul_tendsTo_zero ha hb
  · exact tendsTo_const_mul t hb
  · exact tendsTo_mul_const u ha

-- something we never used!
/-- A sequence has at most one limit. -/
theorem tendsTo_unique (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t :=
  by
  by_contra h
  wlog h2 : s < t
  · cases' Ne.lt_or_lt h with h3 h3
    · contradiction
    · apply this _ _ _ ht hs _ h3
      exact ne_comm.mp h
  set ε := t - s with hε
  have hε : 0 < ε := sub_pos.mpr h2
  obtain ⟨X, hX⟩ := hs (ε / 2) (by linarith)
  obtain ⟨Y, hY⟩ := ht (ε / 2) (by linarith)
  specialize hX (max X Y) (le_max_left X Y)
  specialize hY (max X Y) (le_max_right X Y)
  rw [abs_lt] at hX hY
  linarith

-- bonus solution: another proof of tends_to_unique inspired
-- by a comment on YT!
-- If |r|<ε for all ε>0 then r=0
theorem eq_zero_of_abs_lt_eps {r : ℝ} (h : ∀ ε > 0, |r| < ε) : r = 0 :=
  by
  -- Proof by contradiction. Say r ≠ 0.
  by_contra h2
  -- Then let ε be |r|, and we must have ε > 0.
  specialize h |r| (abs_pos.mpr h2)
  -- Deduce |r|<|r|, a contradiction.
  linarith

-- Second proof
theorem tendsTo_unique' (a : ℕ → ℝ) (s t : ℝ) (hs : TendsTo a s) (ht : TendsTo a t) : s = t :=
  by
  -- We know a - a tends to s - t because of `tendsTo_sub`
  have h := tendsTo_sub hs ht
  -- We want to prove s = t; by previous result suffices to
  -- show |t - s|<ε for all ε>0
  suffices ∀ ε > 0, |t - s| < ε by linarith [eq_zero_of_abs_lt_eps this]
  -- Let ε be positive.
  intro ε hε
  -- There exists X such that for n>=X, |a(n) - a(n) - (s - t)| < ε
  obtain ⟨X, hX⟩ := h ε hε
  specialize hX X (by rfl)
  -- and the simplifier can now reduce that to the goal |t-s|<ε.
  simpa using hX

end Section2sheet6Solutions
