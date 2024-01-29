/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Analysis.NormedSpace.lpSpace
-- theory of ℓᵖ spaces
/-

# ℓᵖ spaces

The set-up : `I` is an index type, `E` is a family of `NormedAddCommGroup`s
(so if `i : I` then `E i` is a type and if `v : E i` then `‖v‖` makes sense and
is a real number).

Then given `p : ℝ≥0∞` (i.e. an element `p` of `[0,∞]`) there is a theory
of ℓᵖ spaces, which is the subspace of `Π i, E i` (the product) consisting of the
sections `vᵢ` such that `∑ᵢ ‖vᵢ‖ᵖ < ∞`. For `p=∞` this means "the ‖vᵢ‖ are
bounded".

-/

open scoped ENNReal

-- to get notation ℝ≥0∞
variable (I : Type) (E : I → Type) [∀ i, NormedAddCommGroup (E i)] (p : ℝ≥0∞)

-- Here's how to say that an element of the product of the Eᵢ is in the ℓᵖ space
example (v : ∀ i, E i) : Prop :=
  Memℓp v p

-- Technical note: 0^0=1 and x^0=0 for x>0, so ℓ⁰ is the functions with finite support.
variable (v : ∀ i, E i)

example : Memℓp v 0 ↔ Set.Finite {i | v i ≠ 0} :=
  memℓp_zero_iff

example : Memℓp v ∞ ↔ BddAbove (Set.range fun i => ‖v i‖) :=
  memℓp_infty_iff

-- The function ENNReal.toReal sends x<∞ to x and ∞ to 0.
-- So `0 < p.toReal` is a way of saying `0 < p < ∞`.
example (hp : 0 < p.toReal) : Memℓp v p ↔ Summable fun i => ‖v i‖ ^ p.toReal :=
  memℓp_gen_iff hp

-- It's a theorem in the library that if p ≤ q then mem_ℓp v p → mem_ℓp v q
example (q : ℝ≥0∞) (hpq : p ≤ q) : Memℓp v p → Memℓp v q :=
  by
  intro h
  exact h.of_exponent_ge hpq

-- The space of all `v` satisfying `mem_ℓp v p` is
-- called lp E p
example : Type :=
  lp E p

-- It has a norm:
noncomputable example (v : lp E p) : ℝ :=
  ‖v‖

-- It's a `NormedAddCommGroup` if `1 ≤ p` but I've not stated this correctly.
noncomputable example (h : 1 ≤ p) : NormedAddCommGroup (lp E p) := by sorry

-- `Real.IsConjugateExponent p q` means that `p,q>1` are reals and `1/p+1/q=1`
example (p q : ℝ) (hp : 1 < p) (hq : 1 < q) (hpq : 1 / p + 1 / q = 1) : p.IsConjugateExponent q :=
  sorry

-- it's a structure
-- We have a verison of Hoelder's inequality.
example (q : ℝ≥0∞)  (hpq : p.toReal.IsConjugateExponent q.toReal)
    (f : lp E p) (g : lp E q) :
    ∑' i : I, ‖f i‖ * ‖g i‖ ≤ ‖f‖ * ‖g‖ :=
  haveI := lp.tsum_mul_le_mul_norm hpq f g
  this.2

-- This would be a useless theorem if `∑' (i : I), ‖f i‖ * ‖g i‖` diverged,
-- because in Lean if a sum diverges then by definition the `∑'` of it is 0.
-- So we also need this:
example (q : ℝ≥0∞) (hpq : p.toReal.IsConjugateExponent q.toReal)
    (f : lp E p) (g : lp E q) :
    Summable fun i => ‖f i‖ * ‖g i‖ :=
  haveI := lp.tsum_mul_le_mul_norm hpq f g
  this.1
