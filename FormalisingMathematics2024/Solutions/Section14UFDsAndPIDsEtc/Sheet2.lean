/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Algebra.EuclideanDomain.Instances
import Mathlib.Data.Polynomial.FieldDivision
-- polynomial rings over a field are EDs

/-

# Euclidean Domains

Lean's definition of a Euclidean domain is more general than the usual one presented
to undergraduates. First things first: here's how to say "let R be a Euclidean domain"

-/

variable (R : Type) [EuclideanDomain R]

/-

And there's various theorems (all known by the typeclass inference system) about
Euclidean domains:

-/
example : EuclideanDomain ℤ := by infer_instance

open scoped Polynomial

-- I neither know nor care why it's noncomputable, but it doesn't matter to mathematicians
noncomputable example (k : Type) [Field k] : EuclideanDomain k[X] :=
  inferInstance

-- Euclidean domains are PIDs
example (R : Type) [EuclideanDomain R] : IsPrincipalIdealRing R :=
  inferInstance

example (R : Type) [EuclideanDomain R] : IsDomain R :=
  inferInstance

/-

Internally the definition of a Euclidean domain is this. It's a ring with the following
structure/axioms:

1) You have a "quotient" function `quotient r s` and a remainder function `remainder r s`,
both of type `R → R → R` (i.e. functions from `R²` to `R`)

2) You have an axiom saying `∀ a b, a = b * quotient a b + remainder a b`

3) You have a binary relation `≺` on the ring such that `remainder a b ≺ b`

4) You have an axiom saying that `≺` is well-founded, i.e., there are no infinite decreasing
sequences.

The point is that these axioms are enough to get Euclid's algorithm to work.

In usual maths you have a function from `R` to `ℕ` sending an element `b` to its "size",
and an axiom saying that the remainder when you divide something by `b` is sent to a smaller
natural number. In Lean the natural numbers are not involved; all that we guarantee is
that you can't keep taking remainders infinitely often, which turns out to be a very slightly
weaker statement. Let's prove that any "normal" Euclidean domain is a mathlib Euclidean domain.

-/

noncomputable example (R : Type) [CommRing R] [IsDomain R] (φ : R → ℕ)
    (h : ∀ a b : R, b ≠ 0 → ∃ q r : R, a = b * q + r ∧ (r = 0 ∨ φ r < φ b))
    (h0 : ∀ a b : R, a ≠ 0 → b ≠ 0 → φ a ≤ φ (a * b)) :
    EuclideanDomain R := by
  classical
  let φ' : R → ℕ := fun r => if r = 0 then 0 else 1 + φ r
  have h' (a b : R) : ∃ q r : R,
    a = b * q + r ∧ (b = 0 ∧ q = 0 ∧ r = a ∨ b ≠ 0 ∧ φ' r < φ' b)
  · by_cases hb : b = 0
    · refine ⟨0, a, ?_, ?_⟩ <;> aesop
    · rcases h a b hb with ⟨q, r, h1, h2⟩
      refine ⟨q, r, h1, Or.inr ⟨hb, ?_⟩⟩
      aesop
  choose quot rem h'' using h'
  exact
    { quotient := quot
      quotient_zero := by
        intro a
        rcases h'' a 0 with ⟨-, ⟨-, h1, -⟩ | ⟨h1, -⟩⟩ <;>
        aesop
      remainder := rem
      quotient_mul_add_remainder_eq := by
        intro a b
        rw [← (h'' a b).1]
      r := fun a b => φ' a < φ' b
      r_wellFounded := by
        apply InvImage.wf
        exact IsWellFounded.wf
      remainder_lt := by
        intro a b hb
        rcases h'' a b with ⟨-, ⟨h2, -⟩ | h3⟩
        · contradiction
        exact h3.2
      mul_left_not_lt := by
        intro a b hb
        push_neg
        by_cases ha : a = 0
        · simp [φ']
          subst ha
          simp
        · specialize h0 a b ha hb
          simp [φ']
          rw [if_neg ha, if_neg (by aesop)]
          linarith }
