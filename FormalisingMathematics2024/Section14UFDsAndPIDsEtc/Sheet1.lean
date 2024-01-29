/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.PrincipalIdealDomain
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/
variable (R : Type) [CommRing R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain.
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":
variable [IsPrincipalIdealRing R] [IsDomain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.
example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b
  apply eq_zero_or_eq_zero_of_mul_eq_zero

-- typeclass inference
-- magically extracts the assumption from `IsDomain`
example : (0 : R) ≠ 1 := sorry

example (I : Ideal R) : I.IsPrincipal := sorry

example (I : Ideal R) : ∃ j, I = Ideal.span {j} := sorry

-- product of two PIDs isn't a PID, but only becuase it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := sorry
