/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic


/-

# Class groups

In Lean we don't talk about the class group of a number field, we talk about
the class group of its integer ring.

-/

variable (R : Type) [CommRing R] [IsDomain R]

example : Type :=
  ClassGroup R

noncomputable example : CommGroup (ClassGroup R) :=
  inferInstance

/-

So what is this group?

A *fractional ideal* of `R` is an `R`-submodule `J` of the field of fractions of `R`
such that there exists a nonzero element `a` of `R` such that `a * J ⊆ R`.

-/
open scoped nonZeroDivisors

-- to get notation R⁰ for the submonoid of nonzero divisors of R
-- (of course in this case it's just R \ {0}).
-- the fractional ideals of R
example : Type :=
  FractionalIdeal R⁰ (FractionRing R)

-- Note that (0) is a fractional ideal with this definition. So fractional ideals aren't
-- a group under multiplication, only a monoid.
example : CommMonoid (FractionalIdeal R⁰ (FractionRing R)) :=
  inferInstance

-- However the invertible fractional ideals (for a number field this is the same as the
-- nonzero fractional ideals) are a group:
example : CommGroup (FractionalIdeal R⁰ (FractionRing R))ˣ :=
  inferInstance

-- There's a group homomorphism from the units of `fraction_ring R` to the invertible
-- fractional ideals
noncomputable example : (FractionRing R)ˣ →* (FractionalIdeal R⁰ (FractionRing R))ˣ :=
  toPrincipalIdeal R _

-- And the class group of `R` is defined to be the quotient of the invertible fractional
-- ideals by the image of this map.
example :
    ClassGroup R =
      ((FractionalIdeal R⁰ (FractionRing R))ˣ ⧸ (toPrincipalIdeal R (FractionRing R)).range) :=
  rfl

-- For a general integral domain, the class group may be infinite. But the class group
-- of the integers of a number field is known by Lean to be finite.
open NumberField

noncomputable example (K : Type) [Field K] [NumberField K] :
    Fintype (ClassGroup (ringOfIntegers K)) :=
  inferInstance

-- Proved in 2021 in Lean. See https://arxiv.org/abs/2102.02600 to see how it was done.
-- My PhD student Ashvni Narayanan was one of the people involved in the proof.
