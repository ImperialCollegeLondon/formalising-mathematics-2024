/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import NumberTheory.NumberField.ClassNumber
import RingTheory.DedekindDomain.Factorization
import Mathlib.Tactic.Default


/-

# Factorization of ideals into primes

The correct generality to set up a theory of factorization of nonzero ideals into prime
ideals is to assume that the ground ring is a Dedekind domain.

-/
/-

# Factorization of ideals into primes

The correct generality to set up a theory of factorization of nonzero ideals into prime
ideals is to assume that the ground ring is a Dedekind domain.

-/
open scoped NumberField

-- for 𝓞 K notation
-- Lean knows that the integers of a number field are a Dedekind domain
example (K : Type) [Field K] [NumberField K] : IsDedekindDomain (𝓞 K) :=
  inferInstance

-- here's how to say "let R be a Dedekind domain"
variable (R : Type) [CommRing R] [IsDomain R] [IsDedekindDomain R]

open IsDedekindDomain

/- 
There's an entire directory of files `ring_theory.dedekind_domain` containing
results about Dedekind domains. There are still a few "TODO"s though; for
example `ring_theory.dedekind_domain.dvr` contains a definition which is
known to be equivalent to Dedekind domain, but this is not yet proved in mathlib.

## Nonzero prime ideals of a Dedekind domain.

Here's the definition of `is_dedekind_domain.height_one_spectrum`:

```
structure height_one_spectrum :=
(as_ideal : ideal R)
(is_prime : as_ideal.is_prime)
(ne_bot : as_ideal ≠ ⊥)
```

It's the nonzero prime ideals of `R`. Because Dedekind domains are either fields or
1-dimensional, `height_one_spectrum R` is either empty (if `R` is a field) or
the set of maximal ideals of `R`.

A key result is that in any Dedekind domain, any nonzero ideal is contained
in only finitely many maximal ideals.

-/
example {I : Ideal R} (hI : I ≠ 0) : {v : HeightOneSpectrum R | v.asIdeal ∣ I}.Finite :=
  Ideal.finite_factors hI

-- Hence it makes sense to take a product over these factors. 
-- The theorem `ideal.finprod_height_one_spectrum_factorization`
-- says that every nonzero ideal factors into primes.
open scoped BigOperators

example (I : Ideal R) (hI : I ≠ 0) : ∏ᶠ v : HeightOneSpectrum R, v.maxPowDividing I = I :=
  Ideal.finprod_heightOneSpectrum_factorization I hI

-- Furthermore the factorization is unique
example : UniqueFactorizationMonoid (Ideal R) :=
  inferInstance

