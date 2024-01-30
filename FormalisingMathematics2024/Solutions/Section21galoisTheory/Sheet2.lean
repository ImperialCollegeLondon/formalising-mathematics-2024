/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Norm -- for norms
import Mathlib.RingTheory.Trace -- for traces

/-

# Extensions of extensions

The problem with making every field a type and using `algebra` to
fix the embeddings from a smaller field to a bigger one, is that
when you have three or more extensions, you need to have a way of
saying that those maps are compatible.

On paper we might write "Let `E ⊆ F ⊆ K` be a tower of fields"
but in Lean we make each each pair into an `algebra` structure
and now we want to somehow explain that the `algebraMap` from
`E` to `F` composed with the one from `F` to `K` equals the
one from `E` to `K`. We assert this compatibility with
the `IsScalarTower E F K` typeclass. Here's the proof
that in the presence of this prop-valued hypothesis, the
diagram commutes.

-/

example (E F K : Type) [Field E] [Field F] [Field K] [Algebra E F] [Algebra F K] [Algebra E K]
    [IsScalarTower E F K] (e : E) : algebraMap E K e = algebraMap F K (algebraMap E F e) :=
  IsScalarTower.algebraMap_apply E F K e

/-

For me, what is surprising is that the definition of `IsScalarTower` is
not at all what one would expect. The idea is due to Kenny Lau (a former Imperial
undergraduate) in 2020; Eric Wieser wrote a paper on how the system works in 2021
https://arxiv.org/abs/2108.10700  (this is Eric on the Discord). Guess what the
definition is and then right click on `IsScalarTower` and jump to definition
to find out the truth (which might surprise you).

Now we have three compatible field extensions we can ask how the basic constructions
such as degree, norm and trace behave.

-/
variable (E F K : Type) [Field E] [Field F] [Field K]
variable [Algebra E F] [Algebra F K] [Algebra E K] [IsScalarTower E F K]

-- There is a mathematically correct tower law, involving cardinals:
example : Module.rank E F * Module.rank F K = Module.rank E K :=
  rank_mul_rank E F K

-- But this is a pain to use, because cardinals are not a particularly well-behaved
-- object. So let's put in a finite-dimensional hypothesis and use `finrank`.
open FiniteDimensional

-- Tower law for dimensions, natural number case.
example [FiniteDimensional E F] : finrank E F * finrank F K = finrank E K :=
  finrank_mul_finrank E F K

/- Note that if K/F is infinite-dimensional then `finrank F K = 0` as does `finrank E K`.
The same argument should apply if F/E is infinite-dimensional; this seems to be a minor
glitch in mathlib!
-/
-- Tricky exercise: look at proof of `finrank_mul_finrank` in mathlib and see if you
-- can generalise it by removing the `[FiniteDimensional E F]` condition in the case
-- where everything is a field.
example : finrank E F * finrank F K = finrank E K :=
  by
  by_cases h : FiniteDimensional E F
  · skip; apply finrank_mul_finrank
  · rw [finrank_of_infinite_dimensional h, MulZeroClass.zero_mul, finrank_of_infinite_dimensional]
    refine' mt _ _
    swap
    intro h
    apply FiniteDimensional.left E F K
    exact h

-- trace of trace is trace in a tower
example [FiniteDimensional E F] [FiniteDimensional F K] (k : K) :
    (Algebra.trace E F) ((Algebra.trace F K) k) = (Algebra.trace E K) k :=
  Algebra.trace_trace k

-- I can't find the norm version though :-/
