/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Trace
import Mathlib.RingTheory.Norm


/-

# Separable extensions

With infinite fields of characteristic `p`, weird things can happen with extensions, where
an irreducible polynomial can pick up repeated roots in an extension. A separable extension
is an extension where this pathology isn't occurring. Note that in examples like extensions
of number fields, this never happens, because number fields are characteristic zero.


-/

-- Let E ⊆ F be a field extension
variable (E F : Type) [Field E] [Field F] [Algebra E F]

section SeparableAssumption

-- Here's how you say it's separable
variable [IsSeparable E F]

-- Separable extensions are algebraic by definition in Lean
example (f : F) : IsAlgebraic E f := by
  apply IsIntegral.isAlgebraic
  -- suffices to prove f is integral over E
  apply IsSeparable.isIntegral

-- follows from separability
end SeparableAssumption

-- finite-dimensional char 0 extensions are separable
example [FiniteDimensional E F] [CharZero E] : IsSeparable E F :=
  inferInstance

-- typeclass inference can solve this as everything's a typeclass!
-- In the separable case, the minimum polynomial of `f : F` is guaranteed to have distinct roots in
-- a splitting field, and we can define traces and norms as sums or products of conjugates.
-- Let `Ω` be an algebraically closed extension of `E` (note: `Ω` doesn't have to contain `F`)
variable (Ω : Type) [Field Ω] [Algebra E Ω] [IsAlgClosed Ω]

open scoped BigOperators

example [IsSeparable E F] [FiniteDimensional E F] (f : F) :
    algebraMap E Ω (Algebra.norm E f) = ∏ σ : F →ₐ[E] Ω, σ f :=
  Algebra.norm_eq_prod_embeddings E Ω f

example [IsSeparable E F] [FiniteDimensional E F] (f : F) :
    algebraMap E Ω (Algebra.trace E F f) = ∑ σ : F →ₐ[E] Ω, σ f :=
  trace_eq_sum_embeddings Ω

-- Note the inconsistencies in both `algebra.trace/norm` inputs
-- and `trace/norm_eq_sum/prod_embeddings` inputs.
-- Now say we have a tower E ⊆ F ⊆ K
variable (K : Type) [Field K] [Algebra E K] [Algebra F K] [IsScalarTower E F K]

-- If the big extension is separable then so are the two smaller ones
example [IsSeparable E K] : IsSeparable E F :=
  isSeparable_tower_bot_of_isSeparable E F K

example [IsSeparable E K] : IsSeparable F K :=
  isSeparable_tower_top_of_isSeparable E F K

-- I can't find the claim that if F/E and K/F are separable then so is K/E. The proof I know
-- uses separable degree and I'm not sure we have that in Lean either.
