/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Data.Real.Basic
import NumberTheory.NumberField.ClassNumber
import Mathlib.Tactic.Default


/-

# More on rings of integers.

Lean has a lot of commutative algebra machinery in its maths library. For example it knows
that the set of elements of a number field which are integral over ℤ form a ring; the fact
that the sum of two integral elements is integral is not obvious. Here is a high-powered
conceptual proof formalised in Lean. Note that the version in Lean's maths library of this
proof was written by an Imperial undergrad!

-/
/-

# More on rings of integers.

Lean has a lot of commutative algebra machinery in its maths library. For example it knows
that the set of elements of a number field which are integral over ℤ form a ring; the fact
that the sum of two integral elements is integral is not obvious. Here is a high-powered
conceptual proof formalised in Lean. Note that the version in Lean's maths library of this
proof was written by an Imperial undergrad!

-/
variable (K : Type) [CommRing K]

-- [number_field K] -- not actually necessary for this sheet
-- The key lemma (proved in mathlib already):
-- An element of K is integral over a subring R iff the subring ℤ[a] of K is finitely-generated
-- as a ℤ-module (i.e. as an abelian group)
theorem lemma1 (R : Type) [CommRing R] [Algebra R K] (a : K) :
    IsIntegral R a ↔ (Algebra.adjoin R ({a} : Set K)).toSubmodule.FG :=
  by
  constructor
  -- Both directions are delicate to do in Lean, but there already
  · exact FG_adjoin_singleton_of_integral a
  · intro h
    exact isIntegral_of_mem_of_FG _ h _ (Algebra.self_mem_adjoin_singleton R a)

-- One can use this lemma to prove that if `a` and `b` are integral then `R[a]` is finitely-generated
-- as an R-module, and `R[a][b]` is finitely-generated as an R[a]-module, so finitely-generated
-- as an `R`-module. If furthermore `R` is Noetherian (for example `R=ℤ` then the subalgebras `R[a+b]` and `R[ab]`
-- are finitely-generated as `R`-modules, so by the lemma applied the other way we deduce
-- that these elements are integral. This is still a hard exercise (despite the lemma)
-- because you have to move between `R` and `R[a]`.
example (a b : K) (ha : IsIntegral ℤ a) (hb : IsIntegral ℤ b) : IsIntegral ℤ (a + b) :=
  by
  rw [lemma1] at ha ⊢
  have hb' : IsIntegral (Algebra.adjoin ℤ ({a} : Set K)) b :=
    by
    apply isIntegral_of_isScalarTower hb
    · exact algebraInt ↥(Algebra.adjoin ℤ {a})
    · exact IsScalarTower.subalgebra' ℤ K K (Algebra.adjoin ℤ {a})
  rw [lemma1] at hb' 
  have foo :
    Algebra.adjoin ℤ ({a, b} : Set K) =
      (Algebra.adjoin (↥(Algebra.adjoin ℤ ({a} : Set K))) ({b} : Set K)).restrictScalars ℤ :=
    by
    apply le_antisymm
    · rw [Algebra.adjoin_le_iff, Subalgebra.coe_restrictScalars]
      rintro x (rfl | hxb)
      · simp only [SetLike.mem_coe]
        -- `mem_adjoin_of_mem` is missing??
        sorry
      · cases hxb
        simp
        -- `mem_adjoin_of_mem_base` or whatever?
        sorry
    · sorry
  -- API is missing?
  -- this is pretty messy actually :-/
  sorry

