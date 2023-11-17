/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default
import MeasureTheory.MeasurableSpace


-- imports all the Lean tactics
-- imports all the Lean tactics
/-

# Measure theory

## More on sigma algebras.

-/
/-

# Measure theory

## More on sigma algebras.

-/
-- Intersection of sigma algebras is a sigma algebra
-- Intersection of sigma algebras is a sigma algebra
-- Let 𝓐 be a family of sigma algebras on a type `X`
-- Let 𝓐 be a family of sigma algebras on a type `X`
variable (X : Type) (I : Type) (𝓐 : I → MeasurableSpace X)

-- Then their intersection is also a sigma algebra
open scoped MeasureTheory

-- to get notation `measurable_set[S] U` for "U is in the sigma algebra S"
example : MeasurableSpace X :=
  { MeasurableSet' := fun U => ∀ i : I, measurable_set[𝓐 i] U
    measurable_set_empty := by
      intro i
      apply MeasurableSet.empty
    measurable_set_compl := by
      intro s hs i
      apply MeasurableSet.compl
      apply hs
    measurable_set_iUnion := by
      intro f h i
      apply MeasurableSet.iUnion
      intro j
      apply h }

-- Lean knows that sigma algebras on X are a complete lattice
-- so you could also make it like this:
example : MeasurableSpace X :=
  ⨅ i, 𝓐 i

-- Sigma algebras are closed under countable intersection
-- Here, because there's only one sigma algebra involved,
-- I use the typeclass inference system to say "fix a canonical
-- sigma algebra on X" and just use that one throughout the question.
example (X : Type) [MeasurableSpace X] (f : ℕ → Set X) (hf : ∀ n, MeasurableSet (f n)) :
    MeasurableSet (⋂ n, f n) := by
  rw [← MeasurableSet.compl_iff]
  rw [Set.compl_iInter]
  apply MeasurableSet.iUnion
  intro b
  apply MeasurableSet.compl
  apply hf

