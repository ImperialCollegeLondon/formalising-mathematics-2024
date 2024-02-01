/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.MeasureTheory.MeasurableSpace.Defs

/-

# Measure theory

## More on sigma algebras.

-/

namespace Section13Sheet2
-- Intersection of sigma algebras is a sigma algebra
-- Let 𝓐 be a family of sigma algebras on a type `X`
variable (X : Type) (I : Type) (𝓐 : I → MeasurableSpace X)

-- Then their intersection is also a sigma algebra
open scoped MeasureTheory
-- to get notation `MeasurableSet[S] U` for "U is in the sigma algebra S"

example : MeasurableSpace X where
  MeasurableSet' U := ∀ i, MeasurableSet[𝓐 i] U
  measurableSet_empty := sorry
  measurableSet_compl := sorry
  measurableSet_iUnion := sorry

-- Lean knows that sigma algebras on X are a complete lattice
-- so you could also make it like this:
example : MeasurableSpace X :=
  ⨅ i, 𝓐 i

-- Sigma algebras are closed under countable intersection
-- Here, because there's only one sigma algebra involved,
-- I use the typeclass inference system to say "fix a canonical
-- sigma algebra on X" and just use that one throughout the question.
example (X : Type) [MeasurableSpace X]
    (f : ℕ → Set X) (hf : ∀ n, MeasurableSet (f n)) :
    MeasurableSet (⋂ n, f n) := sorry

end Section13Sheet2
