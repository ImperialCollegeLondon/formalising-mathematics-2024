/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.FieldTheory.AbelRuffini

/-

## Insolvability of the quintic

There exist polynomials whose solutions cannot be expressed by radicals.

Let `E` be a field and assume `p : E[X]` is a polynomial
-/

open scoped Polynomial

variable (E : Type) [Field E] (p : E[X])

-- The Galois group of `p` is the Galois group of `F/E` where `F` is the splitting field of `p`.
open Polynomial

example : p.Gal = (SplittingField p ≃ₐ[E] SplittingField p) :=
  rfl

/-
If F/E is any field extension at all, then `solvableByRad E F` is the intermediate field consisting
of elements which can be built using n'th roots and the field operations, starting from `E`. Here
is the rather beautiful definition of the underlying set of this intermediate field:

```lean
inductive IsSolvableByRad : E → Prop
  | base (α : F) : IsSolvableByRad (algebraMap F E α)
  | add (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α + β)
  | neg (α : E) : IsSolvableByRad α → IsSolvableByRad (-α)
  | mul (α β : E) : IsSolvableByRad α → IsSolvableByRad β → IsSolvableByRad (α * β)
  | inv (α : E) : IsSolvableByRad α → IsSolvableByRad α⁻¹
  | rad (α : E) (n : ℕ) (hn : n ≠ 0) : IsSolvableByRad (α ^ n) → IsSolvableByRad α
```

-/
variable (F : Type) [Field F] [Algebra E F]

example : IntermediateField E F :=
  solvableByRad E F

-- The Abel-Ruffini theorem is that the min poly of an element in `IsSolvableByRad E F` has solvable Galois group
example (a : solvableByRad E F) : IsSolvable (minpoly E a).Gal :=
  solvableByRad.isSolvable a

-- This was hard won! It was only finished a year or so ago.
-- A symmetric group of size 5 or more is known not to be solvable:
example (X : Type) (hX : 5 ≤ Cardinal.mk X) : ¬IsSolvable (Equiv.Perm X) :=
  Equiv.Perm.not_solvable X hX

-- Using a root of x^5-4x+2 and the machinery in this section, Browning proves
example : ∃ x : ℂ, IsAlgebraic ℚ x ∧ ¬IsSolvableByRad ℚ x :=
  sorry

-- See the file `archive.100-theorems-list.16_abel_ruffini`.
