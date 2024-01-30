/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.FieldTheory.Normal
import Mathlib.FieldTheory.NormalClosure


/-

# Normal extensions

Normal extensions are splitting fields. They play a role in Galois theory
because they correspond to normal subgroups via the fundamental theorem.
In Lean, normal implies algebraic.

Say F/E is an extension of fields

-/

variable (E F : Type) [Field E] [Field F] [Algebra E F]

section IsNormal

-- Say furthermore F/E is normal
variable [Normal E F]

-- Then F/E is algebraic
example (f : F) : IsAlgebraic E f :=
  Normal.isAlgebraic inferInstance f

-- and all min polys split
open Polynomial

example (f : F) : Splits (algebraMap E F) (minpoly E f) :=
  Normal.splits inferInstance f

end IsNormal

-- A finite extension is normal iff it's the splitting field of a polynomial
open scoped Polynomial

open Polynomial

example [FiniteDimensional E F] : Normal E F ↔ ∃ p : E[X], IsSplittingField E F p :=
  ⟨fun h => Normal.exists_isSplittingField E F, fun ⟨p, hp⟩ => Normal.of_isSplittingField p⟩

/-

-- This is Lean3 non-sense, no longer true in Lean4
    Note that in that proof I had to use `by exactI` which jumps into tactic mode, resets the instance
    cache (because I've just `intro`ed something which should be in it but isn't), and jumps back
    into term mode.

PS the proof of `Normal.of_isSplittingField` is a 22 line monster.

## Normal closures

Say E ⊆ F ⊆ Ω is a tower of field extensions. The normal closure of F/E in Ω is naturally a subfield of
Ω containing `F`, and there's a special structure for this: `intermediate_field F Ω`, which we'll
see in the fundamental theorem.

-/
noncomputable section

-- Say E ⊆ F ⊆ Ω
variable (Ω : Type) [Field Ω] [Algebra E Ω] [Algebra F Ω] [IsScalarTower E F Ω]

example : IntermediateField E Ω :=
  normalClosure E F Ω

-- Note that `normal_closure E F Ω` is a term (of type `intermediate_field F Ω`) but it has a coercion
-- to a type, and that type has a field structure and is normal over `E` if `Ω/E` is normal
example [Normal E Ω] : Normal E (normalClosure E F Ω) :=
  normalClosure.normal E F Ω
