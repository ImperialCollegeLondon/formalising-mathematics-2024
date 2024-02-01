/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.FieldTheory.Galois


/-

# Galois extensions

An extension is Galois if it's algebraic, normal and separable (note that both
normal and separable imply algebraic in Lean).

-/

variable (E F : Type) [Field E] [Field F] [Algebra E F] [IsGalois E F]

/-

The Galois group Gal(F/E) doesn't have special notation, it's just the F-algebra isomorphisms
from E to itself

-/
example : Type :=
  F ≃ₐ[E] F

-- It's a group
example : Group (F ≃ₐ[E] F) :=
  inferInstance

-- If F/E is furthermore finite-dimensional then its dimension is the size of the group.
open FiniteDimensional

example [FiniteDimensional E F] : Fintype.card (F ≃ₐ[E] F) = finrank E F :=
  IsGalois.card_aut_eq_finrank E F

-- The fundamental theorem of Galois theory for finite Galois extensions
-- is an order-reversing bijection between subgroups of the Galois group
-- and intermediate fields of the field extension. Here are the maps:
example : Subgroup (F ≃ₐ[E] F) → IntermediateField E F :=
  IntermediateField.fixedField

example : IntermediateField E F → Subgroup (F ≃ₐ[E] F) :=
  IntermediateField.fixingSubgroup

open IntermediateField

variable [FiniteDimensional E F]

-- They're inverse bijections
example (H : Subgroup (F ≃ₐ[E] F)) : fixingSubgroup (fixedField H) = H :=
  fixingSubgroup_fixedField H

example (L : IntermediateField E F) : fixedField (fixingSubgroup L) = L :=
  IsGalois.fixedField_fixingSubgroup L

-- weirdly, one of those is in the `IsGalois` namespace and the other isn't.
-- In the finite Galois case, this can be summarised as follows (≃o is order-preserving bijection; ᵒᵈ is "same set but reverse the order")
example : IntermediateField E F ≃o (Subgroup (F ≃ₐ[E] F))ᵒᵈ :=
  IsGalois.intermediateFieldEquivSubgroup

-- I don't know if we have the result that the subgroup `H` is normal iff the subfield `L` is normal over `E`.
-- The results described above and the techniques used to prove them are described in this 2021 paper
-- by Browning and Lutz : https://arxiv.org/abs/2107.10988
