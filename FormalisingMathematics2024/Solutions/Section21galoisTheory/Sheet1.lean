/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.FieldTheory.Subfield -- for `WayOne`
import Mathlib.FieldTheory.IsAlgClosed.Basic -- for `WayThree`
import Mathlib.RingTheory.Norm -- for norms
import Mathlib.RingTheory.Trace -- for traces

/-

# Field theory

Galois theory is the study of the symmetries of field extensions. So we have
to start with field extensions, and immediately we run into a design decision,
which took the Lean community several years to get right.

A mathematician would informally describe a field extension as a pair
of fields E ⊆ F. When pressed, they might instead concede that it is also
an injective ring homomorphism E → F of fields. So we have three possible ways
of setting things up.

-/

section WayOne

variable (F : Type) [Field F] (E : Subfield F)

-- This way, `F` is a type and `E` is a term.
end WayOne

section WayTwo

variable (E : Type) [Field E] (F : Type) [Field F] [Algebra E F]

-- The `algebra` class fixes a ring homomorphism from `E` to `F` and
-- decrees it as "canonical" -- it is the one which the typeclass inference
-- system will find.
end WayTwo

section WayThree

variable (Ω : Type) [Field Ω] [IsAlgClosed Ω] (E : Subfield Ω) (F : Subfield Ω) (h : E ≤ F)

end WayThree

/-

The problem with the first way is that it is asymmetric. It doesn't take
long to get to a point in the theory where there are three fields E ⊆ F ⊆ K.
If `E : Subfield F` then `F` is a type, so we can't also have `F : Subfield K`.

The third way -- using a "universe" Ω and having every field a subfield,
is symmetric but feels very much like we are making arbitrary
choices; one could imagine that in theory one would have to prove that various
definitions were "independent of the choice". I have seen Galois theory at Imperial
being lectured that way (with `Ω = ℂ`) and it feels to me very much like
pre-Grothendieck algebraic geometry (Weil chose a "universal domain" in his
theory, in the 1940s). It's like defining a vector space to be a subset of ℝⁿ.
However, it has been proved to work in theorem provers. In the monumental
work of Gonthier and others proving the Feit-Thompson odd-order theorem,
all finite groups were a subgroup of a universal group, all group homomorphisms
were maps from the universal group to itself sending the source subgroup
to the target subgroup and so on. This works because given any two groups `G`
and `H`, they are both a subgroup of `G × H`. However, the same trick does
not work for rings; if `A` and `B` are rings, then (at least with Lean's conventions)
there might be no ring containing `A` and `B` as subrings; `A × B` does not work,
because `A × {0}` is not a subring, as it does not contain the correct 1.

Ultimately the community chose the second way. It is symmetric (everything is
a type), but there is a problem with it, which took a while to solve. I will
come back to this in the next sheet. For now let's do some basic theory
with fields as types rather than subfields.

Let `F/E` be a field extension (note `algebra E F` means "fix a ring homomorphism `E → F`").
The map from `E` to `F` is called `algebraMap E F`.
It's not hard to prove that this map must be injective, and thus
identifies `E` with a subfield of `F`.

-/
variable (E F : Type) [Field E] [Field F] [Algebra E F]

-- Let's first prove injectivity.
example : Function.Injective (algebraMap E F) :=
  (algebraMap E F).injective

-- Can you prove it from first principles? Hint: what ideal can the kernel be?
example : Function.Injective (algebraMap E F) := by
  intro a b hab
  by_contra h
  have hzero : algebraMap E F (a - b) = 0
  · rw [RingHom.map_sub]
    simp only [hab, sub_self]
  have hnezero : a - b ≠ 0 := by rintro h2; apply h; linear_combination h2
  suffices : (0 : F) = 1; exact zero_ne_one this
  calc
    (0 : F) = algebraMap E F (a - b)⁻¹ * 0 := by rw [MulZeroClass.mul_zero]
    _ = algebraMap E F (a - b)⁻¹ * algebraMap E F (a - b) := by rw [hzero]
    _ = algebraMap E F ((a - b)⁻¹ * (a - b)) := by rw [map_mul]
    _ = algebraMap E F 1 := by rw [inv_mul_cancel hnezero]
    _ = 1 := by rw [map_one]

-- Many concepts in the basic theory of field extensions assume the
-- extension is finite. Here's how to say this.
variable [FiniteDimensional E F]

open FiniteDimensional

noncomputable section

-- Dimension of the extension
example : ℕ :=
  finrank E F

-- note: this returns 0 if the dimension is +∞ -- but it isn't
-- the norm (a monoid homomorphism)
example : F →* E :=
  Algebra.norm E

-- it's defined as the det of the endomorphism given by left multiplication by
-- the element.
example (f : F) : Algebra.norm E f = LinearMap.det (Algebra.lmul E F f) :=
  rfl

example (e : E) : Algebra.norm E (algebraMap E F e) = e ^ finrank E F :=
  Algebra.norm_algebraMap e

-- the trace (an E-linear map)
example : F →ₗ[E] E :=
  Algebra.trace E F

example (e : E) : Algebra.trace E F (algebraMap E F e) = finrank E F • e :=
  Algebra.trace_algebraMap e

-- the min poly of an element of F
example (f : F) : Polynomial E :=
  minpoly E f
