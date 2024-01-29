/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Noetherian -- theory of Noetherian rings
import Mathlib.RingTheory.Polynomial.Basic

namespace Section16Sheet2solutions

/-

# Commutative algebra

More Conrad, again from

https://kconrad.math.uconn.edu/blurbs/ringtheory/noetherian-ring.pdf

Let's *start* to prove Theorem 3.6 following Conrad: if R is Noetherian then R[X] is
Noetherian.

It's not impossible, but it's also not advisable, to make a complex recursive
definition in the middle of a proof. So we factor it out and do it first.
The set-up is: R is a commutative ring and I ⊆ R[X] is an ideal which
is *not* finitely-generated. We then define a sequence fₙ of elements of R[X]
by strong recursion: fₙ is an element of smallest degree in `I - (f₀,f₁,…fₙ₋₁)`;
note that such an element must exist as `I` is not finitely-generated (and ℕ is
well-ordered).

-/
open scoped Polynomial

-- for R[X] notation
-- If I is a non-finitely-generated ideal of a commutative ring A,
-- and f₀,f₁,...,fₙ₋₁ are elements of I, then I - (f₀,f₁,…,fₙ₋₁) is nonempty
theorem lemma1 {A : Type} [CommRing A] [DecidableEq A] {I : Ideal A}
    (hInonfg : ¬I.FG) (n : ℕ) (g : ∀ m, m < n → I) :
    Set.Nonempty
      ((I : Set A) \
        Ideal.span (Finset.image (fun m : Fin n => (g m.1 m.2).1) Finset.univ :
          Set A)) := by
  rw [Set.nonempty_iff_ne_empty]
  intro h
  rw [Set.diff_eq_empty] at h
  apply hInonfg
  refine' ⟨Finset.image (fun m : Fin n => (g m.1 m.2).1) Finset.univ, _⟩
  refine' le_antisymm _ h
  rw [Ideal.span_le]
  intro a ha
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ,
    Set.mem_range] at ha
  rcases ha with ⟨y, rfl⟩
  exact (g y.1 y.2).2

theorem lemma1' {A : Type} [CommRing A] [DecidableEq A] {I : Ideal A}
    (hInonfg : ¬I.FG) (n : ℕ) (g : ∀ m, m < n → I) :
    Set.Nonempty
      {x : I |
        (x : A) ∉
        Ideal.span (Finset.image (fun m : Fin n => (g m.1 m.2).1) Finset.univ)} := by

  set S : Set A := _
  have ne1 : Set.Nonempty S := lemma1 hInonfg n g

  choose x hx using ne1
  refine ⟨⟨x, hx.1⟩, ?_⟩
  simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_diff,
    SetLike.mem_coe, Set.mem_setOf_eq] at hx ⊢
  exact hx.2

#check Function.argminOn

open scoped Classical

-- I still haven't sorted out this definition and right now I need to prepare the curves
-- and surfaces lecture :-/ Anyway, the moral of this sheet is that making complicated
-- definitions is perhaps more annoying than you might think :-/
noncomputable def f
    {R : Type} [CommRing R] {I : Ideal R[X]} [DecidableEq I]
    (hInonfg : ¬I.FG) (n : ℕ) : R[X] :=
  (Nat.strongRecOn' n fun m hm ↦
    Function.argminOn
      (Polynomial.natDegree ∘ Subtype.val : I → ℕ) wellFounded_lt
        _ <| lemma1' hInonfg m hm : I).1

end Section16Sheet2solutions
