/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Noetherian
-- theory of Noetherian rings
import Mathlib.RingTheory.Polynomial.Basic

namespace Section16sheet2

/-

# Commutative algebra

More Conrad, again from

https://kconrad.math.uconn.edu/blurbs/ringtheory/noetherian-ring.pdf

But this time it's nasty.

Let's *start* to prove Theorem 3.6 following Conrad: if R is Noetherian then R[X] is
Noetherian.

It's not impossible, but it's messy, to make a complex recursive
definition in the middle of a proof, so we factor it out and do it first.
The set-up is: R is a commutative ring and I ⊆ R[X] is an ideal which
is *not* finitely-generated. We then define a sequence fₙ of elements of R[X]
by strong recursion: fₙ is an element of smallest degree in `I - (f₀,f₁,…fₙ₋₁)`;
note that such an element must exist as `I` is not finitely-generated (and ℕ is
well-ordered).

-/
open scoped Polynomial

-- for R[X] notation
-- Here's how Conrad's proof starts
example (R : Type) [CommRing R] [IsNoetherianRing R] :
    IsNoetherianRing R[X] := by
  -- Suffices to prove all ideals are finitely generated
  rw [isNoetherianRing_iff_ideal_fg]
  -- By contradiction. Assume `I` isn't.
  by_contra h;
  push_neg at h ; rcases h with ⟨I, hInotfg⟩
  -- Define a sequence fₙ of elements of `I` by strong recursion:
  -- fₙ is an element of smallest degree in I - (f₀,f₁,…,fₙ₋₁)
  sorry

-- we won't fill this in, let's just discuss how to define `fₙ`
-- (the proof is quite long even after this construction)
-- If I is a non-finitely-generated ideal of a commutative ring A,
-- and f₀,f₁,...,fₙ₋₁ are elements of I, then I - (f₀,f₁,…,fₙ₋₁) is nonempty
theorem lemma1 {A : Type} [CommRing A] [DecidableEq A]
    (I : Ideal A) (hInonfg : ¬I.FG) (n : ℕ) (g : ∀ m, m < n → I) :
    Set.Nonempty
      ((I : Set A) \
        Ideal.span (Finset.image (fun m : Fin n => (g m.1 m.2).1) Finset.univ :
          Set A)) :=
  sorry

-- If a subset of a set with a "ℕ-valued height function" (e.g. R[X] with `polynomial.nat_degree`)
-- is nonempty, then this is a function which returns an element with smallest height.
def smallestHeight {A : Type} (h : A → ℕ) {S : Set A} (hs : Set.Nonempty S) :
    S :=
  sorry

-- The function Conrad wants:
def f {R : Type} [CommRing R] {I : Ideal R[X]} (hInonfg : ¬I.FG) : ℕ → I :=
  sorry

end Section16sheet2
