/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.Noetherian
-- theory of Noetherian rings

/-

# Commutative algebra

I find this quite a joy to do in Lean.

Keith Conrad has some notes on Noetherian rings here:

https://kconrad.math.uconn.edu/blurbs/ringtheory/noetherian-ring.pdf

In this section I prove some of the results which he discusses.

## Noetherian rings

A commutative ring is Noetherian if every ideal is finitely-generated.
Noetherian-ness is a very weak finiteness condition which is satisfied by
many rings which show up naturally in algebra, number theory and and geometry.
Lean has several equivalent standard criteria for being Noetherian. Let's
use one of them to prove Theorem 3.2 in Conrad's notes: a surjective
map from a Noetherian ring to itself is injective (note that this
is a ring-theoretic analogue of the set-theoretic result that a surjective
map from a finite set to itself is injective.)

-/

section Section16Sheet1

open Function

example (R : Type) [CommRing R] [IsNoetherianRing R] (φ : R →+* R) (hφsurj : Surjective φ) :
    Injective φ :=
  -- Here's the proof in Conrad's notes.
  -- For `n` a natural number, define `Kₙ` to be the kernel of `φ ∘ φ ∘ φ ∘ ⋯ φ : R →+* R`,
  -- where we iterate `φ` `n` times. Of course in Lean `K` is a function `ℕ → ideal R`.
  -- The ideals Kₙ satisfy Kₙ ⊆ Kₙ₊₁.
  -- (for if x ∈ Kₙ
  -- then φⁿ(x) = 0
  -- so φⁿ⁺¹(x) = φ(0)=0
  -- so x ∈ Kₙ₊₁)
  -- Hence K is a monotone function.
  -- So by Noetherian-ness of `R`, there exists `n` such that `Kₙ=Kₙ₊₁=Kₙ₊₂=…`
  -- It suffices to prove that every element of ker(φ) is 0
  -- so say r ∈ ker(φ)
  -- and let's prove r=0
  -- For all naturals m, The map φ^m is surjective
  -- (by an easy induction)
  -- so r = φ^n r' for some r' ∈ R
  -- Thus 0 = φ(r)=φ^{n+1}(r')
  -- Therefore r' ∈ ker(φ^{n+1})
  -- ...=ker(φ^n)
  -- and hence r=φ^n(r')=0 as required
  sorry


end Section16Sheet1
