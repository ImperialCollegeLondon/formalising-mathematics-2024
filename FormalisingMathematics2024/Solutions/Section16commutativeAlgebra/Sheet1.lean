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

section Section16Sheet1Solutions

open Function

example (R : Type) [CommRing R] [IsNoetherianRing R]
    (φ : R →+* R) (hφsurj : Surjective φ) :
    Injective φ := by
  -- we follow Conrad's notes.
  -- For `n` a natural number, define `Kₙ` to be the kernel of `φ ∘ φ ∘ φ ∘ ⋯ φ : R →+* R`,
  -- where we iterate `φ` `n` times. Of course in Lean `K` is a function `ℕ → ideal R`.
  let K : ℕ → Ideal R := fun n => RingHom.ker (φ ^ n)
  -- The ideals Kₙ satisfy Kₙ ⊆ Kₙ₊₁.
  have hKinc : ∀ n, K n ≤ K (n + 1)
  · -- for if x ∈ Kₙ
    intro n x hx
    -- then φⁿ(x) = 0
    simp only [K, RingHom.mem_ker] at hx ⊢
    -- so φⁿ⁺¹(x) = φ(0)=0
    apply_fun φ at hx ;
    rw [RingHom.map_zero] at hx
    -- so x ∈ Kₙ₊₁
    exact hx
  -- Hence K is a monotone function.
  have hKmono : Monotone K := monotone_nat_of_le_succ hKinc
  -- So by Noetherian-ness of `R`, there exists `n` such that `Kₙ=Kₙ₊₁=Kₙ₊₂=…`
  obtain ⟨n, hn⟩ :=
    monotone_stabilizes_iff_noetherian.2 inferInstance ⟨K, hKmono⟩
  -- It suffices to prove that every element of ker(φ) is 0
  rw [RingHom.injective_iff_ker_eq_bot, ← le_bot_iff]
  -- so say r ∈ ker(φ)
  intro r hr
  -- and let's prove r=0
  rw [Ideal.mem_bot]
  -- For all naturals m, The map φ^m is surjective
  have hφmsurj :
    ∀ m : ℕ, Surjective ((φ ^ m : R →+* R) : R → R)
  · -- (by an easy induction)
    intro m;
    induction' m with d hd
    -- (base case)
    · exact surjective_id
    -- (inductive step)
    · exact hφsurj.comp hd
  -- so r = φ^n r' for some r' ∈ R
  rcases hφmsurj n r with ⟨r', rfl⟩
  -- Thus 0 = φ(r)=φ^{n+1}(r')
  rw [RingHom.mem_ker] at hr
  change (φ ^ (n + 1) : R →+* R) r' = 0 at hr
  -- Therefore r' ∈ ker(φ^{n+1})
  rw [← RingHom.mem_ker] at hr ⊢
  change r' ∈ K (n + 1) at hr
  -- ...=ker(φ^n)
  rw [show K (n + 1) = K n from (hn (n + 1) (by linarith)).symm] at hr
  -- and hence r=φ^n(r')=0 as required
  exact hr

end Section16Sheet1Solutions
