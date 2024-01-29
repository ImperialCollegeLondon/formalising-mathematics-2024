/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.PrincipalIdealDomain
-- theory of PIDs

/-!

# Principal Ideal Domains

First let's showcase what mathlib has.

Let `R` be a commutative ring.
-/

section Section14Sheet1Solutions

variable (R : Type) [CommRing R]

-- We say `R` is a *principal ideal ring* if all ideals are principal.
-- We say `R` is a *domain* if it's an integral domain.
-- We say `R` is a *principal ideal domain* if it's both.
-- So here's how to say "Assume `R` is a PID":
variable [IsPrincipalIdealRing R] [IsDomain R]

-- Note that both of these are typeclasses, so various things should
-- be automatic.
example : ∀ a b : R, a * b = 0 → a = 0 ∨ b = 0 := by
  intro a b
  apply eq_zero_or_eq_zero_of_mul_eq_zero

-- typeclass inference
-- magically extracts the assumption from `IsDomain`
example : (0 : R) ≠ 1 := by
  -- this is another consequence of being an integral domain
  apply zero_ne_one

example (I : Ideal R) : I.IsPrincipal :=
  -- typeclass inference system finds `IsPrincipalIdealRing` and
  -- uses it automatically
  IsPrincipalIdealRing.principal I

example (I : Ideal R) : ∃ j, I = Ideal.span {j} := by
  -- to make a term of type `IsPrincipal I` you need to give one proof,
  -- but we still need to do `cases` or equivalent (I used `obtain` below)
  -- to get this proof out.
  obtain ⟨h⟩ := IsPrincipalIdealRing.principal I
  exact h

-- Typeclass inference knows a bunch of theorems about PIDs and which things are PIDs.
-- Examples:
-- integers are a PID
example : IsPrincipalIdealRing ℤ :=
  EuclideanDomain.to_principal_ideal_domain

-- just check the domain bit:
example : IsDomain ℤ := by infer_instance

-- a field is a PID
example (k : Type) [Field k] : IsPrincipalIdealRing k := by infer_instance

example (k : Type) [Field k] : IsDomain k := by infer_instance

open scoped Polynomial

-- to get `k[X]` notation instead of `polynomial k`
-- polys over a field are a PID
example (k : Type) [Field k] : IsPrincipalIdealRing k[X] := by infer_instance

example (k : Type) [Field k] : IsDomain k[X] := by infer_instance

-- if all ideals of a ring are principal then the ring is a principal ideal ring
example (A : Type) [CommRing A] (h : ∀ I : Ideal A, I.IsPrincipal) :
    IsPrincipalIdealRing A where
  principal := h

-- product of two PIDs isn't a PID, but only becuase it's not a domain
example (A B : Type) [CommRing A] [CommRing B]
    [IsPrincipalIdealRing A] [IsPrincipalIdealRing B] :
    IsPrincipalIdealRing (A × B) where
  principal I := by
    obtain ⟨a, hA : _ = Ideal.span _⟩ :=
      IsPrincipalIdealRing.principal (I.map (RingHom.fst A B))
    obtain ⟨b, hB : _ = Ideal.span _⟩ :=
      IsPrincipalIdealRing.principal (I.map (RingHom.snd A B))
    use (a, b)
    ext x
    simp only [Ideal.submodule_span_eq]
    rw [Ideal.mem_span_singleton]
    fconstructor
    · intro h
      have h1 : RingHom.fst A B x ∈ I.map (RingHom.fst A B)
      · apply Ideal.mem_map_of_mem _ h
      rw [hA, Ideal.mem_span_singleton] at h1
      rcases h1 with ⟨r, hr⟩
      have h2 : RingHom.snd A B x ∈ I.map (RingHom.snd A B)
      · apply Ideal.mem_map_of_mem _ h
      rw [hB, Ideal.mem_span_singleton] at h2
      rcases h2 with ⟨s, hs⟩
      use(r, s)
      change x = (a * r, b * s)
      rw [← hr, ← hs]
      simp only [RingHom.coe_fst, RingHom.coe_snd, Prod.mk.eta]
    · rintro ⟨⟨r, s⟩, rfl⟩
      have ha : a ∈ I.map (RingHom.fst A B) := by rw [hA, Ideal.mem_span_singleton]
      have hb : b ∈ I.map (RingHom.snd A B) := by rw [hB, Ideal.mem_span_singleton]
      rw [Ideal.mem_map_iff_of_surjective] at ha hb
      · rcases ha with ⟨⟨a, b'⟩, haI, rfl⟩
        rcases hb with ⟨⟨a', b⟩, hbI, rfl⟩
        suffices (a, b) ∈ I by exact Ideal.mul_mem_right _ _ this
        convert I.add_mem (I.mul_mem_left (1, 0) haI) (I.mul_mem_left (0, 1) hbI) <;> simp
      · intro b; use (0, b); rfl
      · intro a; use (a, 0); rfl

end Section14Sheet1Solutions
