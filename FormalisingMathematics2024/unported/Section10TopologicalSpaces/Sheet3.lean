/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/
import RingTheory.Ideal.Operations
import Topology.Algebra.Polynomial
import Topology.Bases


namespace Section10sheet3

/-!
# Prime spectrum of a ring and its Zariski topology

This files contains the following: 
- Zariski topology on the set of all prime ideals of any ring `R`.
- a basis for Zariski topology 
- if `f : R →+* S` is a ring homomorphism, then `𝔭 ↦ f⁻¹ 𝔭` is continuous. 
- for integral domains, there is a unique generic point.
-/


open TopologicalSpace

open scoped Pointwise

universe u

variable (R S : Type u) [CommRing R] [CommRing S]

/-- `Spec R` is the set of prime ideals of `R`
-/
@[ext]
structure Spec : Type u where
  asIdeal : Ideal R
  IsPrime : as_ideal.IsPrime

attribute [instance] Spec.is_prime

-- making sure class inference knows term of `Spec R` is prime
section

variable {R}

/-- zero locus of a set `s ⊆ R` is the set of all prime ideals larger than `s`.

if `f : R`, then it defines a function `𝔭 ↦ ([f] : R ⧸ 𝔭)`.

So `V s` is exactly those primes
vanishing for all `f ∈ s`.
-/
def v (s : Set R) : Set (Spec R) :=
  {I : Spec R | s ⊆ I.asIdeal}

theorem mem_v (s : Set R) {p : Spec R} : p ∈ v s ↔ s ⊆ p.asIdeal :=
  Iff.rfl

/-- empty set is zero locus of `R`
-/
theorem v_univ : v (Set.univ : Set R) = ∅ :=
  sorry

/-- R is zero locus of `∅`
-/
theorem v_empty : v (∅ : Set R) = Set.univ :=
  sorry

/-- union of zero loci is zero locus of pointwise product
-/
theorem v_union (s t : Set R) : v s ∪ v t = v (s * t) :=
  sorry

/-- intersection of zero loci is zero locus of union
-/
theorem v_inter {ι : Sort _} (s : ι → Set R) : (⋂ i : ι, v (s i)) = v (⋃ i, s i) :=
  sorry

end

instance zariskiTopology : TopologicalSpace (Spec R) :=
  sorry

/-- open sets of Zariski topology are complement of zero loci
-/
theorem zt_isOpen (s : Set (Spec R)) : IsOpen s ↔ ∃ t : Set R, s = v tᶜ :=
  sorry

section

variable {R S}

/-- Basic open sets
-/
def d (f : R) : Set (Spec R) :=
  v {f}ᶜ

theorem mem_d (f : R) (p : Spec R) : p ∈ d f ↔ f ∉ p.asIdeal :=
  sorry

theorem open_d (f : R) : IsOpen (d f) :=
  sorry

/-- Basic open sets form a basis
-/
theorem d_is_basis : IsTopologicalBasis (Set.range (d : R → Set (Spec R))) :=
  sorry

/-- Ring homomorphisms induces continuous map (contravariantly).
-/
def comap (f : R →+* S) : Spec S → Spec R :=
  sorry

theorem comap_asIdeal (f : R →+* S) (p : Spec S) : (comap f p).asIdeal = p.asIdeal.comap f :=
  sorry

theorem continuous_comap (f : R →+* S) : Continuous (comap f) :=
  sorry

local notation "ℤ[X]" => Polynomial ℤ

-- every thing from this points work for a generic integral domain
/-- the point corresponding to the zero ideal.
-/
@[simps]
def η : Spec ℤ[X] where
  asIdeal := sorry
  IsPrime := sorry

/-- this is a generic point.
-/
theorem generic_η : closure {η} = (Set.univ : Set (Spec ℤ[X])) :=
  sorry

/-- Generic points is unique.
-/
theorem generic_point_uniq (x : Spec ℤ[X]) (hx : closure {x} = (Set.univ : Set (Spec ℤ[X]))) :
    x = η :=
  sorry

end

end Section10sheet3

