/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/
import RingTheory.Ideal.Operations
import Topology.Algebra.Polynomial
import Topology.Bases


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

attribute [instance] Spec.isPrime

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
  by
  rw [Set.eq_empty_iff_forall_not_mem]
  intro p
  rw [mem_v, Set.univ_subset_iff]
  have mem1 : (1 : R) ∉ (p.as_ideal : Set R) := p.as_ideal.ne_top_iff_one.mp p.is_prime.ne_top
  intro r
  rw [r] at mem1 
  exact mem1 ⟨⟩

/-- R is zero locus of `∅`
-/
theorem v_empty : v (∅ : Set R) = Set.univ :=
  Set.eq_univ_iff_forall.mpr fun p x r => False.elim <| (Set.mem_empty_iff_false _).mp r

/-- union of zero loci is zero locus of pointwise product
-/
theorem v_union (s t : Set R) : v s ∪ v t = v (s * t) :=
  by
  ext p
  constructor
  · rintro (hp | hp) <;> rw [mem_v] at hp ⊢ <;> intro r hr <;> obtain ⟨a, b, ha, hb, rfl⟩ := hr
    · specialize hp ha
      exact p.as_ideal.mul_mem_right _ hp
    · specialize hp hb
      exact p.as_ideal.mul_mem_left _ hp
  · intro hp
    rw [mem_v] at hp 
    rw [Set.mem_union, mem_v, mem_v]
    contrapose! hp
    simp only [Set.not_subset_iff_exists_mem_not_mem] at hp ⊢
    obtain ⟨⟨a, ha1, ha2⟩, ⟨b, hb1, hb2⟩⟩ := hp
    exact
      ⟨_, ⟨a, b, ha1, hb1, rfl⟩, fun r =>
        (p.is_prime.mem_or_mem r).elim (fun h => ha2 h) fun h => hb2 h⟩

/-- intersection of zero loci is zero locus of union
-/
theorem v_inter {ι : Sort _} (s : ι → Set R) : (⋂ i : ι, v (s i)) = v (⋃ i, s i) :=
  by
  ext p
  constructor <;> intro hp
  · simp_rw [Set.mem_iInter, mem_v] at hp 
    rw [mem_v, Set.iUnion_subset_iff]
    assumption
  · rw [mem_v, Set.iUnion_subset_iff] at hp 
    simp_rw [Set.mem_iInter, mem_v]
    assumption

end

instance zariskiTopology : TopologicalSpace (Spec R) :=
  TopologicalSpace.ofClosed {t | ∃ s : Set R, t = v s} ⟨Set.univ, v_univ.symm⟩
    (by
      rintro _ hS
      choose a ha using hS
      rw [Set.sInter_eq_biInter]
      suffices (⋂ (i : Set (Spec R)) (h : i ∈ A), i) = ⋂ i : A, v (a i.2)
        by
        rw [this, v_inter]
        exact ⟨_, rfl⟩
      simp only [Subtype.val_eq_coe, Subtype.coe_mk, Set.iInter_coe_set]
      exact Set.iInter_congr fun s => Set.iInter_congr fun hs => ha hs)
    (by
      rintro _ ⟨s, rfl⟩ _ ⟨t, rfl⟩
      rw [v_union]
      exact ⟨s * t, rfl⟩)

/-- open sets of Zariski topology are complement of zero loci
-/
theorem zt_isOpen (s : Set (Spec R)) : IsOpen s ↔ ∃ t : Set R, s = v tᶜ :=
  by
  change (∃ _, _) ↔ _
  rw [exists_congr]
  exact fun a => by rw [eq_compl_comm, eq_comm]

section

variable {R S}

/-- Basic open sets
-/
def d (f : R) : Set (Spec R) :=
  v {f}ᶜ

theorem mem_d (f : R) (p : Spec R) : p ∈ d f ↔ f ∉ p.asIdeal := by
  constructor <;> intro hp hf <;>
      first
      | rw [d, Set.mem_compl_iff, mem_v, Set.singleton_subset_iff] at hp 
      | rw [mem_v, Set.singleton_subset_iff] at hf  <;>
    exact hp hf

theorem open_d (f : R) : IsOpen (d f) := by
  rw [d, zt_isOpen]
  exact ⟨_, rfl⟩

/-- Basic open sets form a basis
-/
theorem d_is_basis : IsTopologicalBasis (Set.range (d : R → Set (Spec R))) :=
  isTopologicalBasis_of_open_of_nhds (by rintro _ ⟨r, -, rfl⟩; exact open_d _) fun p s hp hs =>
    by
    simp only [Set.mem_range, exists_prop, exists_exists_eq_and, mem_d]
    rw [zt_isOpen] at hs 
    obtain ⟨s, rfl⟩ := hs
    rw [Set.mem_compl_iff, mem_v, Set.not_subset_iff_exists_mem_not_mem] at hp 
    obtain ⟨x, hx1, hx2⟩ := hp
    refine' ⟨x, hx2, fun y hy H => _⟩
    exact (mem_d _ _).mp hy (H hx1)

/-- Ring homomorphisms induces continuous map (contravariantly).
-/
def comap (f : R →+* S) : Spec S → Spec R := fun p => ⟨p.asIdeal.comap f, inferInstance⟩

theorem comap_asIdeal (f : R →+* S) (p : Spec S) : (comap f p).asIdeal = p.asIdeal.comap f :=
  rfl

theorem continuous_comap (f : R →+* S) : Continuous (comap f) :=
  by
  refine' D_is_basis.continuous _ _
  rintro _ ⟨r, rfl⟩
  rw [show comap f ⁻¹' d r = d (f r) by
      ext1 p
      simp only [Set.mem_preimage, mem_d, comap_asIdeal, Ideal.mem_comap]]
  exact open_d _

local notation "ℤ[X]" => Polynomial ℤ

-- every thing from this points work for a generic integral domain
/-- the point corresponding to the zero ideal.
-/
@[simps]
noncomputable def η : Spec ℤ[X] where
  asIdeal := ⊥
  IsPrime :=
    { ne_top' := by
        rw [Ideal.ne_top_iff_one, Ideal.mem_bot]
        norm_num
      mem_or_mem' := fun x y hxy =>
        by
        simp only [Ideal.mem_bot] at hxy ⊢
        rwa [mul_eq_zero] at hxy  }

/-- this is a generic point.
-/
theorem generic_η : closure {η} = (Set.univ : Set (Spec ℤ[X])) :=
  by
  rw [show closure {η} = v (η.as_ideal : Set ℤ[X])
      by
      ext
      rw [mem_v, mem_closure_iff, η_asIdeal]
      constructor
      · intro h r hr
        rw [SetLike.mem_coe, Ideal.mem_bot] at hr 
        rw [hr]
        exact Ideal.zero_mem _
      · rintro - o ho hx
        rw [zt_isOpen] at ho 
        obtain ⟨o, rfl⟩ := ho
        rw [Set.mem_compl_iff, mem_v, Set.not_subset_iff_exists_mem_not_mem] at hx 
        obtain ⟨q, hq1, hq2⟩ := hx
        by_cases q0 : q = 0
        · rw [q0] at *
          exfalso
          refine' hq2 (Ideal.zero_mem _)
        rw [show v oᶜ ∩ {η} = {η}
            by
            rw [Set.inter_eq_right, Set.singleton_subset_iff, Set.mem_compl_iff, mem_v,
              Set.not_subset_iff_exists_mem_not_mem, η_asIdeal]
            exact ⟨q, hq1, q0⟩]
        exact ⟨η, Set.mem_singleton _⟩]
  rw [η_asIdeal, Set.eq_univ_iff_forall]
  intro x
  rw [mem_v]
  intro y hy
  rw [SetLike.mem_coe, Ideal.mem_bot] at hy 
  rw [hy]
  exact Ideal.zero_mem _

/-- Generic points is unique.
-/
theorem generic_point_uniq (x : Spec ℤ[X]) (hx : closure {x} = (Set.univ : Set (Spec ℤ[X]))) :
    x = η := by
  have h : closure {x} = closure {η} := by rw [generic_η, hx]
  have H : ∀ a b : Spec ℤ[X], a.asIdeal ≤ b.asIdeal ↔ b ∈ closure {a} :=
    by
    intro a b
    constructor
    · rw [mem_closure_iff]
      intro hle o ho hb
      rw [zt_isOpen] at ho 
      obtain ⟨o, rfl⟩ := ho
      rw [Set.mem_compl_iff, mem_v, Set.not_subset_iff_exists_mem_not_mem] at hb 
      obtain ⟨q, hq1, hq2⟩ := hb
      rw [Set.inter_nonempty]
      simp_rw [Set.mem_compl_iff, mem_v, Set.not_subset_iff_exists_mem_not_mem, SetLike.mem_coe]
      exact ⟨a, ⟨q, hq1, fun h => hq2 (hle h)⟩, Set.mem_singleton _⟩
    · intro hmem p hp
      rw [mem_closure_iff] at hmem 
      contrapose! hp
      specialize hmem (d p) (open_d p) ((mem_d _ _).mpr hp)
      obtain ⟨x, hx1, hx2⟩ := hmem
      rw [Set.mem_singleton_iff] at hx2 
      rw [hx2] at *
      rwa [mem_d] at hx1 
  have Hle1 : x.as_ideal ≤ η.as_ideal := by
    rw [H, h]
    exact subset_closure (Set.mem_singleton _)
  have Hle2 : η.as_ideal ≤ x.as_ideal := by
    rw [H, ← h]
    exact subset_closure (Set.mem_singleton _)
  ext1
  exact le_antisymm Hle1 Hle2

end

