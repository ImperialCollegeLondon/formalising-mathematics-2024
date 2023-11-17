/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/
import Topology.Bases
import Topology.MetricSpace.Basic
import Topology.Algebra.Order.Floor

#align_import solutions.section10topological_stuffs.sheet1

-- definition of topological bases
-- definition of topological bases
-- facts about intervals in ℝ
-- facts about intervals in ℝ
-- facts about floor function, fractional part function etc
-- facts about floor function, fractional part function etc
noncomputable section

/-!

# Topological Spaces in Lean

For any `X : Type`, a topology on `X` is defined as:
```
@[protect_proj] structure topological_space (α : Type u) :=
(is_open        : set α → Prop)
(is_open_univ   : is_open univ)
(is_open_inter  : ∀s t, is_open s → is_open t → is_open (s ∩ t))
(is_open_sUnion : ∀s, (∀t∈s, is_open t) → is_open (⋃₀ s))
```

In this sheet, the following can be found:
- defining several topological spaces;
- proof or disproof of some functions being continuous;
- denseness, compactness;
- homeomorphism
-/


universe u

namespace TopologicalSpace

variable (X : Type u)

/-- The discrete topology is the one the most open sets.
-/
def discrete : TopologicalSpace X where
  IsOpen _ := True
  isOpen_univ := ⟨⟩
  isOpen_inter _ _ _ _ := ⟨⟩
  isOpen_sUnion _ _ := ⟨⟩

/-- The indiscrete topology is the one with the least open sets.
-/
def indiscrete : TopologicalSpace X
    where
  IsOpen s := s = Set.univ ∨ s = ∅
  isOpen_univ := Or.intro_left _ rfl
  isOpen_inter := by rintro _ _ (rfl | rfl) (rfl | rfl) <;> simp
  isOpen_sUnion := by
    intro S h
    by_cases h' : Set.univ ∈ S
    · left
      refine' le_antisymm (fun _ _ => ⟨⟩) fun x _ => _
      rw [Set.mem_sUnion]
      refine' ⟨_, h', ⟨⟩⟩
    · right
      simp_rw [Set.eq_empty_iff_forall_not_mem, Set.mem_sUnion]
      push_neg
      rintro _ s hs
      exact (h s hs).elim (fun H => False.elim <| h' <| by rwa [H] at hs ) fun H => H.symm ▸ id

/-- `1`
`(X, discrete) ----->  (X, indiscrete)` is continuous 
-/
example : @Continuous (discrete X) (indiscrete X) id :=
  { isOpen_preimage := fun _ _ => ⟨⟩ }

/-- But is
                   `1`
`(X, indiscrete) ------> (X, discrete)` continuous?
-/
example (x y : X) (h : x ≠ y) : ¬@Continuous (indiscrete X) (discrete X) id :=
  by
  rw [continuous_def]
  push_neg
  refine' ⟨{x}, ⟨⟩, not_or_of_not (_ : _ ≠ _) fun r => set.eq_empty_iff_forall_not_mem.mp r x rfl⟩
  rw [Set.ne_univ_iff_exists_not_mem]
  refine' ⟨y, fun r' => h (set.mem_singleton_iff.mp (set.mem_preimage.mp r')).symm⟩

/-- Finite sets only have finitely many possible topology on them.
-/
instance finitelyManyTopologies [Fintype X] : Fintype (TopologicalSpace X) :=
  let i : TopologicalSpace X → Set (Set X) := fun τ => τ.IsOpen
  have inj_i : Function.Injective i := by intro τ1 τ2 h; ext1; exact h
  haveI : Fintype (Set (Set X)) := inferInstance
  Fintype.ofInjective i inj_i

/-- The upper bound is 2^2^|X|
-/
theorem card_topology_le [Fintype X] : Fintype.card (TopologicalSpace X) ≤ 2 ^ 2 ^ Fintype.card X :=
  by
  let i : TopologicalSpace X → Set (Set X) := fun τ => τ.IsOpen
  have inj_i : Function.Injective i := by intro τ1 τ2 h; ext1; exact h
  refine' le_trans (Fintype.card_le_of_injective i inj_i) _
  rw [Fintype.card_set, Fintype.card_set]

/-- `ℝ` has a basis consisted of all open intervals
-/
example : IsTopologicalBasis {I | ∃ a b : ℝ, I = Set.Ioo a b} :=
  isTopologicalBasis_of_open_of_nhds
    (by rintro _ ⟨a, b, rfl⟩; rw [Real.Ioo_eq_ball]; exact Metric.isOpen_ball) fun x s hx hs =>
    by
    rw [Metric.isOpen_iff] at hs 
    obtain ⟨ε, hε, subset1⟩ := hs x hx
    rw [Real.ball_eq_Ioo] at subset1 
    exact ⟨_, ⟨_, _, rfl⟩, ⟨show x - ε < x by linarith, by linarith⟩, subset1⟩

/-- `ℚ ⊆ ℝ` is dense
-/
theorem dense_ℚ : Dense (algebraMap ℚ ℝ '' Set.univ) :=
  by
  intro x
  rw [mem_closure_iff]
  intro v hv hx
  rw [Metric.isOpen_iff] at hv 
  specialize hv x hx
  obtain ⟨ε, hε, subset1⟩ := hv
  rw [Real.ball_eq_Ioo] at subset1 
  obtain ⟨q, hq⟩ := exists_rat_near x hε
  rw [abs_lt] at hq 
  cases hq
  refine' ⟨q, subset1 ⟨_, _⟩, ⟨_, ⟨⟩, rfl⟩⟩ <;> linarith

/-- Hence functions `ℝ → ℝ` is uniquely determined on `ℚ`.
-/
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (heq : ∀ x : ℚ, f x = g x) : f = g :=
  Continuous.ext_on dense_ℚ hf hg fun _ ⟨q, ⟨⟩, h⟩ => h ▸ HEq q

/-- An algebraic interpretation of unit circle `S¹` defined as `ℝ ⧸ ℤ` with the quotient topology,
i.e. `V ⊆ S¹` is open iff `π ⁻¹ V` is open in `ℝ` where `π : ℝ → ℝ ⧸ ℤ`.
-/
def Circle :=
  ℝ ⧸ (algebraMap ℤ ℝ).toAddMonoidHom.range
deriving TopologicalSpace, AddCommGroup, Inhabited

namespace circle

/-- π -/
def fromReal : ℝ → Circle :=
  Quotient.mk''

/-- `[0, 1) → ℝ → S¹` -/
def fromIco : Set.Ico (0 : ℝ) 1 → Circle :=
  fromReal ∘ Subtype.val

@[continuity]
theorem continuous_fromReal : Continuous fromReal :=
  ⟨fun _ => id⟩

@[continuity]
theorem continuousOn_fromReal : ContinuousOn fromReal (Set.Ico 0 1) :=
  Continuous.continuousOn ⟨fun s => id⟩

@[continuity]
theorem continuous_fromIco : Continuous fromIco :=
  by
  rw [continuous_iff_continuousOn_univ]
  refine' ContinuousOn.comp _ _ _
  · exact Set.Ico 0 1
  · exact continuous_on_from_real
  · refine' Continuous.continuousOn _; continuity
  · intro x hx; exact x.2

theorem fromIco_inj : Function.Injective fromIco :=
  by
  rintro ⟨x, hx1, hx2⟩ ⟨y, hy1, hy2⟩ h
  dsimp only [from_Ico, from_real, Function.comp_apply] at h 
  rw [Quotient.eq'', QuotientAddGroup.leftRel_eq] at h 
  obtain ⟨z, hz : ↑z = -(x : ℝ) + y⟩ := h
  rw [neg_add_eq_sub] at hz 
  have ineq1 : abs (y - x : ℝ) < 1 := by rw [abs_lt]; constructor <;> linarith
  rw [← hz] at ineq1 
  norm_cast at ineq1 
  rw [Int.abs_lt_one_iff] at ineq1 
  rw [ineq1] at hz 
  norm_cast at hz 
  replace hz := hz.symm
  rw [sub_eq_zero] at hz 
  simp_rw [hz]
  rfl

theorem fromIco_surj : Function.Surjective fromIco :=
  by
  intro x
  induction x using Quotient.inductionOn'
  dsimp only [from_Ico, from_real, Function.comp_apply]
  refine' ⟨⟨Int.fract x, Int.fract_nonneg _, Int.fract_lt_one _⟩, _⟩
  rw [Quotient.eq'']
  rw [QuotientAddGroup.leftRel_eq, neg_add_eq_sub, Int.self_sub_fract]
  exact ⟨_, rfl⟩

/-- `S¹` is compact.
-/
instance is_compact : CompactSpace Circle
    where isCompact_univ :=
    by
    rw [show Set.univ = from_real '' Set.Icc 0 1 from _]
    · exact IsCompact.image is_compact_Icc ⟨fun s h => h⟩
    symm
    rw [Set.eq_univ_iff_forall]
    intro x
    induction x using Quotient.inductionOn'
    dsimp only [from_Ico, from_real, Function.comp_apply]
    refine' ⟨Int.fract x, ⟨Int.fract_nonneg _, le_of_lt <| Int.fract_lt_one _⟩, _⟩
    rw [Quotient.eq'']
    rw [QuotientAddGroup.leftRel_eq, neg_add_eq_sub, Int.self_sub_fract]
    exact ⟨_, rfl⟩

/-- The half open interval `[0, 1)` continuously bijects to `S¹`.
-/
def equivIco : Set.Ico (0 : ℝ) 1 ≃ Circle :=
  Equiv.ofBijective fromIco ⟨fromIco_inj, fromIco_surj⟩

/-- However, its inverse is not continuous.
-/
theorem not_cont_inv : ¬Continuous equivIco.symm :=
  by
  have nc : ¬CompactSpace (Set.Ico (0 : ℝ) 1) :=
    by
    intro r
    have seteq : (Subtype.val : Set.Ico (0 : ℝ) 1 → ℝ) '' Set.univ = Set.Ico 0 1 :=
      by
      refine' Set.ext fun x => ⟨_, _⟩
      · rintro ⟨y, ⟨⟨⟩, rfl⟩⟩; exact y.2
      · rintro ⟨hx1, hx2⟩; exact ⟨⟨x, hx1, hx2⟩, ⟨⟩, rfl⟩
    have c' : IsCompact (Set.Ico (0 : ℝ) 1) := by rw [← seteq]; exact r.1.image (by continuity)
    have c'' := c'.is_closed.closure_eq
    rw [closure_Ico (by norm_num : (0 : ℝ) ≠ 1), Set.ext_iff] at c'' 
    linarith [((c'' 1).mp ⟨zero_le_one, le_refl _⟩).2]
  contrapose! nc
  let i : Homeomorph (Set.Ico (0 : ℝ) 1) circle :=
    { equiv_Ico with
      continuous_toFun := by continuity
      continuous_invFun := nc }
  exact i.symm.compact_space

end circle

end TopologicalSpace

