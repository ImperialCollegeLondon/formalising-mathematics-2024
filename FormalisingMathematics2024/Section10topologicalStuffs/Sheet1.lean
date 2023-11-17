/-
Copyright (c) 2023 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Jujian Zhang
-/
import Topology.Bases
import Topology.MetricSpace.Basic
import Topology.Algebra.Order.Floor

#align_import section10topological_stuffs.sheet1

-- definition of topological bases
-- definition of topological bases
-- facts about intervals in ℝ
-- facts about intervals in ℝ
-- facts about floor function, fractional part function etc
-- facts about floor function, fractional part function etc
namespace Section10sheet1

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

open TopologicalSpace

variable (X : Type u)

/-- The discrete topology is the one the most open sets.
-/
def discrete : TopologicalSpace X :=
  sorry

/-- The indiscrete topology is the one with the least open sets.
-/
def indiscrete : TopologicalSpace X :=
  sorry

/-- `1`
`(X, discrete) ----->  (X, indiscrete)` is continuous 
-/
example : @Continuous (discrete X) (indiscrete X) id :=
  sorry

/-- But is
                   `1`
`(X, indiscrete) ------> (X, discrete)` continuous?
-/
example (x y : X) (h : x ≠ y) : ¬@Continuous (indiscrete X) (discrete X) id :=
  sorry

/-- Finite sets only have finitely many possible topology on them.
-/
instance finitelyManyTopologies [Fintype X] : Fintype (TopologicalSpace X) :=
  sorry

/-- The upper bound is 2^2^|X|
-/
theorem card_topology_le [Fintype X] : Fintype.card (TopologicalSpace X) ≤ 2 ^ 2 ^ Fintype.card X :=
  sorry

/-- `ℝ` has a basis consisted of all open intervals
-/
example : IsTopologicalBasis {I | ∃ a b : ℝ, I = Set.Ioo a b} :=
  sorry

/-- `ℚ ⊆ ℝ` is dense
-/
theorem dense_ℚ : Dense (algebraMap ℚ ℝ '' Set.univ) :=
  sorry

/-- Hence functions `ℝ → ℝ` is uniquely determined on `ℚ`.
-/
example (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) (heq : ∀ x : ℚ, f x = g x) : f = g :=
  sorry

/-- An algebraic interpretation of unit circle `S¹` defined as `ℝ ⧸ ℤ` with the quotient topology,
i.e. `V ⊆ S¹` is open iff `π ⁻¹ V` is open in `ℝ` where `π : ℝ → ℝ ⧸ ℤ`.
-/
def Circle :=
  ℝ ⧸ (algebraMap ℤ ℝ).toAddMonoidHom.range
deriving TopologicalSpace, AddCommGroup, Inhabited

namespace circle

/-- π -/
def fromReal : ℝ → Circle :=
  sorry

/-- `[0, 1) → ℝ → S¹` -/
def fromIco : Set.Ico (0 : ℝ) 1 → Circle :=
  sorry

@[continuity]
theorem continuous_fromReal : Continuous fromReal :=
  sorry

@[continuity]
theorem continuousOn_fromReal : ContinuousOn fromReal (Set.Ico 0 1) :=
  sorry

@[continuity]
theorem continuous_fromIco : Continuous fromIco :=
  sorry

theorem fromIco_inj : Function.Injective fromIco :=
  sorry

theorem fromIco_surj : Function.Surjective fromIco :=
  sorry

/-- `S¹` is compact.
-/
instance is_compact : CompactSpace Circle :=
  sorry

/-- The half open interval `[0, 1)` continuously bijects to `S¹`.
-/
def equivIco : Set.Ico (0 : ℝ) 1 ≃ Circle :=
  sorry

/-- However, its inverse is not continuous.
-/
theorem not_cont_inv : ¬Continuous equivIco.symm :=
  sorry

end circle

end Section10sheet1

