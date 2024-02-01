/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.MeasureTheory.Function.LpSpace
-- theory of ℒᵖ spaces
/-

# Lᵖ spaces

The set-up : `X` is a type equipped with a (sigma algebra and a) measure.

The space ℒp X
-/
open MeasureTheory

variable (X : Type) [MeasurableSpace X] (μ : Measure X)

-- Instead of functions from X to ℝ, Lean is happy to work with functions from X to
-- some arbitrary `NormedAddCommGroup`
variable (F : Type) [NormedAddCommGroup F]

-- Functions from X to F have an Lᵖ seminorm defined on them, if `p : ℝ≥0∞`
open scoped ENNReal

variable (f : X → F) (p : ℝ≥0∞)

-- the integral (∫ ‖f a‖^p ∂μ) ^ (1/p)
noncomputable example : ℝ≥0∞ :=
  snorm f p μ

-- `mem_ℒp` is the predicate saying that this integral is finite
example : Prop :=
  Memℒp f p μ

-- The reason it's called `snorm` not `norm`, is because we didn't yet quotient out by
-- the things whose integral is zero. This quotient is called `Lp`
example : Type :=
  Lp F p μ

example : AddCommGroup (Lp F p μ) := by infer_instance

-- sum of two p-integrable functions is p-integrable
-- If 1 ≤ p then it's a normed group
noncomputable example [Fact (1 ≤ p)] : NormedAddCommGroup (Lp F p μ) := by infer_instance
