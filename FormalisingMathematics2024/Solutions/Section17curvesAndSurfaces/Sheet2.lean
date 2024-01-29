/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv


namespace Section17sheet2solutions

/-

# Basic calculus

-/
-- Thanks to Moritz Doll on the Zulip for writing this one!
/-- If `f : ℝ → ℝ` is differentiable at `x`, then the obvious induced function `ℝ → ℂ` is
also differentiable at `x`. -/
theorem Complex.differentiableAt_coe {f : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (fun y => (f y : ℂ)) x := by
  apply Complex.ofRealClm.differentiableAt.comp _ hf

-- Here's a harder example
example (a : ℂ) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => Complex.exp (-(a * ↑y ^ 2))) x := by
  change DifferentiableAt ℝ (Complex.exp ∘ _) x
  apply DifferentiableAt.comp
  · apply DifferentiableAt.cexp
    apply differentiableAt_id'
  · apply DifferentiableAt.neg
    apply DifferentiableAt.mul
    · apply differentiableAt_const
    · norm_cast
      apply Complex.differentiableAt_coe
      apply DifferentiableAt.pow
      apply differentiableAt_id'

noncomputable def φ₁ : ℝ → ℝ × ℝ := fun x => (Real.cos x, Real.sin x)

example : ContDiffOn ℝ ⊤ (fun x => (Real.cos x, Real.sin x)) (Set.Icc 0 1) :=
  sorry

end Section17sheet2solutions
