/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Comp


/-

# Basic calculus

Let's figure out how to do differentiability in Lean together (because as I'm writing this
I have very little clue :-/
/-

# Basic calculus

Let's figure out how to do differentiability in Lean together (because as I'm writing this
I have very little clue :-/
section DifferentiabilityInGeneral

-- OK so this seems to be how to say a function is differentiable:
-- these variables will only live in this section
-- Let 𝕜 be a field equipped with a non-trivial norm (e.g. ℝ)
variable (𝕜 : Type) [NontriviallyNormedField 𝕜]

-- Let `E` be a 𝕜-vector space with a norm (e.g. ℝ or ℝ²)
variable (E : Type) [NormedAddCommGroup E] [NormedSpace 𝕜 E]

-- and let `F` be another one
variable (F : Type) [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- Then it makes sense to say that a function `f : E → F` is differentiable
variable (f : E → F)

-- This is the true-false statement that `f` is differentiable.
example : Prop :=
  Differentiable 𝕜 f

-- You can also ask that `f` is differentiable at `e : E`
example (e : E) : Prop :=
  DifferentiableAt 𝕜 f e

-- Here's how you say "`f` is continuously differentiable 37 times"
-- (i.e. you can differentiate f 37 times and when you're done the answer is continuous
-- but might not be differentiable)
example : Prop :=
  ContDiff 𝕜 37 f

-- Here's how you say "`f` is smooth, i.e. infinitely differentiable"
example : Prop :=
  ContDiff 𝕜 ⊤ f

-- That's `⊤` as in "the top element of a lattice" as in `+∞`, not `T` as in "the letter T".
-- Indeed, `ContDiff 𝕜` takes an element of `ℕ∞`.
end DifferentiabilityInGeneral

-- Let's now just assume `𝕜 = ℝ`; then `E` and `F` can be `ℝ` or `ℂ` or `ℝ × ℝ` or `Fin n → ℝ` (the
-- way we say `ℝⁿ` in mathlib) or ...
open Real

-- because there is `Real.cos` and `Complex.cos`,
-- This says "the cos(sin(x))*exp(x) is differentiable"
example : Differentiable ℝ fun x => cos (sin x) * exp x := by
  apply Differentiable.mul
  · exact differentiable_cos.comp differentiable_sin
  · exact differentiable_exp

-- No longer works, I don't think simplifier is picking up `Differentiable.comp`
-- Alternative approach:
-- example : Differentiable ℝ fun x => cos (sin x) * exp x := by simp?

-- Lean3 Kevin : I am less freaked out about this though.
-- simplifier is missing some lemma, so no longer works `simp; ring`
example (x : ℝ) :
    deriv (fun x => cos (sin x) * exp x) x =
    (cos (sin x) - sin (sin x) * cos x) * exp x := by
  rw [deriv_mul, Real.deriv_exp, deriv]
  rotate_left
  · exact differentiable_cos.comp differentiable_sin |>.differentiableAt
  · exact differentiable_exp |>.differentiableAt

  erw [fderiv.comp (f := sin) (g := cos) x differentiable_cos.differentiableAt
    differentiable_sin.differentiableAt]
  rw [ContinuousLinearMap.coe_comp', Function.comp_apply, fderiv_sin, fderiv_cos]
  rotate_left
  · exact differentiable_id.differentiableAt
  · exact differentiable_id.differentiableAt

  erw [fderiv_id]
  simp only [ContinuousLinearMap.id, neg_smul, fderiv_id', ContinuousLinearMap.coe_smul',
    ContinuousLinearMap.coe_mk', LinearMap.id_coe, Pi.smul_apply, id_eq, smul_eq_mul, mul_one,
    ContinuousLinearMap.neg_apply, neg_mul]
  ring

-- Try this one:
example (a : ℝ) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => exp (-(a * y ^ 2))) x := by
  change DifferentiableAt ℝ (exp ∘ _) x
  apply DifferentiableAt.comp
  · apply DifferentiableAt.exp
    apply differentiableAt_id'
  · apply DifferentiableAt.neg
    apply DifferentiableAt.mul
    · apply differentiableAt_const
    · apply DifferentiableAt.pow
      apply differentiableAt_id'

example (a : ℝ) (x : ℝ) :
    DifferentiableAt ℝ (fun y : ℝ => exp (-(a * y ^ 2))) x :=
  differentiableAt_id'.exp.comp x <|
    DifferentiableAt.neg <| (differentiableAt_const a).mul <|
      differentiableAt_id'.pow 2

-- simplifier is just not working??
-- example (a : ℝ) (x : ℝ) : DifferentiableAt ℝ (fun y : ℝ => exp (-(a * y ^ 2))) x := by simp
