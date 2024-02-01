/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Defs


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
-- Indeed, `cont_diff 𝕜` takes an element of `ℕ∞`.
end DifferentiabilityInGeneral

-- Let's now just assume `𝕜 = ℝ`; then `E` and `F` can be `ℝ` or `ℂ` or `ℝ × ℝ` or `fin n → ℝ` (the
-- way we say `ℝⁿ` in mathlib) or ...
open Real

-- because there is `real.cos` and `complex.cos`,
-- This says "the cos(sin(x))*exp(x) is differentiable"
-- Hint: the theorems are called theorems like `differentiable.mul` etc.
-- Try proving it by hand.
example : Differentiable ℝ fun x => cos (sin x) * exp x := by sorry

-- Now see what `hint` has to say!
example : Differentiable ℝ fun x => cos (sin x) * exp x := by sorry

-- The simplifier used to be able to do this
example (x : ℝ) :
    deriv (fun x => cos (sin x) * exp x) x = (cos (sin x) - sin (sin x) * cos x) * exp x :=
  sorry

--by { simp, ring }
-- Try this one:
example (a : ℝ) (x : ℝ) : DifferentiableAt ℝ (fun y : ℝ => exp (-(a * y ^ 2))) x := by sorry
