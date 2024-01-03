/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# The real numbers in Lean

Lean has a copy of of the real numbers. It's called `real`,
but we use the usual notation `ℝ`. Put your cursor on the `ℝ` to find
out how to type it in VS Code.

In this sheet you will prove some basic equalities and inequalities
between "numerical expressions" in Lean. A numeral is something like `37`,
and a numerical expression is something like `(37 + 6) / 4`. To make
things a bit harder, I will throw in some `∃` statements. To make
progress on an `∃` goal, use the `use` tactic.

## Tactics

New tactics you'll need to know about:

* `norm_num` (proves equalities and inequalities involving numerical expressions)
* `use` (if the goal is `∃ x, x + 37 = 42` then `use 8` will change the goal
*        to `8 + 37 = 42`, and `use 10` will change it to `10 + 37 = 42`.

-/

example : (2 : ℝ) + 2 = 4 := by norm_num

example : (2 : ℝ) + 2 ≠ 5 := by norm_num

example : (2 : ℝ) + 2 < 5 := by norm_num

example : ∃ x : ℝ, 3 * x + 7 = 12 := by
  use 5 / 3
  norm_num

example : ∃ x : ℝ, 3 * x + 7 ≠ 12 := by
  use 0
  norm_num

example : ∃ x y : ℝ, 2 * x + 3 * y = 7 ∧ x + 2 * y = 4 :=
  by
  use 2, 1
  norm_num
