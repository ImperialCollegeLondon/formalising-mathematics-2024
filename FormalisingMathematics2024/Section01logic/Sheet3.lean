/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default

#align_import section01logic.sheet3

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → false`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part B of the course notes:
https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_B/equality.html

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by sorry

example : False → ¬True := by sorry

example : ¬False → True := by sorry

example : True → ¬False := by sorry

example : False → ¬P := by sorry

example : P → ¬P → False := by sorry

example : P → ¬¬P := by sorry

example : (P → Q) → ¬Q → ¬P := by sorry

example : ¬¬False → False := by sorry

example : ¬¬P → P := by sorry

example : (¬Q → ¬P) → P → Q := by sorry

