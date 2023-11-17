/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import section01logic.sheet4

/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `split`

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by sorry

example : P ∧ Q → Q := by sorry

example : (P → Q → R) → P ∧ Q → R := by sorry

example : P → Q → P ∧ Q := by sorry

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by sorry

example : P → P ∧ True := by sorry

example : False → P ∧ False := by sorry

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by sorry

example : (P ∧ Q → R) → P → Q → R := by sorry

