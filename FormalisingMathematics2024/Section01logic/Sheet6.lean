/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by sorry

example : Q → P ∨ Q := by sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by sorry

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by sorry

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by sorry

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by sorry

example : (P → Q) → P ∨ R → Q ∨ R := by sorry

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by sorry

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by sorry

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by sorry

