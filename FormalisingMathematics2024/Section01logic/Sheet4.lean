/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases'`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  sorry
  done

example : P ∧ Q → Q := by
  sorry
  done

example : (P → Q → R) → P ∧ Q → R := by
  sorry
  done

example : P → Q → P ∧ Q := by
  sorry
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  sorry
  done

example : P → P ∧ True := by
  sorry
  done

example : False → P ∧ False := by
  sorry
  done

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  sorry
  done

example : (P ∧ Q → R) → P → Q → R := by
  sorry
  done
