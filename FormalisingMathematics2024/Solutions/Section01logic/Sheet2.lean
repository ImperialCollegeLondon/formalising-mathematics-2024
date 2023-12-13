/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `true` and `false`

We learn about the `true` and `false` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `triv`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by triv

example : True → True := by
  intro h
  exact h

example : False → True := by
  intro h
  triv

example : False → False := by
  intro h
  exact h

example : (True → False) → False := by
  intro h
  apply h
  triv

example : False → P := by
  intro h
  exfalso
  exact h

example : True → False → True → False → True → False :=
  by
  intro h1 h2 h3 h4 h5
  exact h4

example : P → (P → False) → False := by
  intro hP h
  apply h
  assumption

example : (P → False) → P → Q := by
  intro h1 h2
  exfalso
  apply h1
  exact h2

example : (True → False) → P := by
  intro h
  exfalso
  apply h
  triv
