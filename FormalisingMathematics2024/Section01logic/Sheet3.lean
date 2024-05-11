/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

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

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro h
  change True → False at h
  apply h
  triv
  done

example : False → ¬True := by
  intro h
  change True -> False
  exfalso
  exact h
  done

example : ¬False → True := by
  intro _h
  triv
  done

example : True → ¬False := by
  intro _h
  change False → False
  exfalso
  done

example : False → ¬P := by
  exfalso
  done

example : P → ¬P → False := by
  intro hP -- assume P
  intro hnP
  apply hnP
  exact hP
  done

example : P → ¬¬P := by
  intro hP
  change ¬P→False
  intro hnP
  change P→False at hnP
  apply hnP at hP
  exact hP
  done

-- another implementation using `by_contra`
example : P → ¬¬P := by
  intro hP
  by_contra hnP
  change P→False at hnP
  apply hnP at hP
  exact hP
  done

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ
  intro hnQ
  by_contra hP
  change Q→False at hnQ
  apply hPQ at hP
  apply hnQ at hP
  exact hP
  done

example : ¬¬False → False := by
  intro h
  by_contra h1
  change ¬False→False at h
  apply h at h1
  exact h1
  done

example : ¬¬P → P := by
  intro h
  by_contra h1
  change ¬P→False at h
  apply h at h1
  exact h1
  done

example : (¬Q → ¬P) → P → Q := by
  intro h
  intro h1
  by_contra h2
  apply h at h2
  change P→False at h2
  apply h2 at h1
  exact h1
  done
