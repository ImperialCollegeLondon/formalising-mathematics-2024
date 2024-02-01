/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
-- imports all the Lean tactics
import Mathlib.MeasureTheory.MeasurableSpace.Defs
/-

# The extended nonnegative reals [0,∞]

The big dilemma when a designer is faced with "minor modifications"
of a standard type, is whether to just stick with the standard type
and make do, or whether to make a new type and then be faced with the
problem of having to make all the API for that type. Example: in measure
theory a key role is played by the "extended non-negative reals",
namely {x : ℝ | 0 ≤ x} ∪ {∞}. In Lean these are their own type,
called `ENNReal`. There is a "scope" containing standard notation
associated for this type. Let's open it.

```lean
scoped[ENNReal] notation "ℝ≥0∞" => ENNReal
scoped[ENNReal] notation "∞" => (⊤ : ENNReal)
```
-/

namespace Section13Sheet3

open scoped ENNReal

#check ENNReal
-- #print notation ℝ≥0∞
-- does not work in Lean4, but `go to definition` works like magic
#check ℝ≥0∞ -- [0,∞]
#check ∞ -- it's the ∞ in ℝ≥0∞
-- What can we do with extended non-negative reals?
variable (a b : ℝ≥0∞)

#check a + b

#check a - b -- surprising?
#check a * b -- what is 0 * ∞ then?
#check a / b

-- is 1 / 0 = 0 or ∞? In ℝ it's 0 but here there's another possibility
example : (0 : ℝ≥0∞) * ∞ = 0 := sorry

example : (1 : ℝ≥0∞) / 0 = ∞ := sorry

example (a b c : ℝ≥0∞) : (a + b) * c = a * c + b * c := sorry

end Section13Sheet3
