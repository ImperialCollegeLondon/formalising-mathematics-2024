/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic


/-

# Basic Number Theory

Lean has enough machinery to make number theory a feasible topic for
a final project. In this section I will work through a bunch of examples,
taken from Sierpinski's old book "250 elementary problems in number theory".

## Switching between naturals and integers

Sometimes when doing number theory in Lean you find yourself having to switch
between naturals, integers and rationals. For example, if you want to do `a ^ n`
with `a` an integer, then `n` had better be a natural number, because in general
you can't raise an integer to the power of an integer. However subtraction is
"broken" on naturals:

-/

example : (2 : ℕ) - 3 = 0 :=
  rfl

-- subtraction on naturals "rounds up to 0" as it must return a natural
example : (2 : ℤ) - 3 = -1 :=
  rfl

-- subtraction on integers works correctly
/-

so sometimes you need to dance between the two. There are coercions between
all of these objects:

-/
example (n : ℕ) : ℤ :=
  n

-- works fine
example (n : ℕ) : ℤ :=
  ↑n

-- what it does under the hood
example (n : ℕ) (z : ℤ) : ℚ :=
  n + z
-- gets translated to ↑n + ↑z where the two ↑s
-- represent different functions (ℕ → ℚ and ℤ → ℚ)

/-
The big problem with this is that you end up with goals and hypotheses with `↑` in
which you want to "cancel". The `norm_cast` tactic does this.
-/
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 :=
  by
  /-
    a b : ℕ
    h : a + b = 37
    ⊢ ↑a + ↑b = 37

    exact `h` fails, because of the coercions (the goal is about the integer 37,
    not the natural 37)
    -/
  norm_cast

-- There are several shortcuts you can take here, for example
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 := by exact_mod_cast h

-- `h` is "correct modulo coercions"
example (a b : ℕ) (h : a + b = 37) : (a : ℤ) + b = 37 := by assumption_mod_cast

-- "it's an assumption, modulo coercions"
-- The `ring` tactic can't deal with the `↑`s here (it's not its job)
example (a b : ℕ) : ((a + b : ℕ) : ℤ) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  norm_cast
  -- all the ↑s are gone now
  ring

-- Another approach:
example (a b : ℕ) : ((a + b : ℕ) : ℤ) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 :=
  by
  push_cast
  -- does the "opposite" to `norm_cast`. The `norm_cast` tactic
  -- tries to pull `↑`s out as much as possible (so it changes `↑a + ↑b`
  -- to `↑(a + b)`), and then tries to cancel them. `push_cast` pushes
  -- the ↑s "inwards", i.e. as tightly up to the variables as it can.
  -- Goal is now
  -- ⊢ (↑a + ↑b) ^ 2 = ↑a ^ 2 + 2 * ↑a * ↑b + ↑b ^ 2
  ring
  -- works fine, with variables ↑a and ↑b.

/-

These `cast` tactics do not quite solve all your problems, however.
Sometimes you have statements about naturals, and you would rather
they were about integers (for example because you want to start
using subtraction). You can use the `zify` tactic to change statements
about naturals to statements about integers, and the `lift` tactic to
change statements about integers to statements about naturals. Check
out the Lean 4 documentation for these tactics if you want to know
more (I didn't cover them in the course notes):
- [`zify`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Zify.html#Mathlib.Tactic.Zify.zify)
- [`lift`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/Lift.html#Mathlib.Tactic.lift)

## For which positive integers n does n+1 divide n²+1?

This is the first question in Sierpinski's book.

Hint: n+1 divides n^2-1.

-/
example (n : ℕ) (hn : 0 < n) : n + 1 ∣ n ^ 2 + 1 ↔ n = 1 := by
  constructor
  · rintro ⟨c, hc⟩
    -- definitional abuse : `a ∣ b` is *defined* to mean `∃ c, b = a * c`
    zify at hc hn ⊢
    -- I want to work with integers
    have h1 : (n : ℤ) ^ 2 - 1 = (n + 1) * (n - 1) := by ring
    have h2 : (n : ℤ) + 1 ∣ 2 := by
      use c - (n - 1)
      linear_combination hc
    -- found with `polyrith` tactic
    have h3 : (n : ℤ) + 1 ≤ 2 := Int.le_of_dvd zero_lt_two h2
    linarith
  · rintro rfl
    norm_num
