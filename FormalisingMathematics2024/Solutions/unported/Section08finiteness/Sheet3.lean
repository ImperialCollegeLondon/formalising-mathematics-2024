/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# Finite types

As well as finite subsets of a (possibly infinite type), Lean has a theory
of finite types. Just like finite subsets, there is a `Prop`-valued version
(the true-false statement "this type is finite") and a `Type`-valued version
("here is an explicit list of all the finitely many terms of this type").
If you want to work constructively, then use the `Type` version, and if
you just care about theorems you can use the `Prop` version.

## The Prop-valued version

If `(X : Type)` then `Finite X` is the true-false statement saying
that `X` is finite. It's a class, which means it goes in square brackets.

-/
section PropVersion

-- Let X be a finite type
variable (X : Type) [Finite X]

-- The typeclass inference system now knows that various other types are finite:
variable (Y : Type) [Finite Y]

example : Finite (X × Y) :=
  inferInstance

example : Finite (X → Y) :=
  inferInstance

-- The type `Fin n` is a structure. To make a term of this structure
-- you need to give a pair, consisting of a natural `a`, and a proof that `a < n`.
example : Fin 37 :=
  ⟨3, by linarith⟩

-- The typeclass inference system also knows that these are finite
example : Finite (Fin 37) :=
  inferInstance

end PropVersion

/-

## The Type-valued version

This is `[Fintype X]`. It's (in my opinion) harder to use, but finite sums work
for it, and they don't appear to work for `Finite`.

-/

-- Let X be a constructively finite type
variable (X : Type) [Fintype X]

example : X = X := by
  -- We're not supposed to do this, but we can take that instance `inst✝: Fintype X` apart:
  rename_i foo
  cases foo
  -- turns out that it's a term of type `Finset X` under the hood, plus a proof
  -- that everything is in it! In particular, it's not a theorem, it's data plus a theorem.
  -- That's why it lives in the `Type` universe, not the `Prop` universe.
  rfl

-- Lean knows that `Fin n` is constructively finite
example (n : ℕ) : Fintype (Fin n) :=
  inferInstance

open scoped BigOperators

-- the advantage of constructive finiteness is that the elements are internally stored
-- as a list, so you can prove this with `rfl`
example : ∑ x : Fin 10, x = 45 := by
  rfl

-- Actually I just tricked you. Can you explain this?
example : ∑ x : Fin 10, x = 25 := by
  rfl

-- Here's a better proof
example : ∑ x : Fin 10, x.val = 45 := by
  rfl

-- Take a look at the types of the 45 in those proof. Do you know how to? Do you know
-- what's going on? Hint: ℤ/10ℤ.
