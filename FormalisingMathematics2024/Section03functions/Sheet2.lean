/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

namespace Section3sheet2

/-!

# Interlude: types.

Lean uses something called "types" instead of sets, as its foundational
way of saying a "collection of stuff". For example, the real numbers
are a type in Lean, a group `G` is a type `G` equipped with a multiplication
and satisfying some axioms, and so on.

Sometimes, especially when making counterexamples, it's helpful to have a way
of making your own types. For example if I asked you to give an example
of a surjective function which wasn't injective then rather than using
Lean's inbuilt types like `ℕ` and `ℝ` you might just want to let `X={a,b}`
and `Y={c}` and define `f(a)=f(b)=c`. In this sheet we learn how to do this.

## Inductive types

There are three ways to make types in Lean. There are function types, quotient
types, and inductive types. Turns out that all types that mathematicians use
to build mathematics are made in one of these three ways. For more information
about all three kinds of types, see the course notes

https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2024/Part_B/threekindsoftypes.html

In this sheet, we will focus on inductive types, which are something like
"types for which you can list all the elements in a certain kind of way".
The definition of the type will basically be the list.

In the rest of this section, the only kinds of types you'll need to know about are
finite types, so let's start by talking about these. Let's make
a type which just has three terms.

-/


-- A type with three terms
inductive X : Type
  | a : X
  | b : X
  | c : X

-- Here `X` is a new type, with three terms whose full names are `X.a`, `X.b` and `X.c`.
-- You can think of `X` as a set, with three elements `X = {X.a, X.b, X.c}`. Typing
-- `X.` gets old very quickly so we `open X` meaning that we don't have to do this.
open X

#check a

-- works, and says `a : X`, i.e. type of `a` is `X`.
-- Given a general term `x : X`, you can do `cases x` and Lean will turn one goal into
-- three goals with this command, one for `x = a`, one for `x = b` and one for `x = c`.
example (x : X) : x = a ∨ x = b ∨ x = c := by
  cases x with
  | a => left; rfl
  | b => right; left; rfl
  | c => right; right; rfl

-- How does Lean know that `a` and `b` are *distinct* elements of `X`? If you
-- have `h : a = b` then you can do `cases h` to close any goal, because "there
-- are no cases". Lean knows deep down in its core that different constructors
-- for inductive types produce different terms
example : a ≠ b :=
  by
  -- `a ≠ b` is definitionally equal to `¬ (a = b)` which is
  -- definitionally equal to `a = b → False`. So `intro` works
  intro h
  -- `h : a = b`
  cases h

-- closes the goal.
-- We defined `X` using the `inductive` keyword and these funny `|` "pipe" symbols.
-- If you want to define a function from `X` to another type you can use `def`
-- and the `|` symbols again.
def f : X → ℕ
  | a => 37
  | b => 42
  | c => 0

example : f a = 37 := by-- true by definition
  rfl

-- Here is a proof that `f` is an injective function.
-- At some point in this proof there are 9 goals; you can see them
-- by changing the `;` after `cases y` to a `,`. The <;> means
-- "apply the next tactic to all the goals produced by the last tactic".
example : Function.Injective f := by
  intro x y h
  cases x <;> cases y -- at this point there are 9 goals, and for each goal either the conclusion
    -- is true by refl, or there's a false hypothesis `h`.
  all_goals try rfl
  -- 6 goals left
  all_goals cases h -- no cases :-)

end Section3sheet2
