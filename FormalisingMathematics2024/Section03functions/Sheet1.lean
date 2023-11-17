/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default


/-!

# Functions in Lean.

In this sheet we'll learn how to manipulate the concepts of 
injectivity and surjectivity in Lean. 

The notation for functions is the usual one in mathematics:
if `X` and `Y` are types, then `f : X → Y` denotes a function
from `X` to `Y`. In fact what is going on here is that `X → Y`
denotes the type of all functions from `X` to `Y`, and `f : X → Y`
means that `f` is a term of type `X → Y`, i.e., a function
from `X` to `Y`.

One thing worth mentioning is that the simplest kind of function
evaluation, where you have `x : X` and `f : X → Y`, doesn't need
brackets: you can just write `f x` instead of `f(x)`. You only
need it when evaluating a function at a more complex object;
for example if we also had `g : Y → Z` then we can't write
`g f x` for `g(f(x))`, we have to write `g(f x)` otherwise
`g` would eat `f` and get confused. Without brackets,
a function just eats the next term greedily.

## The API we'll be using

Lean has the predicates `function.injective` and `function.surjective` on functions.
In other words, if `f : X → Y` is a function, then `function.injective f`
and `function.surjective f` are true-false statements. 

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- Typing `function.` gets old quite quickly, so let's open the function namespace
open Function

-- Now we can just write `injective f` and `surjective f`.
-- Our functions will go between these sets, or Types as Lean calls them
variable (X Y Z : Type)

-- Let's prove some theorems, each of which are true by definition.
theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by rfl

-- this proof works, because `injective f` 
-- means ∀ a b, f a = f b → a = b *by definition*
-- so the proof is "it's reflexivity of `↔`"
-- similarly this is the *definition* of `surjective f`
theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by rfl

-- similarly the *definition* of `id x` is `x`
theorem id_eval (x : X) : id x = x := by rfl

-- Function composition is `∘` in Lean (find out how to type it by putting your cursor on it). 
-- The *definition* of (g ∘ f) (x) is g(f(x)).
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by rfl

-- Why did we just prove all those theorems with a proof
-- saying "it's true by definition"? Because now, if we want,
-- we can `rw` the theorems to replace things by their definitions.
example : Injective (id : X → X) :=
  by-- you can start with `rw injective_def` if you like,
  -- and later you can `rw id_eval`, although remember that `rw` doesn't
  -- work under binders like `∀`, so use `intro` first.
  sorry

example : Surjective (id : X → X) := by sorry

-- Theorem: if f : X → Y and g : Y → Z are injective,
-- then so is g ∘ f
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) :=
  by
  -- By definition of injectivity,
  -- We need to show that if a,b are in X and
  -- (g∘f)(a)=(g∘f)(b), then a=b.
  rw [injective_def] at *
  -- so assume a and b are arbitrary elements of X, and g(f(a))=g(f(b))
  intro a b h
  -- our goal is to prove a=b.
  -- By injectivity of `f`, it suffices to prove `f a = f b`
  apply hf
  -- By injectivity of `g`, it suffices to prove g(f(a))=g(f(b))
  apply hg
  -- but this is exactly our hypothesis `h`
  exact h

-- Theorem: composite of two surjective functions
-- is surjective.
example (f : X → Y) (g : Y → Z) (hf : Surjective f) (hg : Surjective g) : Surjective (g ∘ f) :=
  by
  -- Let f:X→Y and g:Y→Z be surjective functions.
  -- By definition, we need to prove that for
  -- all z ∈ Z there exists x ∈ X such that g(f(x))=z
  rw [surjective_def]
  -- So let z ∈ Z be arbitrary
  intro z
  -- and we need to show there exists x ∈ X
  -- with g(f(x))=z
  -- Recall that g is surjective, so there
  -- must exist y ∈ Y such that g(y)=z
  have h : ∃ y, g y = z := hg z
  cases' h with y hy
  -- Recall also that f is surjective, so
  -- there exists x ∈ X such that f(x)=y
  obtain ⟨x, hx⟩ := hf y
  -- one-liner does the same thing as two-liner above
  -- I claim that this x works
  use x
  -- And indeed g(f(x))=g(y). You can just use `rw` to prove this;
  -- here is a slighly different way
  calc
    g (f x) = g y := by rw [hx]
    _ = z := by rw [hy]

-- This is a question on the IUM (Imperial introduction to proof course) function problem sheet
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f := by sorry

-- This is another one
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g := by sorry

