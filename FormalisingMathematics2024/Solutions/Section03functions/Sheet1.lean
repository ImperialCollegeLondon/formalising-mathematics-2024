/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

namespace Section3sheet1solutions

/-!

# Functions in Lean.

In this sheet we'll learn how to manipulate the concepts of
injectivity and surjectivity in Lean.

The notation for functions is the usual one in mathematics:
if `X` and `Y` are types, then `f : X → Y` denotes a function
from `X` to `Y`. In fact what is going on here is that `X → Y`
denotes the type of *all* functions from `X` to `Y` (so `X → Y`
is what mathematicians sometimes call `Hom(X,Y)`), and `f : X → Y`
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

Lean has the predicates `Function.Injective` and `Function.Surjective` on functions.
In other words, if `f : X → Y` is a function, then `Function.Injective f`
and `Function.Surjective f` are true-false statements.

-/

-- Typing `Function.` gets old quite quickly, so let's open the function namespace
open Function

-- Now we can just write `Injective f` and `Surjective f`.
-- Because of a cunning hack in Lean we can also write `f.Injective` and `f.Surjective`.

-- Our functions will go between these sets, or Types as Lean calls them
variable (X Y Z : Type)

-- Let's prove some theorems, each of which are true by definition.
theorem injective_def (f : X → Y) : Injective f ↔ ∀ a b : X, f a = f b → a = b := by
  rfl

-- this proof works, because `injective f`
-- means ∀ a b, f a = f b → a = b *by definition*
-- so the proof is "it's reflexivity of `↔`"
-- similarly this is the *definition* of `surjective f`
theorem surjective_def (f : X → Y) : Surjective f ↔ ∀ b : Y, ∃ a : X, f a = b := by
  rfl

-- similarly the *definition* of `id x` is `x`
theorem id_eval (x : X) : id x = x := by
  rfl

-- Function composition is `∘` in Lean (find out how to type it by putting your cursor on it).
-- The *definition* of (g ∘ f) (x) is g(f(x)).
theorem comp_eval (f : X → Y) (g : Y → Z) (x : X) : (g ∘ f) x = g (f x) := by
  rfl

-- Why did we just prove all those theorems with a proof
-- saying "it's true by definition"? Because now, if we want,
-- we can `rw` the theorems to replace things by their definitions.
example : Injective (id : X → X) := by
  -- this line can be deleted
  rw [injective_def]
  intro x₁ x₂ h
  -- this line can be deleted
  rw [id_eval, id_eval] at h
  exact h

example : Surjective (id : X → X) :=
  by
  -- goal is `∀ x, ...` so make progress with `intro` tactic
  intro x
  -- goal is `∃ y, ...` so make progess with `use` tactic
  use x
  -- goal is definitionally `x = x`
  rfl

-- Theorem: if f : X → Y and g : Y → Z are injective,
-- then so is g ∘ f
example (f : X → Y) (g : Y → Z) (hf : Injective f) (hg : Injective g) : Injective (g ∘ f) :=
  by
  -- By definition of injectivity,
  -- We need to show that if a,b are in X and
  -- (g∘f)(a)=(g∘f)(b), then a=b.
  rw [injective_def] at *
  -- so assume a and b are arbitrary elements of X, and let `h` be the
  -- hypothesis thst `g(f(a))=g(f(b))`
  intro a b h
  -- our goal is to prove a=b.
  -- By injectivity of `g`, we deduce from `h` that `f(a)=f(b)`
  apply hg at h
  -- By injectivity of `f`, we deduce a=b
  apply hf at h
  -- Now the goal is exactly our hypothesis `h`
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
example (f : X → Y) (g : Y → Z) : Injective (g ∘ f) → Injective f :=
  by
  -- assume gf is injective
  intro hgf
  -- say x₁, x₂ in X and assume f(x₁)=f(x₂). We want to prove x₁ = x₂
  intro x₁ x₂ h
  -- by injectivity of gf it suffices to prove g(f(x₁))=g(f(x₂))
  apply hgf
  -- goal is annoyingly `(g ∘ f) x₁ = ...` instead of `g (f x₁) = ...`
  -- But these are definitionally equal
  change g (f x₁) = g (f x₂)
  rw [h]

-- goal now true by `refl` and so `rw` closes the goal as it tries `refl`.
-- This is another one
example (f : X → Y) (g : Y → Z) : Surjective (g ∘ f) → Surjective g :=
  by
  -- assume gf is surjective
  intro hgf
  -- say z in Z
  intro z
  -- by surjectivity of gf, there's x such that gf(x)=x
  cases' hgf z with x hx
  -- we need to prove there's y in Y with g y = z; use f(x)
  use f x
  -- goal is now exactly hx
  exact hx

end Section3sheet1solutions
