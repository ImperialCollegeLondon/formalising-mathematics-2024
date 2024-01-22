/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

namespace Section9Sheet2
/-

# Constructive bijections

I'm generally quite anti constructive mathematics; it makes things harder
and more confusing for beginners, whilst typically only providing benefits such as
computational content which I am typically not interested in (I never `#eval` stuff,
I just want to prove theorems and I don't care if the proof isn't `rfl`).

But one example of where I love constructivism is `X ≃ Y`, the class
of constructive bijections from `X` to `Y`. What is a constructive
bijection? It is a function `f : X → Y` plus some more data, but here
the data is *not* just the propositional claim that `f` is bijective
(i.e. the *existence* of a two-sided inverse) -- it is the actual
data of the two-sided inverse too.

`X ≃ Y` is notation for `Equiv X Y`. This is the type of constructive
bijections from `X` to `Y`. To make a term of type `X ≃ Y` you need
to give a 4-tuple consisting of two functions `f : X → Y` and `g : Y → X`,
plus also two proofs: firstly a proof of `∀ y, f (g y) = y`, and secondly
a proof of `∀ x, g (f x) = x`.

Note that `X ≃ Y` has type `Type`, not `Prop`. In other words, a term
of type `X ≃ Y` is *not* a proof that there exists a bijection from `X` to `Y`,
it is the actual data of a bijection from `X` to `Y`.

Let's build two different bijections from `ℚ` to `ℚ`.

The first one is easy; I'll do it for you, to show you the syntax.

-/

def bijection1 : ℚ ≃ ℚ where
  toFun := id
  -- use the identity function from ℚ to ℚ
  invFun := id
  -- its inverse is also the identity function
  left_inv :=
    by
    -- we have to prove ∀ q, id (id q) = q
    intro q
    rfl --- works because `id q` is definitionally equal to `q`.
  -- Here's the same proof but in term mode
  right_inv q := rfl

-- Now see if you can do a harder one.
def bijection2 : ℚ ≃ ℚ where
  toFun q := 3 * q + 4
  invFun r := (r - 4) / 3
  left_inv := by
    -- start with `intro r`, then use `dsimp` to tidy up the mess
    sorry
  right_inv := by
    sorry

-- Note that these two terms are *not* equal.
example : bijection1 ≠ bijection2 := by
  -- replace `bijection1` and `bijection2` with their definitions
  unfold bijection1 bijection2
  -- assume for a contradiction that they're equal
  intro h
  -- simplify this mess
  simp at h
  -- `h` is now two false statements, let's just choose one
  cases' h with h1 _
  rw [Function.funext_iff] at h1
  -- now choose any number a such that a ≠ 3a+4
  specialize h1 37
  -- and now h1 is all about numbers so use the number tactic
  norm_num at h1

-- On the other hand, every true-false statement in Lean has at most one proof,
-- so `ℚ ≃ ℚ` can't be a true-false statement. It is in fact the set of bijections
-- from `ℚ` to itself.
