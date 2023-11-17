/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default

#align_import section09bijections_and_isomorphisms.sheet2

namespace Section9sheet2

/-

# Constructive bijections

I'm generally quite anti-constructive mathematics; it makes stuff harder
to do in Lean whilst only providing benefits such as computational content
which I am typically not interested in (I never `#eval` stuff, I just
want to prove theorems and I don't care if the proof isn't `refl`).

But one example of where I love constructivism is `X ≃ Y`, the class
of constructive bijections from `X` to `Y`. What is a constructive
bijection? It is a function `f : X → Y` plus some more data, but here
the data is *not* just the propositional claim that `f` is bijective
(i.e. the *existence* of a two-sided inverse) -- it is the actual
data of the two-sided inverse too. 

`X ≃ Y` is notation for `equiv X Y`. This is the type of constructive
bijections from `X` to `Y`. To make a term of type `X ≃ Y` you need
to give a 4-tuple consisting of two functions `f : X → Y` and `g : Y → X`,
plus also two proofs: firstly a proof of `∀ y, f (g y) = y`, and secondly
a proof of `∀ x, g (f x) = x`.

Note that `X ≃ Y` has type `Type`, not `Prop`. It does *not* mean "there exists
a bijection from `X` to `Y`", it is the actual data of a bijection
from `X` to `Y`. 

Let's build two different bijections from ℚ to ℚ. 

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
    rfl
  right_inv q := rfl

-- same proof but in term mode
-- Now see if you can do a harder one.
def bijection2 : ℚ ≃ ℚ where
  toFun q := 3 * q + 4
  invFun r := (r - 4) / 3
  left_inv :=
    by-- start with `intro r`, then use `dsimp` to tidy up the mess
    sorry
  right_inv := by sorry

end Section9sheet2

