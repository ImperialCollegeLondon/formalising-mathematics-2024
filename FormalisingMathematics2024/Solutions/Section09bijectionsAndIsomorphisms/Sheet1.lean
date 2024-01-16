/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic


/-

# Bijections

Like finiteness, there are two ways to say that a function is bijective in Lean.
Furthermore, you will have heard of both of them, although it may well not
have occurred to you that these two ways were particularly different. It turns
out that one of them is more constructive than the other. Let's talk about
the nonconstructive (propositional) way of talking about bijections.

Let `X` and `Y` be types, and say `f : X → Y` is a function.

-/

variable (X Y : Type) (f : X → Y)

-- The `Prop`-valued way of saying that `f` is bijective is simply
-- to say literally that `f` is bijective, i.e., injective and surjective.
example : Prop :=
  Function.Bijective f

-- Because `f` is a function type, a little Lean hack introduced recently
-- actually enables you to use dot notation for this.
example : Prop :=
  f.Bijective

-- The definition of `Function.Bijective f` is
-- `Function.Injective f ∧ Function.Surjective f`, and the definitions of
-- injective and surjective are what you think they are.
example : f.Bijective ↔ f.Injective ∧ f.Surjective := by
  rfl

example : f.Bijective ↔
    (∀ x₁ x₂ : X, f x₁ = f x₂ → x₁ = x₂) ∧ ∀ y : Y, ∃ x : X, f x = y := by
  rfl

-- It's a theorem that `f` is bijective if and only if it has a two-sided
-- inverse. One way is not hard to prove: see if you can do it. Make
-- sure you know the maths proof first! If you can't do this then
-- please ask. There's lots of little Lean tricks which make this
-- question not too bad, but there are lots of little pitfalls too.
example : (∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id) → f.Bijective :=
  by
  rintro ⟨g, hfg, hgf⟩
  constructor
  · -- injectivity
    intro a b h
    -- want to get from `g ∘ f = id` to `∀ x, g (f x) = x`.
    -- For this we need functional extensionality: two functions are equal
    -- if and only if they take the same values on all inputs.
    simp only [Function.funext_iff, Function.comp_apply, id_eq] at hgf
    -- `apply_fun` can change a hypothesis `x = y` to `g x = g y`.
    apply_fun g at h
    -- now use `hgf` to turn `h` into `a = b`, and then
    -- use `h` to close the goal
    rwa [hgf, hgf] at h -- `rwa` means `rw`, then `assumption`.
  · -- surjectivity
    intro y
    use g y
    -- pretty much the only element of x available!
    -- instead of rewrites let's use `change`
    change (f ∘ g) y = id y
    rw [hfg]

-- The other way is harder in Lean, unless you know about the `choose`
-- tactic. Given `f` and a proof that it's a bijection, how do you
-- prove the existence of a two-sided inverse `g`? You'll have to construct
-- `g`, and the `choose` tactic does this for you.
-- If `hfs` is a proof that `f` is surjective, try `choose g hg using hfs`.
example : f.Bijective → ∃ g : Y → X, f ∘ g = id ∧ g ∘ f = id := by
  -- f is injective and surjective
  rintro ⟨hfi, hfs⟩
  -- construct `g` a one-sided inverse (because `f` is surjective)
  choose g hg using hfs
  -- now you have to use `hg` to prove both f ∘ g = id and g ∘ f = id
  use g
  constructor
  · -- f ∘ g is straightforward
    ext y
    -- use functional extensionality
    exact hg y
  -- abuse of defeq
  · -- g ∘ f needs a trick
    ext x
    -- here we use injectivity
    apply hfi
    -- and here we abuse definitional equality
    exact hg (f x)
