/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-

Note that `X ≃ Y` is not an equivalence relation, for the stupid
reason that it's not even a true-false statement! It doesn't
say "there exists a bijection from X to Y" (which would be an
equivalence relation), it is the *type* of bijections between
`X` and `Y`, and in particular it can have more than one term
(indeed we just saw two distinct terms of type `ℚ ≃ ℚ` on the
previous sheet). However we can make some equivalence-relation-y
type constructions with `≃`. Here are definitions (not theorems!)
called `Equiv.refl`, `Equiv.symm` and `Equiv.trans`.

-/
-- this is called `Equiv.refl` in `mathlib`
example (X : Type) : X ≃ X :=
  { toFun := fun x ↦ x
    invFun := fun y ↦ y
    left_inv := by
      -- got to check that `∀ x, invFun (toFun x) = x`
      intro x
      -- `dsimp` is a tactic which simplifies `(fun x ↦ f x) t` to `f t`.
      dsimp
    right_inv := by
      -- goal is definitionally `∀ y, to_fun (inv_fun y) = y`.
      intro y
      rfl }

-- now let's see you define `Equiv.symm` and `Equiv.trans`.
-- Let's start with `Equiv.symm`.
-- Note that if `e : X ≃ Y` then `e.toFun : X → Y`
-- and `e.left_inv` is a proof of `∀ x : X, e.invFun (e.toFun x) = x` etc
-- This is `Equiv.symm`. Can you fill in the proofs?
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.invFun
    -- you could write `λ x, e.inv_fun x` instead
    invFun := e.toFun
    left_inv := e.right_inv
    right_inv := e.left_inv }

-- Actually, you're not supposed to write `e.toFun` and `e.invFun`
-- directly, because `X ≃ Y` has got a coercion to `X → Y`,
-- so you can (and should) do it like this:
-- `Equiv.symm` again
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.symm
    -- that was using `equiv.symm` and dot notation
    invFun := e
    -- that was using the coercion to function
    left_inv := e.right_inv
    right_inv := e.left_inv }

-- `Equiv.trans`
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  { toFun := fun x => eYZ (eXY x)
    invFun := fun z => eXY.symm (eYZ.symm z)
    left_inv := by
      intro x
      simp
    right_inv := by
      intro z
      simp }

-- Because `Equiv.trans` is already there, we can instead just use it
-- directly:
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  Equiv.trans eXY eYZ

-- here it is again using dot notation
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  eXY.trans eYZ

-- See if you can make the following bijection using dot notation
example (A B X : Type) (eAX : A ≃ X) (eBX : B ≃ X) : A ≃ B :=
  eAX.trans eBX.symm

/-

Note that `Equiv` is *data* -- `X ≃ Y` doesn't say "`X` bijects with `Y`";
that statement is a true-false statement. A term of type `X ≃ Y`
is *explicit functions* `X → Y` and `Y → X`, together with proofs
that they're inverse bijections.

Clearly there's an equivalence relation going on *somewhere* though:
here it is.

If `A : Type` then `∃ x : A, True` is just the statement that `A`
has an element, i.e. that `A` is nonempty. It's a proposition. So this works:

-/
-- Two types `X` and `Y` satisfy `R X Y` iff there *exists*
-- a bijection `X ≃ Y`.
def R (X Y : Type) : Prop :=
  ∃ e : X ≃ Y, True

example : Equivalence R := by
  refine' ⟨_, _, _⟩
  · intro X
    exact ⟨Equiv.refl X, trivial⟩
  · rintro X Y ⟨eXY, _⟩
    exact ⟨eXY.symm, trivial⟩
  · rintro X Y Z ⟨eXY, _⟩ ⟨eYZ, _⟩
    exact ⟨eXY.trans eYZ, trivial⟩

-- Remark: the equivalence classes of `R` are called *cardinals*.
-- Remark: set theorists might be concerned about size issues here
-- (the "set of all sets" isn't a set, so R "isn't strictly speaking an
--  equivalence relation" because it's not defined on a set). The type theorists
-- know that all this is just nonsense: `R` just lives in a higher universe.
