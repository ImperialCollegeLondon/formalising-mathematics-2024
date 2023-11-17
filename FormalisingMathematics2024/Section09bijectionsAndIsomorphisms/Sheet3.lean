/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default


-- imports all the Lean tactics
-- imports all the Lean tactics
namespace Section9sheet3

/-

Note that `X ≃ Y` is not an equivalence relation, for the stupid
reason that it's not even a true-false statement! It doesn't
say "there exists a bijection from X to Y" (which would be an
equivalence relation), it is the *type* of bijections between
`X` and `Y`, and in particular it can have more than one term
(indeed we just saw two distinct terms of type `ℚ ≃ ℚ` on the
previous sheet). However we can make some equivalence-relation-y
type constructions with `≃`. Here are definitions (not theorems!)
called `equiv.refl`, `equiv.symm` and `equiv.trans`.

-/
-- this is called `equiv.refl` in `mathlib`
example (X : Type) : X ≃ X :=
  { toFun := fun x => x
    -- x ↦ x
    invFun := fun y => y
    -- y ↦ y
    left_inv := by sorry
    right_inv := by sorry }

-- now let's see you define `equiv.symm` and `equiv.trans`.
-- Let's start with `equiv.symm`.
-- Note that if `e : X ≃ Y` then `e.to_fun : X → Y`
-- and `e.left_inv` is a proof of `∀ x : X, e.inv_fun (e.to_fun x) = x` etc
-- This is `equiv.symm`. Can you fill in the proofs?
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.invFun
    -- you could write `λ x, e.inv_fun x` instead
    invFun := e.toFun
    -- this is data -- don't use tactic mode
    left_inv := by sorry
    right_inv := by sorry }

-- Actually, you're not supposed to write `e.to_fun` and `e.inv_fun`
-- directly, because `X ≃ Y` has got a coercion to `X → Y`,
-- so you can (and should) do it like this:
-- `equiv.symm` again
example (X Y : Type) (e : X ≃ Y) : Y ≃ X :=
  { toFun := e.symm
    -- using `equiv.symm` and dot notation
    invFun := e
    -- using the coercion to function
    left_inv := e.right_inv
    right_inv := e.left_inv }

-- `equiv.trans`
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  { toFun := fun x => eYZ (eXY x)
    invFun := fun z => eXY.symm (eYZ.symm z)
    left_inv := by sorry
    right_inv := by sorry }

-- Because `equiv.trans` is already there, we can just use it
-- directly:
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  Equiv.trans eXY eYZ

-- here it is again using dot notation
example (X Y Z : Type) (eXY : X ≃ Y) (eYZ : Y ≃ Z) : X ≃ Z :=
  eXY.trans eYZ

-- See if you can make the following bijection using dot notation
example (A B C X : Type) (eAX : A ≃ X) (eBX : B ≃ X) : A ≃ B :=
  sorry

-- can you just make the term directly using `equiv.symm`
-- and `equiv.trans`?
/-

Note that `equiv` is *data* -- `X ≃ Y` doesn't say "`X` bijects with `Y`";
that statement is a true-false statement. A term of type `X ≃ Y`
is *explicit functions* `X → Y` and `Y → X`, together with proofs
that they're inverse bijections.

Clearly there's an equivalence relation going on *somewhere* though:
here it is.  

If `X : Type` then `∃ x : X, true` is just the statement that `X`
is nonempty. It's a proposition. So this works:

-/
-- Two types `X` and `Y` satisfy `R X Y` iff there *exists*
-- a bijection `X ≃ Y`.
def R (X Y : Type) : Prop :=
  ∃ e : X ≃ Y, True

example : Equivalence R := by sorry

-- Remark: the equivalence classes of `R` are called *cardinals*.
end Section9sheet3

