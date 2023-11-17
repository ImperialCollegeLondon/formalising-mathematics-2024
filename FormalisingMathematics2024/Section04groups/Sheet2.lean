/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import section04groups.sheet2

-- imports all the Lean tactics
-- imports all the Lean tactics
namespace Section4sheet2

/-!

# Challenge sheet

This is a harder group theory question. 

It turns out that two of the axioms in our definition of a group
are not needed; they can be deduced from the others. Let's define
a "weak group" class, where we only have three of the group axioms.
The question is: can you prove that a weak group is a group, by
proving the other axioms?

-/


-- removing `mul_one` and `mul_inv_self` from the five standard axioms
-- for a group.
class WeakGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  one_mul : ∀ a : G, 1 * a = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

namespace WeakGroup

variable {G : Type} [WeakGroup G] (a b c : G)

/-

The challenge is to prove that G is a group, which we can interpret as
proving the missing axioms `mul_one` and `mul_inv_self`. Note that you
can't use the `group` tactic any more because `G` isn't a group yet:
this is what you're trying to prove!

One way of doing it: try proving 

`mul_left_cancel : a * b = a * c → b = c`

and then

`mul_eq_of_eq_inv_mul : b = a⁻¹ * c → a * b = c`

first.

-/
theorem hMul_left_cancel (h : a * b = a * c) : b = c := by sorry

theorem hMul_one (a : G) : a * 1 = a := by sorry

theorem hMul_inv_self (a : G) : a * a⁻¹ = 1 := by sorry

end WeakGroup

/-

If you want to take this further: prove that if we make
a new class `bad_group` by replacing
`one_mul` by `mul_one` in the definition of `weak_group`
then it is no longer true that you can prove `one_mul`;
there are structures which satisfy `mul_assoc`, `mul_one`
and `inv_mul_self` but which really are not groups.
Can you find an example? Try it on paper first. 

-/
-- claim: not a group in general
class BadGroup (G : Type) extends One G, Mul G, Inv G : Type where
  mul_assoc : ∀ a b c : G, a * b * c = a * (b * c)
  mul_one : ∀ a : G, a * 1 = a
  inv_mul_self : ∀ a : G, a⁻¹ * a = 1

-- `bool` is a type with two terms, `bool.tt` and `bool.ff`. See if you can make it into 
-- a bad group which isn't a group!
instance : One Bool :=
  ⟨sorry⟩

instance : Mul Bool :=
  ⟨sorry⟩

instance : Inv Bool :=
  ⟨sorry⟩

instance : BadGroup Bool where
  mul_assoc := sorry
  -- `dec_trivial`, might be able to do this
  mul_one := sorry
  -- dec_trivial,
  inv_mul_self := sorry

--dec_trivial,
example : ¬∀ a : Bool, 1 * a = a := by sorry

--dec_trivial,
end Section4sheet2

