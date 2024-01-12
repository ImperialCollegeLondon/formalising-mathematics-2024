/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

## Orderings and lattices

In section 4 we saw how subsets of a type worked, and we saw that
things like `⊆` and `∪` and `∩` made sense for subsets, and they satisfied
theorems such as `A ∩ B ⊆ B`.

But it turns out that there is a more general abstraction called a *lattice*
which captures these kinds of ideas, and I'd like to explain this
concept in this section. Note that the word "lattice" unfortunately
means several distinct things in mathematics; this is the use of the
word in the context of partial orders. So let me start by talking about
partial orders.

## Partial orders

A *partial order* (or a partially ordered type) is a type `X` equipped with
a concept of `≤` satisfying some axioms. More precisely `X` is equipped
with a true-false statement `a ≤ b` for each `a b : X`, satisfying
the following axioms:

`le_refl a : a ≤ a`
`le_antisymm : a ≤ b → b ≤ a → a = b`
`le_trans : a ≤ b → b ≤ c → a ≤ c`

Examples of partial orders include the natural numbers and the real numbers. However
these examples are not quite representative, because a partial order does *not* have
the axiom that for all `a b : X` we have either `a ≤ b` or `b ≤ a`. A perhaps more
representative example of a partial order is the type `Set X` of subsets of a type `X`,
with `a ≤ b` defined to mean `a ⊆ b`. For two general subsets `a` and `b` of `X`,
`a ⊆ b` and `b ⊆ a` might both be false.
-/

-- Let `X` be a partial order.
variable (X : Type) [PartialOrder X]

-- You can prove transitivity directly using the axiom
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c :=
  le_trans hab hbc

-- or you can use the `trans` tactic
example (a b c : X) (hab : a ≤ b) (hbc : b ≤ c) : a ≤ c := by
  trans b
  · exact hab
  · exact hbc

-- Let a,b,c,d be arbitrary elements of `X`
variable (a b c d : X)

-- See if you can prove these basic facts about partial orders.
example : a ≤ a :=
  le_refl a

example (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) : a ≤ d :=
  le_trans hab (le_trans hbc hcd)

example (hab : a ≤ b) (hbc : b ≤ c) (hca : c ≤ a) : a = b := by
  apply le_antisymm hab
  exact le_trans hbc hca
