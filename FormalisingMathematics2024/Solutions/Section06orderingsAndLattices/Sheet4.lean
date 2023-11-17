/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathbin.Tactic.Default

#align_import solutions.section06orderings_and_lattices.sheet4

/-

# Complete lattices

A lattice has sups and infs for all subsets with 2 elements. A *complete lattice* has sups
and infs for *every* subset. An example would be the set of all subsets of a fixed base set
(or, in Lean speak, the type `set X` of all subsets of a type `X`). Other examples: all
subgroups of a group, all subspaces of a vector space (and all subrings of a ring, all
subfields of a field...). A non-example would be the real numbers: we do say that the
reals are "complete" but we're talking about a different kind of completeness here
(an order-theoretic concept, not a metric space concept), and indeed subsets of ℝ like
the natural numbers, or the empty set, do *not* have a sup. 

If `L` is a complete lattice, and `S : set L` is a subset, then its sup is `Sup S`
and its inf is `Inf S`. Here's the basic API for `Sup`:

`le_Sup : a ∈ S → a ≤ Sup S`
`Sup_le : (∀ (b : L), b ∈ S → b ≤ a) → Sup S ≤ a`

and you can probably guess the basic API for `Inf` :-)

A special case: the empty set has a `Sup` and and an `Inf`, and if you think carefully
about this then you'll discover that this means that the lattice has a least element and a
greatest element. These elements are called `⊥` and `⊤` respectively, pronounced `bot`
and `top`. 

`Sup_empty : Sup ∅ = ⊥`

See if you can prove basic things about `⊥` and `Sup` just using the API for `Sup`. 
All these results are in the library, but it's a good exercise to prove them from
the axioms directly. 

-/
/-

# Complete lattices

A lattice has sups and infs for all subsets with 2 elements. A *complete lattice* has sups
and infs for *every* subset. An example would be the set of all subsets of a fixed base set
(or, in Lean speak, the type `set X` of all subsets of a type `X`). Other examples: all
subgroups of a group, all subspaces of a vector space (and all subrings of a ring, all
subfields of a field...). A non-example would be the real numbers: we do say that the
reals are "complete" but we're talking about a different kind of completeness here
(an order-theoretic concept, not a metric space concept), and indeed subsets of ℝ like
the natural numbers, or the empty set, do *not* have a sup. 

If `L` is a complete lattice, and `S : set L` is a subset, then its sup is `Sup S`
and its inf is `Inf S`. Here's the basic API for `Sup`:

`le_Sup : a ∈ S → a ≤ Sup S`
`Sup_le : (∀ (b : L), b ∈ S → b ≤ a) → Sup S ≤ a`

and you can probably guess the basic API for `Inf` :-)

A special case: the empty set has a `Sup` and and an `Inf`, and if you think carefully
about this then you'll discover that this means that the lattice has a least element and a
greatest element. These elements are called `⊥` and `⊤` respectively, pronounced `bot`
and `top`. 

`Sup_empty : Sup ∅ = ⊥`

See if you can prove basic things about `⊥` and `Sup` just using the API for `Sup`. 
All these results are in the library, but it's a good exercise to prove them from
the axioms directly. 

-/
-- Let `L` be a complete lattice and say `a` is a general element of `L`
-- Let `L` be a complete lattice and say `a` is a general element of `L`
variable (L : Type) [CompleteLattice L] (a : L)

-- this is called `bot_le`
example : ⊥ ≤ a := by
  rw [← sSup_empty]
  apply sSup_le
  rintro b ⟨⟩

-- recall `b ∈ ∅` is defined to mean `false`, and `cases` on a proof of `false` 
-- solves the goal
-- this is called `le_bot_iff`
example : a ≤ ⊥ ↔ a = ⊥ := by
  constructor
  · rw [← sSup_empty]
    intro h
    -- to prove x = y suffices to prove x ≤ y and y ≤ x, and we alreasdy have x ≤ y (it's `h`)
    apply le_antisymm h
    apply sSup_le
    rintro _ ⟨⟩
  · rintro rfl
    -- quicker than `intro h, rw h`
    rfl

-- `≤` is reflexive
-- this is called Sup_le_Sup
example (S T : Set L) : S ⊆ T → sSup S ≤ sSup T :=
  by
  intro hST
  apply sSup_le
  intro b hb
  apply le_sSup
  apply hST
  -- definitional abuse: S ⊆ T is *defined* to mean `∀ a, a ∈ S → a ∈ T`
  exact hb

