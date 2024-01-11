/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one of these equalities holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question.

-/

-- This is a cheating proof. Instead of actually doing the work, I just steal
-- the argument from Lean's maths library.

namespace Section6Sheet3solutions

lemma foo (L : Type) [Lattice L] (h : ∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) :
    ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  -- our hypothesis `h` makes `L` into what Lean calls a `DistribLattice`
  letI : DistribLattice L := { (show Lattice L by infer_instance) with le_sup_inf := fun x y z => by rw [← h] }
  -- The result we want is now already in the library
  exact fun a b c => inf_sup_left -- ctrl-click on this to see the actual proof

example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  constructor
  · apply foo
  · apply foo (Lᵒᵈ)
