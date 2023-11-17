/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default


/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one equality holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question. 

-/
/-

# A harder question about lattices

I learnt this fact when preparing sheet 2.

With sets we have `A ∪ (B ∩ C) = (A ∪ B) ∩ (A ∪ C)`, and `A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)`.
In sheet 2 we saw an explicit example (the lattice of subspaces of a 2-d vector space)
of a lattice where neither `A ⊓ (B ⊔ C) = (A ⊔ B) ⊓ (A ⊔ C)` nor `A ⊓ (B ⊔ C) = (A ⊓ B) ⊔ (A ⊓ C)`
held. But it turns out that in a general lattice, one equality holds if and only if the
other one does! This was quite surprising to me.

The challenge is to prove it in Lean. My strategy would be to prove it on paper first
and then formalise the proof. If you're not in to puzzles like this, then feel free to skip
this question. 

-/
-- This is a really unhelpful proof; the argument below is "a lattice satisfying one of
-- This is a really unhelpful proof; the argument below is "a lattice satisfying one of
-- the distributivity laws is called a `distrib_lattice` in Lean and it's a theorem
-- the distributivity laws is called a `distrib_lattice` in Lean and it's a theorem
-- in Lean called `inf_sup_left` that a `distrib_lattice` satisfies the other law,
-- in Lean called `inf_sup_left` that a `distrib_lattice` satisfies the other law,
-- so just apply that". There is a purely low-level proof though, which you can see by
-- so just apply that". There is a purely low-level proof though, which you can see by
-- just looking at mathlib's proof of `inf_sup_left`, and which I will write
-- just looking at mathlib's proof of `inf_sup_left`, and which I will write
-- down here if I find the time :-/ I'd rather concentrate on getting some groups and
-- down here if I find the time :-/ I'd rather concentrate on getting some groups and
-- vector spaces into the course repo though, because the first project deadline is imminent.
-- vector spaces into the course repo though, because the first project deadline is imminent.
example (L : Type) [Lattice L] :
    (∀ a b c : L, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c)) ↔ ∀ a b c : L, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c :=
  by
  constructor
  · intro h
    -- make a distrib_lattice from `h`
    letI : DistribLattice L := { _inst_1 with le_sup_inf := fun x y z => by rw [← h] <;> rfl }
    intros
    -- use `inf_sup_left`, proved in Lean. Look at the proof to see where the actual
    -- content is.
    exact inf_sup_left
  · -- other way is the same but using the dual partial order (so `a ≤ b` is defined to be `b ≤ a`!)
    intro h
    letI foo : Lattice Lᵒᵈ := inferInstance
    -- now need to change all infs to sups and vice versa
    change ∀ a b c : Lᵒᵈ, a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) at h 
    change ∀ a b c : Lᵒᵈ, a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c
    -- now same proof as before
    letI : DistribLattice Lᵒᵈ := { foo with le_sup_inf := fun x y z => by rw [← h] <;> rfl }
    intros
    exact inf_sup_left

