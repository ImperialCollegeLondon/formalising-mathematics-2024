/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Acyclic
-- trees and forests

/-

# Trees and forests

A *forest* is a graph with no cycles. A *tree* is a connected forest.

Here's how to do this in Lean. Let `G` be a graph with vertex set `V`.

-/

variable (V : Type) (G : SimpleGraph V)

-- Here's how to say "G is a forest"
example : Prop :=
  G.IsAcyclic

-- It's defined to mean "For all `v : V`, every walk from `v` to `v` is not a cycle. "
example : G.IsAcyclic ↔ ∀ (v : V) (p : G.Walk v v), ¬p.IsCycle := by rfl

-- Here's how to say "G is a tree"
example : Prop :=
  G.IsTree

example : G.IsTree ↔ G.Connected ∧ G.IsAcyclic :=
  G.isTree_iff

-- Here are some harder theorems from the library. Recall that a *path* is a walk
-- with no repeated vertices.
-- A graph is acyclic iff for all `v w : V`, there's at most one path from `v` to `w`.
example : G.IsAcyclic ↔ ∀ (v w : V) (p q : G.Path v w), p = q :=
  SimpleGraph.isAcyclic_iff_path_unique

-- A graph is a tree iff `V` is nonempty and for all `v w : V`,
-- there's exactly one path from `v` to `w`.
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath :=
  SimpleGraph.isTree_iff_existsUnique_path

-- If you want a logic puzzle, rephrase this in terms of `G.path`
example : G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Path v w, True :=
  by
  rw [SimpleGraph.isTree_iff_existsUnique_path]
  apply and_congr Iff.rfl
  apply forall_congr'; intro v
  apply forall_congr'; intro w
  constructor
  · rintro ⟨p, hp, hp2⟩
    refine' ⟨⟨p, hp⟩, True.intro, _⟩
    rintro ⟨q, hq⟩ -
    ext
    exact hp2 _ hq
  · rintro ⟨⟨p, hp⟩, -, h2⟩
    refine' ⟨p, hp, fun q hq => _⟩
    specialize h2 ⟨q, hq⟩ True.intro
    cases h2
    rfl

/-
If you want a hard graph theory puzzle, prove that in a finite tree,
1 + the number of edges equals the number of vertices.
I don't think this is in the library and it would be a neat project.

Because induction on the size of `V` will be messy (it will involve
changing `V` and them moving between graphs on different types)
I think that the best way to do this would be to prove that for
an acyclic graph on a fixed `V`, #connected components + #edges = #vertices,
by induction on number of edges.

Note: the solution to this is not in the solutions!
-/
open scoped Classical

example (V : Type) [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    1 + Finset.card G.edgeFinset = Fintype.card V :=
  sorry
