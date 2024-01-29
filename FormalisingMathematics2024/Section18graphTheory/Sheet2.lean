/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.Combinatorics.SimpleGraph.Connectivity
-- paths, cycles etc in graph theory

/-

Cut and pasted directly from the module docstring from the file imported above:

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

(and then there's a warning that in topology some of these words are
used to mean different things)

So of course the question is how to actually do this in Lean. Here's how.
Let `G` be a simple graph with vertex set `V`, and say `v,w,x` in `V`

-/

variable (V : Type) (G : SimpleGraph V) (v w x : V)

-- The type of all walks from `v` to `w`
example : Type :=
  G.Walk v w

-- The empty walk from `v` to `v`
example : G.Walk v v :=
  SimpleGraph.Walk.nil' v

-- oh that's a bit annoying, let's open `SimpleGraph`
open SimpleGraph

example : G.Walk v v :=
  Walk.nil' v

-- Add an edge to the beginning of a walk
example (h : G.Adj v w) (a : G.Walk w x) : G.Walk v x :=
  Walk.cons' v w x h a

-- There's also walk.cons where you don't have to specify the vertices
example (h : G.Adj v w) (a : G.Walk w x) : G.Walk v x :=
  Walk.cons h a

-- concatenation of walks
example (a : G.Walk v w) (b : G.Walk w x) : G.Walk v x :=
  a.append b

-- Let `a` be a walk from `v` to `w`
variable (a : G.Walk v w)

-- length of `a` is a natural
example : ℕ :=
  a.length

-- reverse of `a`
example : G.Walk w v :=
  a.reverse

-- n'th vertex visited in `a`
example (n : ℕ) : V :=
  a.getVert n

-- 0'th vertex is where we start
example : a.getVert 0 = v :=
  Walk.getVert_zero a

-- (Walk length)'th vertex is where we end.
example : a.getVert a.length = w :=
  Walk.getVert_length a

-- Support of `a` is the list of vertices it goes through
example : List V :=
  a.support

-- Edges of `a` is the list of edges it goes through
example : List (Sym2 V) :=
  a.edges

-- A walk is a *trail* if it has no repeating edges.
example : Prop :=
  a.IsTrail

-- A walk is a *path* if it has no repeating vertices.
example : Prop :=
  a.IsPath

-- Paths are sufficiently common that `G.path v w` is defined to be the
-- subtype `{p : G.walk v w // p.is_path}`. So to give a term of type `G.path v w`
-- is to give a pair consisting of a walk `p : G.walk v w` and a proof of `p.IsPath`.
-- A walk is a *circuit* at `v : V` if it's a nonempty trail beginning and ending at `v`.
example (b : G.Walk v v) : Prop :=
  b.IsCircuit

-- A walk is a *cycle* at `v : V` if it's a circuit at `v` whose only repeating vertex
-- is `v` (which appears exactly twice).
example (b : G.Walk v v) : Prop :=
  b.IsCycle

-- Exercise : give an example of a circuit which isn't a cycle. Can you do it in Lean?
-- Remark: a Lean solution is in the solutions.
-- Example theorem in the API: given a walk `p` from `v` to `u` and an edge from `u` to `v`,
-- putting them together gives a cycle iff `p` is a path and the edge from `u` to `v`
-- is not in the edges of `p`.
example {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ Sym2.mk (u, v) ∉ p.edges :=
  Walk.cons_isCycle_iff p h

-- Given a walk from `v` to `w` and a vertex `u` in the support of the walk,
-- truncate the walk so it starts at `v` and finishes at `u`.
open scoped Classical

noncomputable section

-- don't ask me
example (a : G.Walk v w) (u : V) (hu : u ∈ a.support) : G.Walk v u :=
  a.takeUntil u hu

-- With the same hypotheses, return the rest of the walk from `u` to `w`
example (a : G.Walk v w) (u : V) (hu : u ∈ a.support) : G.Walk u w :=
  a.dropUntil u hu

-- Example in the API : those two walks added together give the original
-- walk again
example (a : G.Walk v w) (u : V) (hu : u ∈ a.support) :
    (a.takeUntil u hu).append (a.dropUntil u hu) = a :=
  Walk.take_spec a hu

-- Two vertices `u` and `v` satisfy `G.reachable u v : Prop` if there's a walk from `u` to `v`.
example : G.Reachable v w ↔ Nonempty (G.Walk v w) :=
  Iff.rfl

-- true by definition
-- Can you show that `G.reachable` is an equivalence relation?
example : Equivalence G.Reachable := by sorry

-- A graph is "preconnected" if `G.reachable v w` is true for any `v w : V`.
-- Note that this includes the empty graph with `V` empty, for silly logic reasons.
example : G.Preconnected ↔ ∀ v w : V, G.Reachable v w :=
  Iff.rfl
-- true by definition

-- A graph is connected iff it's preconnected and nonempty.
example : G.Connected ↔ G.Preconnected ∧ Nonempty V :=
  connected_iff G
