/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic

/-

# Finitely-supported functions

We're used to dealing with finite-dimensional vector spaces when we begin studying
vector spaces, but infinite-dimensional vector spaces exist everywhere (for example
the polynonial ring `ℝ[X]` is an infinite-dimensional real vector space) and Lean
is happy to work with both finite and infinite-dimensional vector spaces.

If `V` is a finite-dimensional vector space, with basis `{e₁,e₂,...,eₙ}`, then
every element of `V` can be uniquely expressed as ∑ cᵢeᵢ, with cᵢ in the ground field.
In the infinite-dimensional case this doesn't make sense, because in algebra you
cannot do infinite sums in general; you need some kind of metric or topology
to express the idea that an infinite sum converges or tends to some limit, and a general
field `k` may not have a metric or a topology. If `k` is a finite field, you could
give it the discrete topology, but then no infinite sum would converge, unless all
but finitely many of the terms were actually equal to zero.

The simplest example of an infinite-dimensional vector space is the ring of polynomials
`k[X]` over a field `k`, and this vector space has a basis `{1,X,X²,X³,...}`. Hopefully
all this enables you to see what is going on: whilst the vector space is infinite-dimensional,
and the basis is infinite, each vector in the space (i.e. each polynomial in `k[X]`) is
a *finite* linear combination of basis elements; so we have `v = ∑ᵢ cᵢ eᵢ` but all
of the `cᵢ` are zero other than finitely many of them. This makes the sum finite,
and hence it makes in algebra without having to assume anything about existence of
metrics or topologies.

This example shows that an important role in the theory of vector spaces is played
by the *finitely-supported functions*. If `X` and `Y` are types, and `Y` has a special
element called `0`, then a function from `X` to `Y` is *finitely-supported* if it sends
all but finitely many elements of `X` to `0`. Just like the theory of finite sets,
there are two ways to set up a theory of finitely-supported functions. We could first
consider all functions and then have a predicate on functions saying "I have finite support".
Alternatively, we could make an entirely new type of finitely-supported functions, and
then just have a map from that type to the type of all functions. This latter approach
is what we do in Lean.

The type of finitely-supported functions from `X` to `Y` is denoted `X →₀ Y`, which
is notation for `Finsupp X Y`. Put another way; a term of this type can be thought
of as a function from `X` to `Y` which is only non-zero on a finite subset of `X`.
Note that `Y` needs to have a `zero` for this notion to make sense.
-/

example : Type :=
  ℕ →₀ ℕ -- works because ℕ has a zero

/-

The theory of finitely supported functions is a noncomputable theory in Lean, so
let's switch `noncomputable` on.

-/
noncomputable section

-- In the application to vector spaces, `Y` will be a field, so it will have a zero.
-- If you know about free modules, then you can let `Y` be a ring.
-- Lean's typeclass inference system knows that if `X` is an arbitrary type and `k` is a field,
-- then `X →₀ k` is a `k`-vector space.
example (X : Type) (k : Type) [Field k] : Module k (X →₀ k) := by
  infer_instance -- the tactic which magics up terms which the typeclass inference
                 -- system knows about.

-- In particular, Lean is happy to add two finitely-supported functions and return
-- a finitely-supported function.
-- Lean will also allow you to evaluate a finitely-supported function at an input,
-- even though a finitely-supported function is not strictly speaking a function
-- (it's a function plus some extra data and proofs). Lean will *coerce* a finitely-supported
-- function into a function if required though.
example (X : Type) (k : Type) [Field k] (f : X →₀ k) (x : X) : k :=
  f x

-- Because these things are a vector space, addition of two finitely-supported functions is a
-- finitely-supported function. Similarly multiplication by a scalar is a finitely-supported
-- function
example (X : Type) (k : Type) [Field k] (f g : X →₀ k) (c : k) : X →₀ k :=
  c • f + g

-- How do we access the support of `f`? i.e. what is the finite subset of `X` where `f`
-- is nonzero? If you try `by exact?` below you'll get `Finset.empty`, but we want
-- to definitely use `f` so try `by exact? using f` and you'll hopefully get the right answer.
example (X : Type) (k : Type) [Field k] (f : X →₀ k) : Finset X := f.support -- hover to check!
