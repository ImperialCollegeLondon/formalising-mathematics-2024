/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic


/-

# Finite sets

Remember that mathematicians use "set" in two different ways. There is
the generic "collection of stuff" usage, as in "A group is a set equipped with
a multiplication and satisfying these axioms...", for which Lean uses types.
And there's the concept of a *subset*, so we have the collection of stuff
already and want to consider the elements which have some other properties,
for example the subset {1,2,3,4,...,37} of the natural numbers, or the
subset of prime numbers or even numbers or whatever.

I want to talk about "finite sets", but because there are several uses of the
idea of a set in mathematics, the first question is "which kind of finite set?".
Let's talk first about finite *subsets*.

## Two ways to do finite subsets of a type `X`

### First way: a subset of `X`, which is finite

Let `X` be a type. We've already seen the type `Set X` of subsets of `X`,
so one way to let `S` be a finite subset of `X` would be to make a term
`S : Set X` and then to have a hypothesis that `S` is finite.
Recall that a predicate on a type just means
In Lean the predicate on sets which says a set is finite is `Set.Finite`.
So here
is one way of saying "let `S` be a finite subset of `X`":

-/

-- Let X be a type, let `S` be a subset of `X`, and assume `S` is finite. Then S=S.
example (X : Type) (S : Set X) (hS : Set.Finite S) : S = S := by
  rfl

-- Note that because `S` has type `Set (something)` we can use dot notation here:
-- this means the same thing as the above example.
example (X : Type) (S : Set X) (hS : S.Finite) : S = S := by
  rfl

-- Lots of proofs about finite sets in this sense live in the `Set.Finite` namespace.
-- How would you find out the name of the lemma saying that the union of two finite
-- sets is finite?
example (X : Type) (S : Set X) (T : Set X) (hs : Set.Finite S) (ht : T.Finite) : (S ∪ T).Finite :=
  -- `by exact?` will discover that it's `Set.Finite.union`
  hs.union ht -- again dot notation, and we cancelled `by exact` because this just moves
              -- us to tactic mode and back to term mode

/-
But Lean has another way to do finite subsets.

### Second way: the type of all finite subsets of X

Lean has a dedicated type whose terms are finite subsets of `X`. It's called `Finset X`.

Clearly, for a general infinite type `X`, the types `Set X` and `Finset X` are not "the same".
But in type theory, *distinct types are disjoint*. That means if we have a term `S : Finset X`
then *`S` does not have type `Set X`*. A finset is not *equal to* a set. This is the
same phenomenon which says that a natural number in Lean is not *equal to* a real number.
There is a *map* from the natural numbers to the real numbers, and it's a map which
mathematicians don't notice and so it's called a *coercion*, is denoted with a little
up-arrow `↑`, and "happens behind the scenes". The same is true here.

If `S : Finset X` then you can coerce `S` to `Set X`, and this coerced term will be
displayed as `↑S` in Lean, with this arrow meaning "the obvious map from `Finset X` to `Set X`".
-/

-- let X be a type
variable (X : Type)

-- If S is a Finset, then S (considered as a set) is equal to itself.
example (S : Finset X) : (S : Set X) = (S : Set X) := by
  -- goal is `⊢ ↑S = ↑S`
  rfl

-- Lean has the theorem that if you start with a Finset, then the coerced set is finite.
example (S : Finset X) : Set.Finite (S : Set X) :=
  Set.toFinite S

/-

# Why?

Finite sets are really important in computer science, and they also play a special role in
mathematics: for example you can sum over a finite set in huge generality, whereas if you
want to sum over a general set then you need some metric or topology on the target to make
sense of the notion of convergence. Also finite sets can be handled in constructive mathematics
and the theory is much easier to make computable than a general theory of sets. I'm not
particularly interested in making mathematics more constructive and computable, but other
people are, and this is why we've ended up with a dedicated type for finite sets.

Let's see how to do finite sums in Lean. In mathematics we often sum from 1 to n, but
computer scientists seem to prefer to sum from 0 to n-1 (you might have seen this in python).
The finset `{0,1,2,...,n-1} : Finset ℕ` has got a special name: it's called `Finset.range n`.
Let's see it in action by proving that the sum of i^2 from i=0 to n-1 is
(some random cubic with 6 in the denominator).

Note in the below example: I use the coercion `(x : ℚ)` to mean "`x` is a natural, but
consider it as a rational number for this proof". It's really important to do this calculation
over the rationals, because subtraction and division are pathological operations on the
naturals (e.g. 2-3=0 and 5/2=2 in the naturals, as they are forced to return a natural as an answer)
-/

open BigOperators -- enable ∑ notation

example (n : ℕ) : ∑ i in Finset.range n, (i : ℚ) ^ 2 = (n : ℚ) * (n - 1) * (2 * n - 1) / 6 := by
  -- induction on `n`.
  induction' n with d hd
  · -- base case `n = 0` will follow by rewriting lemmas such as `∑ i in finset.range 0 f(i) = 0`
    -- and `0 * x = 0` etc, and the simplifier knows all these things.
    simp
  · -- inductive step
    -- We're summing over `Finset.range (succ d)`, and so we next use the lemma saying
    -- that equals the sum over `Finset.range d`, plus the last term.
    rw [Finset.sum_range_succ]
    -- Now we have a sum over finset.range d, which we know the answer to by induction
    rw [hd]
    -- Now tidy up (e.g. replace all the `succ d` with `d + 1`)
    simp
    -- and now it must be an identity in algebra.
    ring

-- If you look through the proof you'll see some ↑; this is because we can't do the
-- algebra calculation in the naturals because subtraction and division are involved.
-- The up-arrows are "the obvious map from the naturals to the rationals".

-- See if you can can sum the first n cubes.
example (n : ℕ) : ∑ i in Finset.range n, (i : ℚ) ^ 3 = (n : ℚ) ^ 2 * (n - 1) ^ 2 / 4 := by
  induction' n with d hd
  · simp
  · simp [Finset.sum_range_succ, hd]
    ring
