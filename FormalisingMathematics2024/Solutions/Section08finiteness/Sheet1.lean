/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default

#align_import solutions.section08finiteness.sheet1

/-

# Finite sets

Remember that mathematicians use "set" in two different ways. There is
the generic "collection of stuff" usage, as in "A group is a set equipped with
a multiplication and satisfying these axioms...", for which Lean uses types.
And there's the concept of a *subset*, so we have the collection of stuff
already and want to consider the elements which have some other properties,
for example the subset {1,2,3,4,...,37} of the natural numbers, or the
subset of prime numbers or even numbers or whatever.

Someone on the Discord asked if I would do something about "finite sets",
and because there are two uses of the idea of a set in mathematics, the
first question on my mind is "which kind of finite set?". It seems to me
that the student is interested in finite *subsets* of the naturals and
the reals, so let's talk first about finite subsets.

## Two ways to do finite subsets of a type `X`

### First way: a subset of `X`, which is finite

Let `X` be a type. We've already seen the type `set X` of subsets of `X`,
so one way to let `S` be a finite subset of `X` would be to make a term
`S : set X` and then to have a hypothesis that `S` is finite. 
In Lean the predicate which says a set is finite is `set.finite`. So here
is one way of saying "let `S` be a finite subset of `X`":

-/
/-

# Finite sets

Remember that mathematicians use "set" in two different ways. There is
the generic "collection of stuff" usage, as in "A group is a set equipped with
a multiplication and satisfying these axioms...", for which Lean uses types.
And there's the concept of a *subset*, so we have the collection of stuff
already and want to consider the elements which have some other properties,
for example the subset {1,2,3,4,...,37} of the natural numbers, or the
subset of prime numbers or even numbers or whatever.

Someone on the Discord asked if I would do something about "finite sets",
and because there are two uses of the idea of a set in mathematics, the
first question on my mind is "which kind of finite set?". It seems to me
that the student is interested in finite *subsets* of the naturals and
the reals, so let's talk first about finite subsets.

## Two ways to do finite subsets of a type `X`

### First way: a subset of `X`, which is finite

Let `X` be a type. We've already seen the type `set X` of subsets of `X`,
so one way to let `S` be a finite subset of `X` would be to make a term
`S : set X` and then to have a hypothesis that `S` is finite. 
In Lean the predicate which says a set is finite is `set.finite`. So here
is one way of saying "let `S` be a finite subset of `X`":

-/
-- "Let X be a type, let `S` be a subset of `X`, and assume `S` is finite.
-- "Let X be a type, let `S` be a subset of `X`, and assume `S` is finite.
-- Then S = S"
-- Then S = S"
example (X : Type) (S : Set X) (T : Set X) (hs : Set.Finite S) (ht : T.Finite) : (S ∪ T).Finite :=
  hs.union ht

-- set.finite.union
/-

But Lean has another way. 

### Second way: the type of all finite subsets of X

Lean has a dedicated type whose terms are finite subsets of `X`. It's called `finset X`.

Clearly, for a general infinite type `X`, `set X` and `finset X` are not "the same".
In type theory, *distinct types are disjoint*. That means if we have a term `S : finset X`
then *`S` does not have type `set X`*. A finset is not *equal to* a set. This is the
same phenomenon which says that a natural number in Lean is not *equal to* a real number. 
There is a *map* from the natural numbers to the real numbers, and it's a map which
mathematicians don't notice and so it's called a *coercion* and is represented by a little
up-arrow. The same is true here.

If `S : finset X` then you can coerce `S` to `set X`, and this coerced term will be 
displayed as `↑S` in Lean, with this arrow meaning "the obvious map from `finset X` to `set X`".

-/
-- let X be a type
variable (X : Type)

example (S : Finset X) : (S : Set X) = (S : Set X) :=
  by-- ⊢ ↑S = ↑S
  rfl

-- Lean has the theorem that if you start with a finset, then the coerced set is finite.
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
computer scientists seem to prefer to sum from 0 to n-1. The finset `{0,1,2,...,n-1} : finset ℕ`
has got a name; it's called `finset.range n`. Let's see it in action by proving that
the sum of i^2 from i=0 to n-1 is (some random cubic with 6 in the denominator).

-/
open scoped BigOperators

-- enable ∑ notation
example (n : ℕ) : ∑ i in Finset.range n, (i : ℚ) ^ 2 = n * (n - 1) * (2 * n - 1) / 6 :=
  by
  induction' n with d hd
  ·-- base case n = 0 will follow by rewriting lemmas such as `∑ i in finset.range 0 f(i) = 0`
    -- and `0 * x = 0` etc, and the simplifier knows all these things.
    simp
  · -- inductive step
    -- We're summing to `finset.range succ(d)`, and so we next use the lemma saying
    -- that equals the sum over `finset.range d`, plus the last term.
    rw [Finset.sum_range_succ]
    -- Now we have a sum over finset.range d, which we know the answer to by induction
    rw [hd]
    -- Now tidy up (e.g. replace all the `succ d` with `d + 1`)
    simp
    -- and now it must be an identity in algebra.
    ring

-- If you look through the proof you'll see some ↑; this is because we can't do the
-- algebra calculation in the naturals because subtraction and division are involved,
-- and the definitions of subtraction and division on the naturals in Lean are *pathological*
-- (for example 4 - 5 = 0 and 5 / 2 = 2, because they have to return naturals, so they have to
-- return the wrong answer). So we coerce everything to the rationals first, and then the
-- problem goes away.
-- See if you can can sum the first n cubes.
example (n : ℕ) : ∑ i in Finset.range n, (i : ℚ) ^ 3 = n ^ 2 * (n - 1) ^ 2 / 4 :=
  by
  -- same proof works
  induction' n with d hd
  · simp
  · simp [Finset.sum_range_succ, hd]
    ring

