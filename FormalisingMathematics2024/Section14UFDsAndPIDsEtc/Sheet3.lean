/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic
import Mathlib.RingTheory.UniqueFactorizationDomain -- UFDs
import Mathlib.RingTheory.PrincipalIdealDomain      -- PIDs
import Mathlib.Data.MvPolynomial.CommRing
import Mathlib.RingTheory.Polynomial.Basic          -- multivariable polynomials

/-

# Unique Factorization Domains

Thanks to Yael on the Discord for explaining to me how to write "let R be a UFD"
in Lean! It looks like this.

-/
-- let R be a UFD
variable (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]

/-

The reason we're seeing `UniqueFactorizationMonoid` here is that
the definition of unique factorization domain never mentions addition!
So it makes sense for monoids.

-/
-- a PID is a UFD (so ℤ, k[X] etc are UFDs)
example (R : Type) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] :
    UniqueFactorizationMonoid R := by infer_instance

-- multivariate polynomials over a field in a set of variables
-- indexed by a (possibly infinite) index set I are a UFD
example (k : Type) [Field k] (I : Type) :
    UniqueFactorizationMonoid (MvPolynomial I k) := inferInstance

/-

Under the hood, the definition of UFD is a bit weird. But

A binary relation ★ is *well-founded* if you can't have an infinite decreasing
sequence a₂ ★ a₁, a₃ ★ a₂, a₄ ★ a₃, ... . For example `<` is well-founded
on the naturals, but `≤` is not, and `<` is not well-founded on the integers.

If `R` is a commutative ring, let's define `a ★ b` to mean "a strictly divides b",
i.e. that there exists a non-unit `c` such that `b = a * c`. The mathlib folks
in their wisdom decided to call `R` a `WfDvdMonoid` ("a well-founded monoid under division")
if this relation is well-founded. For example the integers are a `WfDvdMonoid`,
because (for example) 24 ★ 0, 12 ★ 24, 3 ★ 12, 1 ★ 3, but there's no solution to `x ★ 1`.

-/
example : WfDvdMonoid ℤ := by infer_instance

-- In fact (if you know what this means): any Noetherian integral domain is a `WfDvdMonoid`:
example (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] : WfDvdMonoid R := by
  infer_instance

/-

...and in particular any PID is a `wf_dvd_monoid`.

The point about well-founded orders is that you can do well-founded induction
on them, which is what mathematicians often call "strong induction". In other words,
if `S` is a set and `★` is a well-founded binary relation on `S`, and if
you can prove "for all `s : S`, if `P(t)` is true for all `t ★ s` then `P(s)` is true",
then you can deduce "for all `a : S`, `P(a)` is true" (proof: if `P(a)` is not
true for all `a`, then choose some `a₁` for which it's false, and then by
hypothesis there must be `a₂ ★ a₁` for which `P(a₂)` is false, and go on
like this to obtain a contradiction to well-foundedness).

As a consequence, we can deduce that in an integral which is
a `WfDvdMonoid`, everything nonzero factors as a unit multiplied by a product of irreducibles.
For by well-founded induction all we have to do is to check that if all proper
divisors of a nonzero element `s` factor as unit times irreducibles, then `s` does
too. If `s` is a unit or irreducible then we're done, and if it isn't then
by definition of irreducible it factors as `s = ab` with `a ★ s` and `b ★ s`;
both `a` and `b` factor into irreducibles, so `s` does too.

(Note that this argument proves that every nonzero element of every Noetherian
integral domain factors into irreducibles)

However, the factorization might not be unique (take for example `ℤ[√-5]` or your
favourite non-UFD domain which is Noetherian. The problem is that the concept of prime
and irreducible don't coincide in general integral domains.
In Lean it turns out that the definition of UFD is "`WfDvdMonoid`, and irreducible ↔ prime",
and it's a theorem that this is mathematically equivalent to the usual definition.
The reason for this is that "irreducible ↔ prime" is precisely what you need
to get the proof that two factorizations are equivalent (pull an irreducible off
one factorization, and then use that it's prime to show that it shows up in the
other factorization).

## A theorem

Here's a theorem about UFDs.

The *height* of a prime ideal `P` in a commutative ring `R` is
the largest `n` such that there exists a strictly increasing
chain of prime ideals `P₀ ⊂ P₁ ⊂ ⋯ ⊂ Pₙ = P` (or +∞ if there
are chains of arbitrary length). The claim is that in a UFD,
all height one primes are principal.

-/

namespace Section14Sheet3

-- out of laziness we don't define height n primes in a general
-- commutative ring but just height one primes in an integral
-- domain
/-- An ideal of an integral domain is a height one prime if it's prime, it's
nonzero, and the only strictly smaller prime ideal is the zero ideal. -/
def IsHeightOnePrime
    {R : Type} [CommRing R] [IsDomain R] (P : Ideal R) : Prop :=
  P.IsPrime ∧ P ≠ 0 ∧ ∀ Q : Ideal R, Q.IsPrime ∧ Q < P → Q = 0

-- All height one primes are principal in a UFD.
example (R : Type) [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (P : Ideal R) : IsHeightOnePrime P → P.IsPrincipal :=
  /-
    The maths proof: let P be a height 1 prime. Then P ≠ 0, so choose
    nonzero x ∈ P. Factor x into irreducibles; by primality of P one
    of these irreducible factors π must be in P. But now (π) ⊆ P,
    and (π) is prime and nonzero, so by the height 1 assumption we
    must have (π)=P.
    -/
  sorry

end Section14Sheet3
