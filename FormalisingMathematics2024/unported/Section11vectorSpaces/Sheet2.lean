/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Finite-dimensional vector spaces

Here's how you say "let `k` be a field and let `V` be a finite-dimensional `k`-vector space"

-/

-- let k be a field and let V be a finite-dimensional k-vector space
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

#check FiniteDimensional.finrank

/-
There are two concepts of "dimension" in Lean. There's a general `Module.rank k V`, which
returns a `Cardinal` (so in particular the answer could be one of many kinds of infinity)
and, in the finite-dimensional case, there is `FiniteDimensional.finrank k V`, which returns
a natural number. Note that, as is idiomatic in Lean, the latter function will accept
an infinite-dimensional space as input (garbage in) and will return 0 for the answer
(garbage out). All our spaces will be finite-dimensional, so we can use
`FiniteDimensional.finrank`. Note that if we `open FiniteDimensional` then we can
just call it `finrank`.

So how do we find theorems about `finrank`? Well one way of doing it would be to control-click
(or command-click on Mac, I think) on `finrank` in some Lean code (not in a comment though)
and then just browse the file which the definition is in (be careful not to edit it though).

Another way would be to type `FiniteDimensional.finrank` into the online documentation
here https://leanprover-community.github.io/mathlib4_docs/ , and then read the docs instead.
The most relevant page is
https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Dimension/Finrank.html .
That way you don't see the proofs, which makes things easier to read.

Or I could just tell you some. Here's some API for `finrank`. Note
that if `A : Subspace k V` then `A` is a term, not a type, and in particular it's not a
vector space (it's a vector subspace). However `↥A`, a "coercion to type", is a type,
and hence has a `finrank`.

## Some API for finite-dimensional vector spaces

This should be all you need.

`Submodule.finrank_sup_add_finrank_inf_eq` says
    `finrank k ↥(A ⊔ B) + finrank k ↥(A ⊓ B) = finrank k ↥A + finrank k ↥B`
`Submodule.finrank_le A : finrank k ↥A ≤ finrank k V`
`finrank_bot k V : finrank k ↥⊥ = 0`

# An example sheet question

A 2019 University of Edinburgh example sheet question (set to me as a challenge by a lecturer
there): prove that if `V` is a 9-dimensional
vector space and `A, B` are two subspaces of dimension 5, then `A ∩ B` cannot be
the zero vector space.

-/
open FiniteDimensional -- now we can just write `finrank`.

example (A B : Subspace k V) (hV : finrank k V = 9) (hA : finrank k A = 5) (hB : finrank k B = 5) :
    A ⊓ B ≠ ⊥ := by
  sorry
