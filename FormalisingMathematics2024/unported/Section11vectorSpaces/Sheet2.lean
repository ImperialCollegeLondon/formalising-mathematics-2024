/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default
import LinearAlgebra.FiniteDimensional


/-!

# Finite-dimensional vector spaces

Here's how you say "let `k` be a field and let `V` be a finite-dimensional `k`-vector space"

-/


-- imports all the Lean tactics
-- imports all the Lean tactics
-- finite-dimensional vector spaces
-- finite-dimensional vector spaces
-- let k be a field and let V be a k-vector space
variable (k : Type) [Field k] (V : Type) [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-

There are two concepts of "dimension" in Lean. There's a general `module.rank k V`, which
returns a `cardinal` (so in particular the answer could be one of many kinds of infinity)
and, in the finite-dimensional case, there is `finite_dimensional.finrank k V`, which returns
a natural number. Note that, as is idiomatic in Lean, the latter function will accept
an infinite-dimensional space as input (garbage in) and will return 0 for the answer
(garbage out). All our spaces will be finite-dimensional, so we can use
`finite_dimensional.finrank`. Note that if we `open finite_dimensional` then we can
just call it `finrank`. 

# An example sheet question

A 2019 University of Edinburgh example sheet question: prove that if `V` is a 9-dimensional
vector space and `A, B` are two subspaces of dimension 5, then `A ∩ B` cannot be 
the zero vector space. See below the question for the API you'll need.

-/
open FiniteDimensional

example (A B : Subspace k V) (hV : finrank k V = 9) (hA : finrank k A = 5) (hB : finrank k B = 5) :
    A ⊓ B ≠ ⊥ := by sorry

/-

Here's some API which you will need for this question. Note that if `A : subspace k V` then
`A` is a term, not a type, and in particular it's not a vector space (it's a vector subspace).
However `↥A`, a "coercion to type", is a type, and hence has a dimension. 

## Some API for finite-dimensional vector spaces

This should be all you need.

`submodule.dim_sup_add_dim_inf_eq A B : finrank k ↥(A ⊔ B) + finrank k ↥(A ⊓ B) = finrank k ↥A + finrank k ↥B`
`submodule.finrank_le A : finrank k ↥A ≤ finrank k V`
`finrank_bot k V : finrank K ↥⊥ = 0`

-/
