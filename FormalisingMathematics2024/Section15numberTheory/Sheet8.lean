/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default
import Data.Zmod.Algebra
import NumberTheory.Wilson


namespace Section15sheet8

open scoped BigOperators

/-

## -1 is a square mod p if p=1 mod 4

I formalise the following constructive proof in the solutions: ((p-1)/2)! works!
Why does it work: claim 1*2*...*(p-1)/2 squared is -1
1*2*....*(p-1)/2 -- p is 1 mod 4 so this is also
-1 * -2 * ... * -((p-1)/2), and mod p this is the same
(p-1) * (p-2) * ... ((p+1)/2), so i^2=1*2*....*(p-2)*(p-1)=(p-1)!
Wilson's theorem tels us that (p-1)! = -1 mod p if p is prime.

-/
theorem exists_sqrt_neg_one_of_one_mod_four (p : ℕ) (hp : p.Prime) (hp2 : ∃ n, p = 4 * n + 1) :
    ∃ i : ZMod p, i ^ 2 = -1 := by sorry

end Section15sheet8

