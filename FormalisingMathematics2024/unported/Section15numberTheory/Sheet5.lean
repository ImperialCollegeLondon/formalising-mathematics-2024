/-
Copyright (c) 2023 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic.Default
import Data.Zmod.Basic


namespace Section15sheet5

/-

# Prove that 19 ∣ 2^(2^(6k+2)) + 3 for k = 0,1,2,... 


This is the fifth question in Sierpinski's book "250 elementary problems
in number theory".

thoughts

if a(k)=2^(2^(6k+2))
then a(k+1)=2^(2^6*2^(6k+2))=a(k)^64

Note that 16^64 is 16 mod 19 according to a brute force calculation
and so all of the a(k) are 16 mod 19 and we're done

-/
theorem sixteen_pow_sixtyfour_mod_nineteen : (16 : ZMod 19) ^ 64 = 16 := by rfl

-- :-)
example (k : ℕ) : 19 ∣ 2 ^ 2 ^ (6 * k + 2) + 3 := by sorry

end Section15sheet5

