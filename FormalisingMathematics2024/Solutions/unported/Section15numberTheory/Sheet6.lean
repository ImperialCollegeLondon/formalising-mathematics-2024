import Mathlib.Tactic.Default
import Data.Zmod.Basic
import FieldTheory.Finite.Basic
import Data.Nat.PrimeNormNum


/-

# Prove the theorem, due to Kraichik, asserting that 13|2^70+3^70

This is the sixth question in Sierpinski's book "250 elementary problems
in number theory".

-/
/-

# Prove the theorem, due to Kraichik, asserting that 13|2^70+3^70

This is the sixth question in Sierpinski's book "250 elementary problems
in number theory".

-/
example : 13 ∣ 2 ^ 70 + 3 ^ 70 :=
  by
  -- use a computer algebra package to work out (2^70+3^70)/13
  use 192550423461109399456637645953021
  norm_num

-- Here is a more honest proof, using Fermat's Little Theorem
example : 13 ∣ 2 ^ 70 + 3 ^ 70 :=
  by
  -- reduce to a question about `zmod 13`
  rw [← ZMod.nat_cast_zmod_eq_zero_iff_dvd]
  -- get rid of the arrows
  push_cast
  -- oops that did some weird stuff
  -- fix up the goal
  change (2 : ZMod 13) ^ 70 + (3 : ZMod 13) ^ 70 = 0
  have h0 : Nat.Prime 13 := by norm_num
  haveI : Fact (Nat.Prime 13) := ⟨h0⟩
  -- apply Fermat's Little Theorem
  have h1 : (2 : ZMod 13) ^ 12 = 1 :=
    by
    apply ZMod.pow_card_sub_one_eq_one
    intro h2
    have h3 : ((2 : ℕ) : ZMod 13) = 0
    assumption_mod_cast
    rw [ZMod.nat_cast_zmod_eq_zero_iff_dvd] at h3 
    revert h3
    norm_num
  -- For 3 we can do better
  have h2 : (3 : ZMod 13) ^ 3 = 1
  rfl
  -- use `conv` mode to rewrite the `70`s in the goal
  conv_lhs =>
    congr
    rw [show 70 = 12 * 5 + 10 by norm_num]
    skip
    rw [show 70 = 3 * 23 + 1 by norm_num]
  -- now use Fermat's Little Theorem to simplify
  rw [pow_add, pow_add, pow_mul, pow_mul, h1, h2]
  simp
  -- We still have to work out 2^10 though, so 
  -- in some sense we're still doing a calculation, just
  -- a smaller one
  norm_num
  rfl

-- lol, funny way to finish (these are numbers mod 13)
