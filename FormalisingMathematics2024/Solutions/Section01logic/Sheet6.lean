/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases'` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

example : P ∨ Q → (P → R) → (Q → R) → R :=
  by
  intro hPoQ hPR hQR
  cases' hPoQ with hP hQ
  · apply hPR
    exact hP
  · exact hQR hQ

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  · right; assumption
  · left; assumption

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro ((hP | hQ) | hR)
    · left; exact hP
    · right; left; exact hQ
    · right; right; exact hR
  · rintro (hP | hQ | hR)
    · left; left; exact hP
    · left; right; exact hQ
    · right; exact hR

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
  by
  rintro hPR hQS (hP | hQ)
  · left; apply hPR; exact hP
  · right; exact hQS hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  intro hPQ h
  cases' h with hP hR
  · left; apply hPQ; exact hP
  · right; exact hR

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
  by
  intro h1 h2
  rw [h1, h2]

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h
    constructor
    · intro hP
      apply h
      left
      exact hP
    · intro hQ
      apply h
      right
      exact hQ
  · rintro ⟨hnP, hnQ⟩ (hP | hQ)
    · apply hnP; exact hP
    · exact hnQ hQ

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h
    by_cases hP : P
    · right
      intro hQ
      apply h
      exact ⟨hP, hQ⟩
    · left
      exact hP
  · rintro (hnP | hnQ) ⟨hP, hQ⟩
    · contradiction
    · apply hnQ; exact hQ
