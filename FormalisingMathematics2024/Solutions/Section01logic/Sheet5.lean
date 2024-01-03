/-
Copyright (c) 2022 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author : Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `refl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro h
  rw [h]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor <;>
    · intro h
      rw [h]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro h1 h2
-- rwa is rw + assumption
  rwa [h1]

example : P ∧ Q ↔ Q ∧ P := by
  constructor <;>
    · rintro ⟨h1, h2⟩
      exact ⟨h2, h1⟩

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h
    cases' h with hPaQ hR
    cases' hPaQ with hP hQ
    constructor
    · exact hP
    · constructor
      · exact hQ
      · exact hR
  · rintro ⟨hP, hQ, hR⟩
    exact ⟨⟨hP, hQ⟩, hR⟩

example : P ↔ P ∧ True := by
  constructor
  · intro hP
    constructor
    · exact hP
    · triv
  · rintro ⟨hP, -⟩
    exact hP

example : False ↔ P ∧ False := by
  constructor
  · rintro ⟨⟩
  · rintro ⟨-, ⟨⟩⟩

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) :=
  by
  intro h1 h2
  rw [h1]
  rw [h2]

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  by_cases hP : P
  · apply h1 <;> assumption
  · apply hP
    apply h2
    exact hP

-- constructive proof
example : ¬(P ↔ ¬P) := by
  intro h
  have hnP : ¬P := by
    cases' h with h1 h2
    intro hP
    apply h1 <;> assumption
  apply hnP
  rw [h]
  exact hnP
