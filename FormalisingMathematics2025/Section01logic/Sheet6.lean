/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP
  done

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h =>
    intro hPR hQR
    apply hPR
    exact h
  | inr h =>
    intro hPR hQR
    apply hQR
    exact h

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  intro hPoQ
  cases' hPoQ with hP hQ
  · right
    exact hP
  · left
    exact hQ

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  <;> intro h
  · cases' h with hPoQ hR
    · cases' hPoQ with hP hQ
      · left
        exact hP
      · right
        left
        exact hQ
    · right
      right
      exact hR

  · cases' h with hP hQoR
    · left
      left
      exact hP
    · cases' hQoR with hQ hR
      ·left
       right
       exact hQ
      · right
        exact hR
--I forogot about rintro, could have been shorter
--But this way is more explicit

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  intro hPR hQS hPoQ
  cases' hPoQ with hP hQ
  · left
    apply hPR
    exact hP
  · right
    apply hQS
    exact hQ

example : (P → Q) → P ∨ R → Q ∨ R := by
  rintro hPQ (hP | hR)
  · left
    apply hPQ
    exact hP
  · right
    exact hR


example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  rintro ⟨hPR, hRP⟩ ⟨hQS, hSQ⟩
  constructor
  · rintro (hP | hQ)
    · left
      apply hPR
      exact hP
    · right
      apply hQS
      exact hQ

  · rintro (hR | hS)
    · left
      apply hRP
      exact hR
    · right
      apply hSQ
      exact hS
--or much better using 'rw'
example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  intro hPR hQS
  rw [hPR]
  rw [hQS]

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  constructor
  · intro h1
    --change P ∨ Q → False at h1
    --change (P → False) ∧ (Q → False)
    constructor
    · intro hP
      apply h1
      left
      exact hP
    · intro hQ
      apply h1
      right
      exact hQ

  · intro h2 hPoQ
    --change (P ∨ Q) → False
    --change (P → False) ∧ (Q → False) at h2
    --intro hPoQ
    cases' h2 with hnP hnQ
    cases' hPoQ with hP hQ
    · apply hnP
      exact hP
    · apply hnQ
      exact hQ



example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  constructor
  · intro h1
    by_contra hc
    apply h1
    constructor
    · by_contra hnP
      apply hc
      left
      exact hnP
    · by_contra hnQ
      apply hc
      right
      exact hnQ

  · intro h2 hPyQ
    cases' hPyQ with hP hQ
    cases' h2 with hnP hnQ
    · apply hnP
      exact hP
    · apply hnQ
      exact hQ
