/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro hPQ
  rw [hPQ]

example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  ·intro hPQ
   rw [hPQ]
  ·intro hQP
   rw [hQP]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ hQR
  rw [hQR] at hPQ
  exact hPQ

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro hPyQ
    cases' hPyQ with hP hQ
    constructor
    · exact hQ
    · exact hP
  · intro hQyP
    cases' hQyP with hQ hP
    constructor
    · exact hP
    · exact hQ
-- or
example : P ∧ Q ↔ Q ∧ P := by
  constructor <;> --uses the next tactics for every goal
  · intro h
    cases' h with h1 h2
    exact ⟨h2,h1⟩ /-means the proof is the pair (h2,h1)
    it works for a '∧' statement, i don't know about '∨' yet -/

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro h
    cases' h with hPyQ hR
    cases' hPyQ with hP hQ
    exact ⟨hP,hQ,hR⟩
  · intro hPQR
    cases' hPQR with hP hQyR
    cases' hQyR with hQ hR
    exact ⟨⟨hP,hQ⟩, hR⟩
    /- instead of 'exact' we could use
    constructor
    · exact ⟨hP,hQ⟩
    · exact hR
    -/


example : P ↔ P ∧ True := by
  constructor
  · intro hP
    exact ⟨hP, trivial⟩
  · rintro ⟨hP, hT⟩
    exact hP

example : False ↔ P ∧ False := by
  constructor
  · intro hF
    exfalso
    exact hF
  · rintro ⟨hP,hF⟩ /-I don't know why rintro here neither applies assumption afterwards
                    nor let's me write 'rintro h ⟨hP,hF⟩' as before -/
    exact hF
    /-
    intro h
    cases' h with hP hF
    exact hF
-/

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  rintro ⟨hPQ, hQP⟩ ⟨hRS,hSR⟩
  constructor
  · rintro ⟨hP, hR⟩
    constructor
    · apply hPQ
      exact hP
    · apply hRS
      exact hR
--or easier using 'rw' twice, since 'rw' uses 'rfl' afterwards
example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro h1 h2
  rw [h1]
  rw [h2]

example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  by_cases hP : P
  · change P → (P → False) at h1
    apply h1
    exact hP
    exact hP
  · change P → False at hP
    apply hP
    apply h2
    change ¬P at hP
    apply hP
--or
example : ¬(P ↔ ¬P) := by
  intro h
  cases' h with h1 h2
  apply h1
  <;> by_contra hnP
  <;> apply h1
  <;> apply h2
  <;> exact hnP
/- In his solution he uses 'have' which I guess it is like stating a lemma
and proving it inside the big proof, but I didn't want to use that.
Maybe what I came up with is unelegant or something, but it returns 'no goals'-/
