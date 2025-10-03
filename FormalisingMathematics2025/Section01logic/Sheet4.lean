/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 4 : "and" (`∧`)

We learn about how to manipulate `P ∧ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics:

* `cases`
* `constructor`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : P ∧ Q → P := by
  intro h
  cases h with
  | intro left right => exact left
  done

example : P ∧ Q → Q := by
  intro h
  cases' h with hP hQ
  exact hQ

example : (P → Q → R) → P ∧ Q → R := by
  intro hPQR hPyQ
  cases' hPyQ with hP hQ
  apply hPQR
  · exact hP
  · exact hQ

example : P → Q → P ∧ Q := by
  intro hP hQ
  constructor <;> assumption
  -- · assumption
  -- · assumption
  done

/-- `∧` is symmetric -/
example : P ∧ Q → Q ∧ P := by
  intro h
  cases' h with hP hQ
  constructor <;> assumption

example : P → P ∧ True := by
  intro h
  constructor
  exact h
  trivial

example : False → P ∧ False := by
  intro h
  exfalso
  exact h

/-- `∧` is transitive -/
example : P ∧ Q → Q ∧ R → P ∧ R := by
  intro hPyQ hQyR
  constructor
  · cases' hPyQ with hP hQ
    exact hP
  · cases' hQyR with hQ hR
    exact hR


example : (P ∧ Q → R) → P → Q → R := by
  intro h1 hP hQ
  apply h1
  constructor
  · exact hP
  · exact hQ
