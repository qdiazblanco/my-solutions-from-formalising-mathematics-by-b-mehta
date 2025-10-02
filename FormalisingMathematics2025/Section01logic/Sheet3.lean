/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- import all the tactics

/-!

# Logic in Lean, example sheet 3 : "not" (`¬`)

We learn about how to manipulate `¬ P` in Lean.

# The definition of `¬ P`

In Lean, `¬ P` is *defined* to mean `P → False`. So `¬ P` and `P → false`
are *definitionally equal*. Check out the explanation of definitional
equality in the "equality" section of Part 1 of the course notes:
https://b-mehta.github.io/formalising-mathematics-notes/

## Tactics

You'll need to know about the tactics from the previous sheets,
and the following tactics may also be useful:

* `change`
* `by_contra`
* `by_cases`

-/

-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : ¬True → False := by
  intro hnT
  change True → False at hnT
  apply hnT
  trivial

example : False → ¬True := by
  intro hF
  by_contra hT
  exact hF

example : ¬False → True := by
  intro hnF
  by_contra hnT
  change True → False at hnT
  apply hnT
  trivial

example : False → ¬P := by
  intro hF
  exfalso
  exact hF
--or
example : False → ¬P := by
  intro hF
  by_contra hP
  exact hF

example : P → ¬P → False := by
  intro hP hnP
  change P → False at hnP
  apply hnP
  exact hP

example : P → ¬¬P := by
  intro hP
  change ¬P → False
  intro hnP
  change P → False at hnP
  apply hnP
  exact hP

example : (P → Q) → ¬Q → ¬P := by
  intro hPQ hnQ
  change Q → False at hnQ
  by_contra hP
  apply hnQ
  apply hPQ
  exact hP

example : ¬¬False → False := by
  intro hnnF
  change ¬False → False at hnnF
  apply hnnF
  by_contra hF
  exact hF

example : ¬¬P → P := by
  intro hnnP
  change ¬ P → False at hnnP
  by_contra hnP
  apply hnnP
  exact hnP

example : (¬Q → ¬P) → P → Q := by
  intro h1 hP
  by_contra hnQ
  apply h1 at hnQ
  change P → False at hnQ
  apply hnQ
  exact hP
-- I could have used "exact hnQ hP" after apply and nothing else
