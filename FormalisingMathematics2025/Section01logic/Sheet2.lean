/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 2 : `True` and `False`

We learn about the `True` and `False` propositions.

## Tactics you will need

To solve the levels on this sheet you will need to know all previous
tactics, plus the following two new ones. Check out their explanations
in the course book. Or just try them out and hover over them to see
if you can understand what's going on.

* `trivial`
* `exfalso`

-/


-- Throughout this sheet, `P`, `Q` and `R` will denote propositions.
variable (P Q R : Prop)

example : True := by
  trivial
  done

example : True → True := by
  intro h
  trivial
  done

example : False → True := by
  intro h
  cases h -- quiza mejor usar exfalso y luego exact h o trivial (aunque trivial te lo hace de una)
  done

example : False → False := by
  intro h
  exact h
  done

example : (True → False) → False := by
  intro h1
  apply h1
  trivial
  done

example : False → P := by
  intro h
  exfalso
  exact h
  done

example : True → False → True → False → True → False := by
  intro h1 h2
  exfalso
  exact h2
  done

example : True → False → True → False → True → False := by --mismo que el anterior
  intro h1 h2 h3 h4 h5
  exact h2
  done

example : P → (P → False) → False := by
  intro hP hPF
  apply hPF
  exact hP
  done

example : (P → False) → P → Q := by
  intro hPF hP
  exfalso
  apply hPF
  exact hP
  done

/-
example : (True → False) → P := by
  intro h1
  have h3 : False := by
    apply h1
    trivial
  -- have h2 : True := by
  --   trivial
  -- apply h1 at h2
  exfalso
  exact h3
  -- apply h1
  -- trivial
  -- done
  done

  -/
example : (True → False) → P := by --lo mio
  intro h1
  exfalso
  apply h1
  trivial
  done
example : (True → False) → P := by --tambien vale, trivial te lo hace
  intro h1
  exfalso
  trivial
  done
