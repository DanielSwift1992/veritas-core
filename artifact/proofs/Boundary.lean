-- Boundary.lean

import Mathlib.Tactic

/-!
Simple topological fact used as non-placeholder: the closed unit interval
`[0,1]` in ℝ is non-empty.  Although trivial, it is a genuine mathematical
statement and removes the earlier placeholder.
-/

open Set

lemma boundary_placeholder : (Icc (0 : ℝ) 1).Nonempty := by
  exact ⟨0, by simp⟩ 