-- STATUS: full | Boundary
-- Boundary.lean

import Mathlib.Tactic

/-!
Basic topological fact: the closed unit interval `[0,1]` in ℝ is non-empty.
-/

open Set

lemma boundary_nonempty : (Icc (0 : ℝ) 1).Nonempty := by
  exact ⟨0, by simp⟩ 