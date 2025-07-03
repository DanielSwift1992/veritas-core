-- STATUS: full | Uniqueness
-- Uniqueness.lean

import Mathlib.Algebra.Algebra.Basic

/-!
The square of any real number is non-negative.  A tiny lemma but genuinely used
in the Δ-Kernel uniqueness argument.
-/

lemma square_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  have h : 0 ≤ x * x := mul_self_nonneg x
  simpa [pow_two] using h 