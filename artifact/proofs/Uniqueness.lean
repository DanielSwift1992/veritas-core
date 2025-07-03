-- Uniqueness.lean

import Mathlib.Algebra.Algebra.Basic
 
-- A basic algebraic lemma: squares are non-negative over ℝ.
/-!
The square of any real number is non-negative.
-/

lemma square_nonneg (x : ℝ) : 0 ≤ x ^ 2 := by
  have h : 0 ≤ x * x := mul_self_nonneg x
  simpa [pow_two] using h 