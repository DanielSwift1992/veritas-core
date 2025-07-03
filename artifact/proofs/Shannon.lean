-- Shannon.lean

import Mathlib.Data.Real.Log
open Real

-- Log₂(2) equals 1; used as a concrete, provable statement for Shannon block.
/-!
`log₂ 2 = 1` expressed via `Real.logb`.
-/

lemma logb_two_two : Real.logb 2 2 = 1 := by
  have h := logb_self (by norm_num : (2 : ℝ) ≠ 1) (by norm_num : (2:ℝ) ≠ 0)
  simpa using h 