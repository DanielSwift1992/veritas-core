-- Control.HJB.lean

import Mathlib.Analysis.Calculus.Deriv
 
/-- Derivative of a constant function is zero: simple lemma used as HJB placeholder. -/
lemma hjb_placeholder : deriv (fun x : ℝ => (1 : ℝ)) 0 = 0 := by
  simpa using deriv_const (c := (1 : ℝ)) 