-- EulerLagrange.lean

import Mathlib.Analysis.Calculus.Deriv
open Real

-- Derivative of the 1-D quadratic energy L(q)=q^2/2 is q.
lemma euler_lagrange_placeholder : deriv (fun x : ℝ => (x ^ 2) / 2) 3 = 3 := by
  have : deriv (fun x : ℝ => (x ^ 2) / 2) 3 = (2 * 3) / 2 := by
    simpa using deriv_div_const (f := fun x => x ^ 2) (x := 3) (c := (2:ℝ))
  simpa using this 