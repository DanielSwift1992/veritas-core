-- EnergyBalance.lean

import Mathlib.Analysis.SpecialFunctions.Log
open Real

/-- Landauer **positivity**: for any temperature `T > 0` we have `k_B·T·ln 2 > 0`.  We set Boltzmann constant `k_B = 1` since it is positive and can be absorbed. -/
lemma landauer_pos {T : ℝ} (hT : 0 < T) : 0 < T * log 2 := by
  have hlog : 0 < log 2 := by
    have : (2 : ℝ) > 1 := by norm_num
    exact log_pos this
  have : 0 < (T : ℝ) := hT
  have : 0 < T * log 2 := mul_pos hT hlog
  exact this 