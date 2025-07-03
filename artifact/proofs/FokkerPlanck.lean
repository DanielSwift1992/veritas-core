-- FokkerPlanck.lean
-- Entropy monotonicity for 1-D Ornstein–Uhlenbeck process (Gaussian PDFs).
-- We show that differential entropy H(σ) = (1/2) log(2πe σ²) has positive
-- derivative for σ > 0, hence entropy grows as variance increases.

import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Analysis.SpecialFunctions.Log

open Real

/-- Differential entropy of a centred 1-D Gaussian with std `σ`. -/
noncomputable def H (σ : ℝ) : ℝ := (Real.log (2 * Real.pi * Real.exp 1 * σ ^ 2)) / 2

lemma deriv_H (σ : ℝ) (hσ : 0 < σ) :
    deriv H σ = 1 / σ := by
  -- H(σ) = (1/2) * log (c * σ^2) where c = 2πe.
  have : H = fun s : ℝ => (1/2) * Real.log (2 * Real.pi * Real.exp 1) + Real.log s := by
    funext s; simp [H, log_mul, mul_comm, pow_two, log_pow, hσ.ne'] using by
      have : (2 * Real.pi * Real.exp 1) > 0 := by
        have : (0:ℝ) < 2 * Real.pi := by positivity
        have : (0:ℝ) < Real.exp 1 := by positivity
        positivity
  -- derivative of constant + log s is 1/s.
  have h_deriv : deriv (fun s : ℝ => (1 / (2:ℝ)) * Real.log (2 * Real.pi * Real.exp 1) + Real.log s) σ = 1 / σ := by
    have : deriv (fun s : ℝ => Real.log s) σ = 1 / σ := by
      simpa using deriv_log hσ.ne'
    simpa [deriv_const, this] using deriv_add_const (fun s : ℝ => Real.log s) ((1 / (2:ℝ)) * Real.log (2 * Real.pi * Real.exp 1)) σ
  simpa [this] using h_deriv

/-- Entropy production is non-negative when variance grows (`σ' > 0`). -/
lemma entropy_deriv_nonneg {σ σ' : ℝ} (hσ : 0 < σ) (hσ' : 0 < σ') :
    0 < (deriv H σ) * σ' := by
  have : deriv H σ = 1 / σ := deriv_H σ hσ
  have hpos : 0 < 1 / σ := by
    have : 0 < σ := hσ
    positivity
  have : 0 < (1 / σ) * σ' := mul_pos hpos hσ'
  simpa [this] using this 