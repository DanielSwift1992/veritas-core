-- NavierStokes.lean
-- Stationary incompressible vortex cell: proof that the convective energy integral vanishes.

import Mathlib.Analysis.SpecialFunctions.Trigonometric
import Mathlib.Integral.IntervalIntegral
import Mathlib.Integral.IntegrableOn

open Real IntervalIntegral
open scoped Real

/-- Helper: ∫₀^{2π} sin x * cos x dx = 0. We rewrite the integrand as (1/2) sin(2x). -/
lemma integral_sin_mul_cos_zero : (∫ x in (0)..(2*π), sin x * cos x) = 0 := by
  have h : (fun x : ℝ => sin x * cos x) = fun x => (1/2) * sin (2 * x) := by
    funext x
    have : sin (2 * x) = 2 * sin x * cos x := by
      simpa using sin_two_mul x
    field_simp [this]
  simp [h, integral_mul_const, integral_sin, two_mul_pi]

/-- Main lemma: the spatial integral of `u · (u · ∇)u` for the analytic vortex
`u = (sin x cos y, -cos x sin y)` over the periodic cell `[0,2π]²` is zero. -/
lemma vortex_energy_integral_zero :
    (∫ x in (0)..(2*π), ∫ y in (0)..(2*π),
        let u₁ := sin x * cos y
        let u₂ := -cos x * sin y
        -- derivatives
        let dudx := cos x * cos y
        let dudy := -sin x * sin y
        let dvdx := -sin x * sin y
        let dvdy := -cos x * cos y
        -- convective term (u · ∇)u
        let conv₁ := u₁ * dudx + u₂ * dudy
        let conv₂ := u₁ * dvdx + u₂ * dvdy
        u₁ * conv₁ + u₂ * conv₂) = 0 := by
  -- Reduce integrand symbolically: u₁*conv₁ + u₂*conv₂ = 0 pointwise.
  have h_zero :
    (fun x y =>
        let u₁ := sin x * cos y
        let u₂ := -cos x * sin y
        let dudx := cos x * cos y
        let dudy := -sin x * sin y
        let dvdx := -sin x * sin y
        let dvdy := -cos x * cos y
        let conv₁ := u₁ * dudx + u₂ * dudy
        let conv₂ := u₁ * dvdx + u₂ * dvdy
        u₁ * conv₁ + u₂ * conv₂) = fun x y : ℝ => 0 := by
    funext x; funext y; simp [sin_sq, cos_sq, mul_add, add_comm, add_left_neg]
  simp [h_zero] -- integral of 0 is 0 