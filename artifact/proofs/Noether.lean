-- Noether.lean
-- Energy conservation for the 1-D harmonic oscillator: ẋ = v, v̇ = -x.
-- We show that the Hamiltonian H = x²/2 + v²/2 is constant along the flow.

import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Tactic

open Real

/-- State of the oscillator as a pair (x,v). -/
structure State where
  x : ℝ
  v : ℝ

def H (s : State) : ℝ := (s.x ^ 2 + s.v ^ 2) / 2

/-- ODE RHS. -/
def f (s : State) : State := ⟨s.v, -s.x⟩

/-- Time derivative of the Hamiltonian along the vector field `f` is zero. -/
lemma dH_dt (s : State) :
    (∂ fun t : ℝ => H ⟨s.x + t * s.v, s.v + t * (-s.x)⟩) 0 = 0 := by
  -- Compute derivative symbolically at t = 0
  simp [H, State.mk] using by
    -- derivative of (x+tv)^2 /2 + (v - tx)^2 /2 at t=0
    have : (fun t : ℝ => ((s.x + t * s.v)^2 + (s.v - t * s.x)^2) / 2)'
        0 = 0 := by
      -- expand derivative manually
      have h1 : deriv (fun t => (s.x + t * s.v)^2) 0 = 2 * s.x * s.v := by
        simpa using deriv_pow (fun t => (s.x + t * s.v)) 0 2
      have h2 : deriv (fun t => (s.v - t * s.x)^2) 0 = -2 * s.v * s.x := by
        simpa using
          (by
            have : deriv (fun t => (s.v - t * s.x)^2) 0 =
                2 * (s.v - 0 * s.x) * (-s.x) := by
              simpa using deriv_pow (fun t => (s.v - t * s.x)) 0 2
            simpa using this)
      have : (deriv (fun t => (s.x + t * s.v)^2 + (s.v - t * s.x)^2) 0) = 0 := by
        simpa [h1, h2, add_comm, add_left_neg] using congrArg (fun x => (x)) (by rfl)
      simpa [deriv_mul_const] using this
    simpa [deriv_const] using this

/-- Global statement: along the exact solution the Hamiltonian stays constant. -/
lemma energy_conserved (s : State) (t : ℝ) :
    H ⟨s.x * Real.cos t + s.v * Real.sin t,
        s.v * Real.cos t - s.x * Real.sin t⟩ = H s := by
  -- explicit solution of oscillator and algebraic identity
  simp [H, mul_pow, cos_sq, sin_sq, add_comm, add_left_comm, add_assoc,
        sub_eq, mul_add, add_comm, add_left_neg, two_mul] using by ring 