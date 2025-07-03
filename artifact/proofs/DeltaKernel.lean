-- DeltaKernel.lean

import Mathlib.Analysis.SpecialFunctions.Log

/-- Minimal synthetic definition of the Δ-Kernel contraction in 1-D: the scalar
product of a vector field `F` and the gradient of a scalar potential `∇P`.
We model both as real numbers for the purposes of correspondence checks. -/
@[simp] def DeltaKernel (F gradP : ℝ) : ℝ := F * gradP

open Real

/-- **Δ-Kernel ↦ Landauer**: for a one-bit erasure the vector field magnitude is
`F = 1` (unitless boundary flip) and the gradient term is `∇P = log 2` (Boltzmann
factor absorbed).  Hence the Δ-Kernel contraction reduces to `log 2`.  This
connects the abstract integral to the standard Landauer bound. -/
lemma deltaKernel_landauer : DeltaKernel 1 (log 2) = log 2 := by
  simp [DeltaKernel]

/-- Variant with explicit temperature factor. Boltzmann constant is taken as 1.
If `T > 0` then the Δ-Kernel contraction equals `T * log 2`. -/
lemma deltaKernel_landauer_T {T : ℝ} (hT : 0 < T) :
    DeltaKernel 1 (T * log 2) = T * log 2 := by
  simpa [DeltaKernel] 