-- STATUS: full | Guardian
-- Guardian.lean : Relates positivity assumption to DeltaKernel non-negativity

import DeltaKernel
open Real

/-- If the product F * ∇P is non-negative, their Δ-Kernel energy is also non-negative.
    This provides a logical link used by the property-based *guardian* test. -/
lemma guardian_nonneg {F ∇P : ℝ}
    (h : 0 ≤ F * ∇P) : 0 ≤ DeltaKernel F ∇P := by
  simpa [DeltaKernel] using h 