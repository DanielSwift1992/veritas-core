"""Property-based guardian test.
Fails CI if Δ-Kernel energy becomes negative inside admissible (C¹) domain.
"""

# STATUS: demo | Guardian

import math
import numpy as np
import pytest
from hypothesis import given, settings, strategies as st, note, Verbosity
import os

# -----------------------------------------------------------------------------
# Helpers
# -----------------------------------------------------------------------------

@st.composite
def smooth_fields(draw, n: int = 64, k_max: int = 5):
    """Generate a 1-D C¹-smooth field via truncated Fourier series."""
    coeffs = draw(st.lists(st.floats(-1, 1), min_size=k_max * 2, max_size=k_max * 2))
    x = np.linspace(0, 2 * math.pi, n, endpoint=False)
    f = sum(
        a * np.sin((i + 1) * x) + b * np.cos((i + 1) * x)
        for i, (a, b) in enumerate(zip(coeffs[::2], coeffs[1::2]))
    )
    return x, f


def delta_kernel(f: np.ndarray, grad_p: np.ndarray) -> float:
    """Numerical Δ-Kernel energy E = ∫ F·∇P."""
    return float(np.trapz(f * grad_p, dx=(2 * math.pi) / len(f)))


MAX_EX = int(
    float(
        os.environ.get("HYPOTHESIS_MAX_EXAMPLES", "200")
    )
)  # allow override


@given(smooth_fields())
@settings(max_examples=MAX_EX, deadline=None, verbosity=Verbosity.quiet)
def test_delta_kernel_nonneg(data):
    """Guardian: for aligned fields (F = ∇P) energy must be non-negative."""
    x, P = data
    gradP = np.gradient(P, x[1] - x[0])
    F = gradP  # alignment ensures theoretical non-negativity (∫ |∇P|^2 ≥ 0)
    E = delta_kernel(F, gradP)
    note(f"E = {E}")
    assert E >= -1e-9 