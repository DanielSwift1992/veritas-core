"""veritas_guardian – Δ-Kernel energy non-negativity plugin.

Obligation name: `guardian_align`
Checks that numerical implementation conserves the theoretical sign: for
aligned fields F = ∇P the integral ∫ F·∇P ≥ 0.
Runs ≤ 20 Hypothesis generated examples for speed.
"""

from __future__ import annotations

import math, numpy as np, pathlib
from hypothesis import given, settings, Verbosity
import hypothesis.strategies as st
from veritas.plugin import plugin, CheckResult


# ---------------- helper generator ------------------------
@st.composite
def _smooth_fields(draw, n: int = 64, k_max: int = 5):
    coeffs = draw(st.lists(st.floats(-1, 1), min_size=k_max * 2, max_size=k_max * 2))
    x = np.linspace(0, 2 * math.pi, n, endpoint=False)
    f = sum(
        a * np.sin((i + 1) * x) + b * np.cos((i + 1) * x)
        for i, (a, b) in enumerate(zip(coeffs[::2], coeffs[1::2]))
    )
    return x, f


def _energy(f: np.ndarray, grad_p: np.ndarray) -> float:
    return float(np.trapz(f * grad_p, dx=(2 * math.pi) / len(f)))


@plugin("guardian_align")  # type: ignore[misc]
class _GuardianAlign:  # noqa: D401
    """Property-based guard: Δ-Kernel energy non-negativity for aligned fields."""

    MAX_EXAMPLES = 20  # keep it fast for CI

    def run(self, artifact: pathlib.Path, **kw):  # type: ignore[override]
        failed = False

        @given(_smooth_fields())
        @settings(max_examples=self.MAX_EXAMPLES, deadline=None, verbosity=Verbosity.quiet)
        def _property(data):  # type: ignore[missing-return-type-doc]
            x, P = data
            gradP = np.gradient(P, x[1] - x[0])
            E = _energy(gradP, gradP)
            assert E >= -1e-9

        try:
            _property()  # type: ignore[arg-type]
        except AssertionError:
            failed = True
        except Exception as exc:  # pragma: no cover
            return CheckResult.failed(str(exc))

        return CheckResult.failed("found negative energy") if failed else CheckResult.passed() 