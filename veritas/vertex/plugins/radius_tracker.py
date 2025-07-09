from __future__ import annotations

"""RadiusTracker – computes trust score S and radius R.

Reference plugin for Principle P-4 metrics. This module must live under
`veritas.vertex.plugins` so that the built-in discovery finds it without
entry-points.
"""

import math, time
from typing import Any, Dict

import pathlib
from veritas.vertex.plugin_api import BaseCheck, CheckResult


class RadiusTracker(BaseCheck):
    """Derive new trust score and autonomy radius for ``actor``.

    Expected ``edge.meta`` keys:
        actor: str              – human/service identifier
        delta_value: float      – ΔV (value produced)
        delta_cost: float       – ΔD (resources spent)
        stability: float = 1.0  – σ  (0-1 share tasks w/o collapse)
        risk: float = 1.0       – ρ  (discount for high-risk changes)
        lambda_decay: float = .03 – λ  (forgetting per day)
        k_factor: float = 5.0   – culture scaling constant
        prev_score: float = 0.0 – S_{t-1} (passed from storage)
    """

    obligation = "radius_tracker"

    # BaseCheck protocol allows any *artifact*; we ignore for scoring.
    def run(
        self,
        artifact: pathlib.Path | None = None,
        *,
        actor: str,
        delta_value: float,
        delta_cost: float,
        stability: float = 1.0,
        risk: float = 1.0,
        lambda_decay: float = 0.03,
        k_factor: float = 5.0,
        prev_score: float = 0.0,
        **kw: Any,
    ) -> CheckResult:
        # Validate basic ranges -------------------------------------------------
        if delta_cost <= 0:
            return CheckResult.failed("delta_cost must be positive")
        if not (0 <= stability <= 1):
            return CheckResult.failed("stability σ must be within [0,1]")
        if not (0 < risk <= 1):
            return CheckResult.failed("risk ρ must be in (0,1]")

        # Decay previous score (assumed 1-day interval for demo) ----------------
        s_prev = max(prev_score, 0.0)
        s_decayed = s_prev * math.exp(-lambda_decay)

        # Instant contribution ---------------------------------------------------
        s_instant = (risk * delta_value / delta_cost) * stability
        s_new = s_decayed + s_instant

        radius = k_factor * math.log1p(s_new)

        payload: Dict[str, Any] = {
            "actor": actor,
            "trust_score": round(s_new, 4),
            "radius": round(radius, 3),
            "timestamp": int(time.time()),
        }

        import json as _json
        return CheckResult.passed(details=_json.dumps(payload)) 