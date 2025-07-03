"""Search for Δ-Kernel counter-examples *outside* the admissible C¹ domain.

This script is **non-blocking**: it never exits with non-zero status.  Instead, it
logs any discovered outside-domain cases into `cases_outside.json` so that reviewers
see what kinds of inputs break the positivity proof once smoothness assumptions are
violated.
"""
from __future__ import annotations

import json
import math
import os
import random
import sys
from datetime import datetime
from pathlib import Path
from typing import List, Dict, Any

import numpy as np

ROOT = Path(__file__).resolve().parents[2]
OUT_FILE = Path(__file__).with_name("cases_outside.json")
SAMPLES = int(os.environ.get("DISPROOF_SAMPLES", "50"))
np.random.seed(0)
random.seed(0)

def delta_kernel(f: np.ndarray, grad_p: np.ndarray) -> float:
    return float(np.trapz(f * grad_p, dx=(2 * math.pi) / len(f)))


def gen_nonsmooth_field(n: int = 64) -> np.ndarray:
    """Generate a field with potential discontinuity (piecewise constant)."""
    splits = sorted(random.sample(range(1, n - 1), k=random.randint(1, 4)))
    vals = np.random.uniform(-1, 1, size=len(splits) + 1)
    arr = np.empty(n)
    idx0 = 0
    for v, idx1 in zip(vals, splits + [n]):
        arr[idx0:idx1] = v
        idx0 = idx1
    return arr


def second_derivative_norm(a: np.ndarray) -> float:
    return float(np.max(np.abs(np.diff(a, n=2))))


def main() -> None:
    existing: Dict[str, Any] = {}
    if OUT_FILE.exists():
        try:
            existing = json.loads(OUT_FILE.read_text())
        except Exception:
            pass
    existing.setdefault("outside_cases", [])

    new_cases: List[Dict[str, Any]] = []

    x = np.linspace(0, 2 * math.pi, 64, endpoint=False)
    for _ in range(SAMPLES):
        F = gen_nonsmooth_field()
        P = gen_nonsmooth_field()
        gradP = np.gradient(P, x[1] - x[0])
        sd_norm = second_derivative_norm(F) + second_derivative_norm(P)
        if sd_norm < 5:  # still roughly smooth → skip
            continue
        E = delta_kernel(F, gradP)
        if E < -1e-3:  # genuine negativity
            case = {
                "E": E,
                "F_head": list(map(float, F[:5])),
                "P_head": list(map(float, P[:5])),
            }
            new_cases.append(case)

    if not new_cases:
        print("[disproof] No new outside-domain counter-examples found.")
    else:
        print(f"[disproof] Found {len(new_cases)} outside-domain cases (logged)")
        existing["outside_cases"].extend(new_cases)
        existing["updated_at"] = datetime.utcnow().isoformat() + "Z"
        OUT_FILE.write_text(json.dumps(existing, indent=2))


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print(f"[disproof] finder failed: {e}", file=sys.stderr) 