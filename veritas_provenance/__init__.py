"""veritas_provenance – basic data provenance check.

Obligation: produced_by
Edge meta options:
  inputs: list[str]  # paths to input files/dirs relative to repo root

Passes if *all* input paths exist and are **older** than the artifact boundary.
If any input missing or newer, fails.
"""
from __future__ import annotations
import pathlib, os, time
from veritas.plugin import BaseCheck, CheckResult
from typing import Sequence

class ProducedBy(BaseCheck):
    obligation = "produced_by"

    def _mtime(self, p: pathlib.Path) -> float:
        try:
            return p.stat().st_mtime
        except FileNotFoundError:
            return 0.0

    def run(self, artifact: pathlib.Path, *, cfg: dict | None = None, **kw):
        inputs: Sequence[str] = (cfg or {}).get("meta", {}).get("inputs", [])
        if not inputs:
            return CheckResult.failed("no inputs listed")
        boundary_mtime = self._mtime(artifact)
        if boundary_mtime == 0:
            return CheckResult.failed("output missing")
        for inp in inputs:
            p = pathlib.Path(inp)
            if not p.exists():
                return CheckResult.failed(f"input missing: {inp}")
            if self._mtime(p) > boundary_mtime:
                return CheckResult.failed(f"input newer than output: {inp}")
        return CheckResult.passed() 