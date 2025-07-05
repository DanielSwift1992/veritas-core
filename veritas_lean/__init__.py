"""veritas_lean – Lean 4 compilation plugin for Veritas."""

from __future__ import annotations

import pathlib, subprocess, re
from veritas.plugin import BaseCheck, CheckResult


class LeanCompile(BaseCheck):
    """Run `lake build` and ensure no `sorry` in Lean sources."""
    obligation = "lean_compile"

    def run(self, artifact: pathlib.Path, **kw):
        proofs_dir = artifact if artifact.is_dir() else artifact.parent
        try:
            subprocess.check_output(["lake", "build"], cwd=proofs_dir, stderr=subprocess.STDOUT)
        except FileNotFoundError:
            return CheckResult.failed("lake not installed")
        except subprocess.CalledProcessError as exc:
            return CheckResult.failed(exc.output.decode(errors="ignore"))

        # Abort if any `sorry` left (exclude lake-packages)
        for lf in proofs_dir.glob("*.lean"):
            if "lake-packages" in lf.parts:
                continue
            if re.search(r"\bsorry\b", lf.read_text()):
                return CheckResult.failed(f"found sorry in {lf}")
        return CheckResult.passed() 