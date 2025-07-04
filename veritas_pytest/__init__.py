"""veritas_pytest – external plugin package providing 'pytest' obligation.

Installed as extra; in demo repository bundled as source tree.
"""

from __future__ import annotations

import pathlib, subprocess, sys
from veritas.plugin import plugin, CheckResult


@plugin("pytest")  # type: ignore[misc]
class _PytestPlugin:  # noqa: D401
    """Run pytest on the given directory or single test file."""

    def run(self, artifact: pathlib.Path, **kw):  # type: ignore[override]
        target = artifact if artifact.is_dir() else artifact.parent
        cmd = [sys.executable, "-m", "pytest", "-q", str(target)]
        try:
            subprocess.check_output(cmd, stderr=subprocess.STDOUT)
            return CheckResult.passed()
        except subprocess.CalledProcessError as exc:
            return CheckResult.failed(exc.output.decode(errors="ignore")) 