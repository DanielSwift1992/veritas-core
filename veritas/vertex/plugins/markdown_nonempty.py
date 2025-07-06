"""Fallback plugin: markdown_nonempty obligation.
Passes if file exists and has non-empty content; additionally fails if it contains an empty math block `$$ $$`."""
from __future__ import annotations
import pathlib, re
from veritas.vertex.plugin_api import BaseCheck, CheckResult

_EMPTY_MATH = re.compile(r"\$\$\s*\$\$")

class MarkdownNonEmpty(BaseCheck):
    obligation = "markdown_nonempty"

    def run(self, artifact: pathlib.Path, **kw):
        if not artifact.exists():
            return CheckResult.failed("file missing")
        txt = artifact.read_text(encoding="utf-8", errors="ignore")
        if not txt.strip():
            return CheckResult.failed("markdown empty")
        if _EMPTY_MATH.search(txt):
            return CheckResult.failed("empty $$ $$ block found")
        return CheckResult.passed() 