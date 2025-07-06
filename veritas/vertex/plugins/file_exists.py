"""Fallback plugin: file_exists obligation."""
from __future__ import annotations
import pathlib
from veritas.vertex.plugin_api import BaseCheck, CheckResult

class FileExists(BaseCheck):
    obligation = "file_exists"

    def run(self, artifact: pathlib.Path, **kw):
        return CheckResult.passed() if artifact.exists() else CheckResult.failed("missing") 