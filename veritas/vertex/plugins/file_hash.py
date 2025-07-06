"""Plugin: file_hash – verify SHA-256 hash of a file or directory."""
from __future__ import annotations
import pathlib, hashlib
from typing import Any
from veritas.vertex.plugin_api import BaseCheck, CheckResult

class FileHash(BaseCheck):
    obligation = "file_hash"

    def _sha256(self, path: pathlib.Path) -> str:
        if path.is_file():
            return hashlib.sha256(path.read_bytes()).hexdigest()
        if path.is_dir():
            h = hashlib.sha256()
            for p in sorted(path.rglob("*")):
                if p.is_file():
                    h.update(p.read_bytes())
            return h.hexdigest()
        return ""

    def run(self, artifact: pathlib.Path, *, cfg: dict | None = None, **kw: Any) -> CheckResult:
        expected = cfg.get("expected") if cfg else None
        actual = self._sha256(artifact)
        if expected and actual != expected:
            return CheckResult.failed(f"hash mismatch {actual} ≠ {expected}")
        return CheckResult.passed() 