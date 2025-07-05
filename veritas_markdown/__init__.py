"""veritas_markdown – минимальный плагин для проверки markdown-файлов.

Obligation name: markdown_nonempty
Проверяет, что файл существует и содержит хотя бы одну строку (или LaTeX-блок)."""

from __future__ import annotations
import pathlib
from veritas.plugin import BaseCheck, CheckResult

class MarkdownNonEmpty(BaseCheck):
    """Проверяет, что markdown-файл не пустой и содержит хотя бы одну формулу или строку."""
    obligation = "markdown_nonempty"
    def run(self, artifact: pathlib.Path, **kw):
        if not artifact.exists():
            return CheckResult.failed("file not found")
        text = artifact.read_text(encoding="utf-8", errors="ignore").strip()
        if not text:
            return CheckResult.failed("file is empty")
        # Можно искать LaTeX-блоки, но для простоты — просто непустой файл
        return CheckResult.passed() 