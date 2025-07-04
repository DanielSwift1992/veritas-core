"""veritas_cite – проверка согласованности ссылок LaTeX/Markdown ↔ Lean proofs.

Obligation name: `cite_consistency`
Ищет все `\cite{Lemma}` или `[@Lemma]`, убеждается, что существует файл
`artifact/proofs/Lemma.lean`.
"""

from __future__ import annotations

import pathlib, re
from veritas.plugin import plugin, CheckResult

_CITE_RE = re.compile(r"\\cite\{([^}]+)\}|\[@([^\]]+)\]")


@plugin("cite_consistency")  # type: ignore[misc]
class _CiteConsistency:  # noqa: D401
    """Validate that every citation of a Lean lemma has corresponding file."""

    def run(self, artifact: pathlib.Path, **kw):  # type: ignore[override]
        base = pathlib.Path("artifact/proofs")
        if not base.exists():
            return CheckResult.failed("artifact/proofs missing")

        text = artifact.read_text(encoding="utf-8", errors="ignore")
        missing: list[str] = []
        for m in _CITE_RE.finditer(text):
            lemma = m.group(1) or m.group(2)
            fname = base / f"{lemma}.lean"
            if not fname.exists():
                missing.append(lemma)
        if missing:
            return CheckResult.failed("missing lemmas: " + ", ".join(missing[:5]))
        return CheckResult.passed() 