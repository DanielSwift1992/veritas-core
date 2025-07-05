# Writing a Veritas Plugin in ≤ 50 LOC

Example: check that a Markdown file is non-empty.

```python
from __future__ import annotations
import pathlib
from veritas.plugin import BaseCheck, CheckResult

class MarkdownNonEmpty(BaseCheck):
    """Fail if the file is missing or blank."""
    def run(self, artifact: pathlib.Path, **kw):
        if not artifact.exists():
            return CheckResult.failed("file missing")
        if not artifact.read_text().strip():
            return CheckResult.failed("file is empty")
        return CheckResult.passed()
```

Для плагинов внутри самого репозитория **pyproject.toml не нужен** — ядро Veritas импортирует любой модуль `veritas_*` и автоматически регистрирует класс, если у него есть строковый атрибут `obligation`.

That's it: `logic-graph.yml` can now use `obligation: markdown_nonempty`. 