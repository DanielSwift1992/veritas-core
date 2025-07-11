# Veritas Cookbook — From "What-if?" to `obligation`

*A concise collection of mini-recipes that show how to turn real-world reliability & compliance questions into Veritas edges plus minimal plugins.*

---

## Quick pattern

1. Formulate a **What-if question** (risk, SLO breach, policy rule).
2. Identify which **objects** participate (source / target nodes).
3. Add **one row** to `logic-graph.yml`.
4. Write a tiny plugin (often < 30 LoC) that returns `passed()` / `failed(reason)`.

> 📖  See also: `docs/POSITIONING.md` for the business value of this pattern.

---

## Recipes

> Feel free to copy-paste & adjust. Each example stands on its own.

### 1  Limit JavaScript bundle size (< 500 KB)

Edge snippet:
```yaml
- from: ui_bundle.js
  to: ui_bundle.js
  obligation: bundle_size_max
  meta:
    limit_kb: 500
```
Plugin skeleton:
```python
from veritas.vertex.plugin_api import BaseCheck, CheckResult
import pathlib, os

class BundleSizeMax(BaseCheck):
    obligation = "bundle_size_max"

    def run(self, artifact: pathlib.Path, *, limit_kb: int, **kw):
        size_kb = os.stat(artifact).st_size / 1024
        return (CheckResult.passed()
                if size_kb <= limit_kb
                else CheckResult.failed(f"{size_kb:.0f} KB > {limit_kb} KB"))
```
---

### 2  P95 latency SLO (< 200 ms)

Edge snippet:
```yaml
- from: api_service
  to: api_service
  obligation: promql_latency_p95
  meta:
    threshold_ms: 200
```
Conceptual plugin (pseudo-code):
```python
class PromQLLatencyP95(BaseCheck):
    obligation = "promql_latency_p95"

    def run(self, artifact: str, *, threshold_ms: int, query: str | None = None, **kw):
        latency = prom_api(query or f"histogram_quantile(0.95, rate(http_request_duration_seconds_bucket{{service='{artifact}'}}[5m]))") * 1000
        return (CheckResult.passed()
                if latency <= threshold_ms
                else CheckResult.failed(f"p95 {latency:.1f} ms > {threshold_ms} ms"))
```
---

### 3  Forbid specific import

Edge snippet:
```yaml
- from: service_a
  to: service_a
  obligation: forbid_import
  meta:
    forbidden: module_b
```
Minimal plugin idea:
```python
class ForbidImport(BaseCheck):
    obligation = "forbid_import"

    def run(self, artifact: pathlib.Path, *, forbidden: str, **kw):
        import ast
        tree = ast.parse(artifact.read_text())
        for node in ast.walk(tree):
            if isinstance(node, (ast.Import, ast.ImportFrom)) and any(alias.name == forbidden for alias in node.names):
                return CheckResult.failed(f"illegal import of {forbidden}")
        return CheckResult.passed()
```
---

## MDR: Flow + Dissipation

MDR is the core trust invariant in Veritas: every obligation (flow) must be checked, and dissipation (cycles, entropy) must be controlled. For the full theory and mathematical background, see [docs/MDR.md](MDR.md).

- **Flow**: Checking obligations through the graph (edges).
- **Dissipation**: Controlling cycles, self-checks, radius, entropy via plugins.

### Example: Plugin for dissipation_check
```