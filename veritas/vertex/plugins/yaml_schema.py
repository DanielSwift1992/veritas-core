"""Plugin: yaml_schema – validate YAML file (optionally against JSON Schema)."""
from __future__ import annotations
import pathlib, json, yaml
from typing import Any

try:
    import jsonschema
except ImportError:  # pragma: no cover
    jsonschema = None  # type: ignore

from veritas.vertex.plugin_api import BaseCheck, CheckResult

class YamlSchema(BaseCheck):
    obligation = "yaml_schema"

    def run(self, artifact: pathlib.Path, *, cfg: dict | None = None, **kw: Any) -> CheckResult:  # noqa: D401
        try:
            data = yaml.safe_load(artifact.read_text())
            schema_path = cfg.get("schema") if cfg else None
            if schema_path:
                if jsonschema is None:
                    return CheckResult.failed("jsonschema not installed")
                try:
                    schema = json.loads(pathlib.Path(schema_path).read_text())
                except Exception as exc:
                    return CheckResult.failed(f"schema read error: {exc}")
                try:
                    jsonschema.validate(data, schema)  # type: ignore[arg-type]
                except Exception as exc:
                    return CheckResult.failed(str(exc))
            return CheckResult.passed()
        except Exception as exc:
            return CheckResult.failed(str(exc)) 