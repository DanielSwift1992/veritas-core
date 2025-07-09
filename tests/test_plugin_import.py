import textwrap, pathlib, sys, importlib
from veritas.vertex.plugin_api import plugin, discover_plugins

def test_auto_import_kb_plugins(tmp_path, monkeypatch):
    # create package kb_plugins
    pkg = tmp_path / "my_plugins"
    pkg.mkdir()
    (pkg / "__init__.py").write_text(textwrap.dedent("""
        import pathlib
        from veritas.vertex.plugin_api import plugin, BaseCheck, CheckResult
        @plugin("dummy")
        class Dummy(BaseCheck):
            def run(self, artifact: pathlib.Path, **kw):
                return CheckResult.passed()
    """))
    sys.path.insert(0, str(tmp_path))
    graph = tmp_path / "logic-graph.yml"
    graph.write_text(textwrap.dedent("""
    schema: 1
    plugins:
      - ./my_plugins
    nodes:
      - id: a
        type: evidence
        boundary: README.md
    edges:
      - from: a
        to: a
        obligation: dummy
    """))
    (tmp_path/"README.md").write_text("ok")
    from veritas.vertex.engine import run as engine_run
    monkeypatch.chdir(tmp_path)
    summary = engine_run(graph)
    assert summary["checks_failed"] == 0 