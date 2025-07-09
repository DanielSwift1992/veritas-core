# pragma: no cover – handle missing optional dep
import importlib, pytest, textwrap

from veritas.vertex.cli import app

if importlib.util.find_spec("typer") is None:
    pytest.skip("typer not installed", allow_module_level=True)

from typer.testing import CliRunner

def test_cli_ask_json(tmp_path, monkeypatch):
    cfg = tmp_path / "logic-graph.yml"
    cfg.write_text(textwrap.dedent("""
    schema: 1
    nodes: []
    edges: []
    """))
    monkeypatch.chdir(tmp_path)
    runner = CliRunner()
    result = runner.invoke(app, ["ask", "--json"])
    assert result.exit_code == 0
    assert '"n_nodes": 0' in result.stdout 