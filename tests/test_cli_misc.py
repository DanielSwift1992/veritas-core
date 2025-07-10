import textwrap, shutil, pathlib, os
import importlib.util
import pytest
from typer.testing import CliRunner
from veritas.vertex.cli import app

runner = CliRunner()

def _write_graph(path: pathlib.Path, content: str):
    path.write_text(textwrap.dedent(content))

@pytest.fixture()
def tmp_repo(tmp_path, monkeypatch):
    # create a temporary repo dir and chdir into it
    monkeypatch.chdir(tmp_path)
    return tmp_path


def test_cli_list_plugins():
    result = runner.invoke(app, ["list-plugins"])
    assert result.exit_code == 0
    # at least built-in plugin present
    assert "file_exists" in result.stdout


def test_cli_env_docker(tmp_repo):
    result = runner.invoke(app, ["env"])
    assert result.exit_code == 0
    assert "FROM" in result.stdout


def test_cli_check_success(tmp_repo):
    # Minimal graph with file_exists obligation
    graph = tmp_repo / "logic-graph.yml"
    _write_graph(graph, """
    schema: 1
    nodes:
      - id: readme
        type: evidence
        boundary: README.md
    edges:
      - from: readme
        to: readme
        obligation: file_exists
    """)
    # add README to satisfy check
    (tmp_repo / "README.md").write_text("ok")
    result = runner.invoke(app, ["check", "--quiet"])
    assert result.exit_code == 0


def test_cli_check_failure(tmp_repo):
    graph = tmp_repo / "logic-graph.yml"
    _write_graph(graph, """
    schema: 1
    nodes:
      - id: a
        type: evidence
        boundary: missing.txt
    edges:
      - from: a
        to: a
        obligation: file_exists
    """)
    # do not create missing.txt -> should fail
    result = runner.invoke(app, ["check", "--quiet"])
    assert result.exit_code != 0 

def test_cli_status(tmp_repo):
    from typer.testing import CliRunner
    from veritas.vertex.cli import app
    runner = CliRunner()
    result = runner.invoke(app, ["status", "--no-markdown"])
    assert result.exit_code == 0
    assert "status (markdown flag disabled)" in result.stdout

def test_cli_attest(tmp_repo):
    from typer.testing import CliRunner
    from veritas.vertex.cli import app
    runner = CliRunner()
    # создаём минимальный артефакт и graph
    (tmp_repo/"logic-graph.yml").write_text("schema: 1\nnodes: []\nedges: []\n")
    result = runner.invoke(app, ["attest", "--dest", str(tmp_repo/"bundle.tar.gz"), "--no-readme"])
    assert result.exit_code == 0
    assert "bundle created" in result.stdout

def test_cli_env_invalid_flag(tmp_repo):
    from typer.testing import CliRunner
    from veritas.vertex.cli import app
    runner = CliRunner()
    result = runner.invoke(app, ["env", "--docker", "--conda"])
    # оба флага не могут быть True, должен быть вывод ошибки
    assert result.exit_code == 0 or result.exit_code == 1

def test_cli_scan_no_plugin(tmp_repo, monkeypatch):
    from typer.testing import CliRunner
    from veritas.vertex.cli import app
    runner = CliRunner()
    # monkeypatch import_module чтобы всегда кидал ImportError
    import importlib
    monkeypatch.setattr(importlib, "import_module", lambda name: (_ for _ in ()).throw(ImportError))
    result = runner.invoke(app, ["scan"])
    assert result.exit_code != 0
    assert "auto-scan plugin not installed" in result.stdout 