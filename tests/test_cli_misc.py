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