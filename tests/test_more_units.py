import os, textwrap, pathlib, sys, importlib
import pytest
from collections import Counter

from veritas.vertex import env_gen
from veritas.vertex import bus
from veritas.vertex.plugins.file_hash import FileHash
from veritas.vertex.plugins.yaml_schema import YamlSchema
from veritas.vertex._util import render_stats

from typer.testing import CliRunner
from veritas.vertex.cli import app


def test_env_generate_conda(tmp_path, monkeypatch):
    # create fake requirements.txt
    req = tmp_path / "requirements.txt"
    req.write_text("pyyaml==6.0\n# comment\n")
    # Monkeypatch ROOT so env_gen finds requirements
    monkeypatch.setattr(env_gen, "ROOT", tmp_path, raising=False)
    content = env_gen.generate_conda_yaml()
    assert "pyyaml==6.0" in content


def test_bus_subscribe_publish(capsys):
    collected = {}
    def _listener(data):
        collected.update(data)
    bus.subscribe("stats.ready", _listener)
    bus.publish("stats.ready", {"value": 42})
    assert collected == {"value": 42}


def test_file_hash_directory(tmp_path):
    d = tmp_path / "dir"
    d.mkdir()
    (d / "a.txt").write_text("A")
    (d / "b.txt").write_text("B")
    plugin = FileHash()
    expected = plugin._sha256(d)
    assert plugin.run(d, cfg={"expected": expected})


def test_yaml_schema_basic(tmp_path, monkeypatch):
    yml = tmp_path / "data.yml"
    yml.write_text("foo: bar")
    plugin = YamlSchema()
    # ensure jsonschema absent to test fallback path
    monkeypatch.setitem(sys.modules, "jsonschema", None)
    res = plugin.run(yml)
    assert res


def test_util_render_stats_missing_jinja(monkeypatch, capsys):
    stats = {"n_nodes":0, "n_edges":0, "density":0, "diameter":"∞", "kinds": Counter(), "self_pct":1.0, "cross_refs":0}
    monkeypatch.setitem(sys.modules, "jinja2", None)
    result = render_stats(stats, json_out=False, template=None, pretty=False)
    # pretty path prints
    out, _ = capsys.readouterr()
    assert "Nodes:" in out


def test_cli_env_conda(tmp_path, monkeypatch):
    monkeypatch.chdir(tmp_path)
    content = env_gen.generate_conda_yaml()
    (tmp_path / "env.yml").write_text(content)
    runner = CliRunner()
    result = runner.invoke(app, ["env", "--conda"])
    assert result.exit_code == 0 