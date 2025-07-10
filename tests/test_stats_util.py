import json, pathlib, sys, textwrap
from typer.testing import CliRunner
import veritas.vertex.stats as vstats
from veritas.vertex import _util
from veritas.kernel import graph as kgraph
from collections import Counter
import pytest

def _make_graph(nodes, edges):
    return kgraph.Graph1(nodes, edges)

def test_stats_empty_graph():
    g = _make_graph({}, [])
    res = vstats.analyse(g)
    assert res["n_nodes"] == 0
    assert res["n_edges"] == 0
    assert res["diameter"] == "∞"


def test_stats_single_node_self_edge():
    g = _make_graph({"a": {"id": "a"}}, [{"from": "a", "to": "a", "obligation": "file_exists"}])
    res = vstats.analyse(g)
    assert res["n_nodes"] == 1
    assert res["density"] == 0


def test_render_stats_template(monkeypatch, tmp_path, capsys):
    stats = {"foo": 1}
    tpl = tmp_path / "tpl.j2"
    tpl.write_text("foo={{ stats.foo }}")
    try:
        import jinja2
    except ImportError:
        pytest.skip("jinja2 not installed")
    _util.render_stats(stats, json_out=False, template=tpl, pretty=False)
    out, _ = capsys.readouterr()
    assert "foo=1" in out

def test_render_stats_json(monkeypatch, capsys):
    stats = {"foo": 1}
    _util.render_stats(stats, json_out=True, template=None, pretty=False)
    out, _ = capsys.readouterr()
    import json
    assert json.loads(out) == stats

def test_render_stats_pretty(capsys):
    stats = {"n_nodes": 0, "n_edges": 0, "density": 0, "diameter": "∞", "kinds": Counter(), "self_pct": 1.0, "cross_refs": 0}
    _util.render_stats(stats, json_out=False, template=None, pretty=True)
    out, _ = capsys.readouterr()
    # pretty output should contain "Nodes:" line
    assert "Nodes:" in out 

def test_stats_with_timings():
    g = _make_graph({"a": {"id": "a"}, "b": {"id": "b"}}, [{"from": "a", "to": "b", "obligation": "x"}])
    timings = {"x": 1.23}
    res = vstats.analyse(g, timings)
    assert "timings" in res 