import textwrap
import pathlib
import shutil
import os
import sys

repo_root = pathlib.Path(__file__).resolve().parents[1]
# package now resides at repo_root / "veritas"
if str(repo_root) not in sys.path:
    sys.path.insert(0, str(repo_root))

from veritas.vertex.engine import run as engine_run

def test_engine_minimal(tmp_path):
    # create minimal graph file
    cfg = tmp_path / "logic-graph.yml"
    cfg.write_text(textwrap.dedent("""
    schema: 1
    nodes:
      - id: a
        type: evidence
        boundary: README.md
    edges:
      - from: a
        to: a
        obligation: file_exists
    """))
    # copy README to temp dir to satisfy boundary
    shutil.copyfile(repo_root / "README.md", tmp_path / "README.md")
    os.chdir(tmp_path)
    summary = engine_run(cfg)
    assert summary["checks_failed"] == 0 

def test_engine_invalid_schema(tmp_path):
    cfg = tmp_path / "logic-graph.yml"
    cfg.write_text("schema: 2\nnodes: []\nedges: []\n")
    import pytest
    with pytest.raises(SystemExit):
        engine_run(cfg)

def test_engine_missing_file(tmp_path):
    import pytest
    with pytest.raises(SystemExit):
        engine_run(tmp_path / "nope.yml")

def test_engine_orphan(tmp_path):
    cfg = tmp_path / "logic-graph.yml"
    cfg.write_text("""
schema: 1
nodes:
  - id: a
    type: evidence
    boundary: README.md
  - id: b
    type: evidence
    boundary: README.md
edges:
  - from: a
    to: a
    obligation: file_exists
""")
    import shutil, os
    from veritas.vertex.engine import run as engine_run
    shutil.copyfile(pathlib.Path(__file__).parents[1]/"README.md", tmp_path/"README.md")
    os.chdir(tmp_path)
    summary = engine_run(cfg)
    assert summary["checks_failed"] > 0

def test_engine_cycle(tmp_path):
    cfg = tmp_path / "logic-graph.yml"
    cfg.write_text("""
schema: 1
nodes:
  - id: a
    type: evidence
    boundary: README.md
  - id: b
    type: evidence
    boundary: README.md
edges:
  - from: a
    to: b
    obligation: file_exists
  - from: b
    to: a
    obligation: file_exists
""")
    import shutil, os
    from veritas.vertex.engine import run as engine_run
    shutil.copyfile(pathlib.Path(__file__).parents[1]/"README.md", tmp_path/"README.md")
    os.chdir(tmp_path)
    summary = engine_run(cfg)
    assert summary["checks_failed"] > 0

def test_engine_unknown_plugin(tmp_path):
    cfg = tmp_path / "logic-graph.yml"
    cfg.write_text("""
schema: 1
nodes:
  - id: a
    type: evidence
    boundary: README.md
edges:
  - from: a
    to: a
    obligation: not_a_plugin
""")
    import shutil, os
    from veritas.vertex.engine import run as engine_run
    shutil.copyfile(pathlib.Path(__file__).parents[1]/"README.md", tmp_path/"README.md")
    os.chdir(tmp_path)
    summary = engine_run(cfg)
    assert summary["checks_failed"] > 0 

def test_extract_subgraph():
    from veritas.kernel.graph import Graph1, extract_subgraph
    nodes = {"a": {"id": "a"}, "b": {"id": "b"}, "c": {"id": "c"}}
    edges = [
        {"from": "a", "to": "b", "obligation": "x"},
        {"from": "b", "to": "c", "obligation": "x"},
    ]
    g = Graph1(nodes, edges)
    sub = extract_subgraph(g, "a")
    assert set(sub.nodes) == {"a", "b", "c"}
    sub2 = extract_subgraph(g, "b")
    assert set(sub2.nodes) == {"b", "c"}
    sub3 = extract_subgraph(g, "a", depth=1)
    assert set(sub3.nodes) == {"a", "b"} 