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