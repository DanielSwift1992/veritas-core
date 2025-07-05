import textwrap
import pathlib
import shutil
import os
import sys

repo_root = pathlib.Path(__file__).resolve().parents[1]
core_path = repo_root / "tools" / "veritas-core"
if str(core_path) not in sys.path:
    sys.path.insert(0, str(core_path))

from veritas.engine import run as engine_run

def test_engine_minimal(tmp_path):
    # create minimal graph file
    cfg = tmp_path / "logic-graph.yml"
    cfg.write_text(textwrap.dedent("""
    schema: 4
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
    shutil.copyfile(pathlib.Path("README.md"), tmp_path / "README.md")
    os.chdir(tmp_path)
    summary = engine_run(cfg)
    assert summary["checks_failed"] == 0 