import hashlib, pathlib, textwrap
import pytest

from veritas.vertex.plugins.file_hash import FileHash
from veritas.vertex.plugins.markdown_nonempty import MarkdownNonEmpty
from veritas.vertex.plugins.radius_tracker import RadiusTracker


def test_file_hash_pass(tmp_path):
    f = tmp_path / "sample.txt"
    f.write_text("hello", encoding="utf-8")
    h = hashlib.sha256(b"hello").hexdigest()
    plugin = FileHash()
    res = plugin.run(f, cfg={"expected": h})
    assert res


def test_file_hash_fail(tmp_path):
    f = tmp_path / "sample.txt"
    f.write_text("hello", encoding="utf-8")
    plugin = FileHash()
    res = plugin.run(f, cfg={"expected": "deadbeef"})
    assert not res


def test_markdown_nonempty(tmp_path):
    md = tmp_path / "doc.md"
    md.write_text("content", encoding="utf-8")
    assert MarkdownNonEmpty().run(md)
    md.write_text("   ", encoding="utf-8")
    assert not MarkdownNonEmpty().run(md)


def test_radius_tracker_validation():
    rt = RadiusTracker()
    # invalid delta_cost
    res = rt.run(actor="x", delta_value=1, delta_cost=0, stability=1, risk=1)
    assert not res
    # valid scenario
    res_ok = rt.run(actor="x", delta_value=10, delta_cost=2, stability=1, risk=1)
    assert res_ok 