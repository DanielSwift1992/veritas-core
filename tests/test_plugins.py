import hashlib, pathlib, textwrap
import pytest
import sys

from veritas.vertex.plugins.file_hash import FileHash
from veritas.vertex.plugins.markdown_nonempty import MarkdownNonEmpty
from veritas.vertex.plugins.radius_tracker import RadiusTracker
from veritas.vertex.plugins.yaml_schema import YamlSchema


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


def test_yaml_schema_no_jsonschema(tmp_path, monkeypatch):
    yml = tmp_path / "data.yml"
    yml.write_text("foo: bar")
    plugin = YamlSchema()
    monkeypatch.setitem(sys.modules, "jsonschema", None)
    res = plugin.run(yml)
    assert res

def test_yaml_schema_invalid_schema(tmp_path):
    yml = tmp_path / "data.yml"
    yml.write_text("foo: bar")
    plugin = YamlSchema()
    # schema path не существует
    res = plugin.run(yml, cfg={"schema": "nope.json"})
    assert not res

def test_yaml_schema_invalid_yaml(tmp_path):
    yml = tmp_path / "data.yml"
    yml.write_text(": : :")
    plugin = YamlSchema()
    res = plugin.run(yml)
    assert not res 

def test_mdr_dissipation(tmp_path):
    from veritas.vertex.plugins.mdr_dissipation import MDRDissipation
    import yaml
    # Без цикла
    data = {"nodes": [{"id": "a"}, {"id": "b"}], "edges": [{"from": "a", "to": "b"}]}
    yml = tmp_path / "g1.yml"
    yml.write_text(yaml.dump(data))
    assert MDRDissipation().run(yml)
    # С циклом
    data2 = {"nodes": [{"id": "a"}, {"id": "b"}], "edges": [{"from": "a", "to": "b"}, {"from": "b", "to": "a"}]}
    yml2 = tmp_path / "g2.yml"
    yml2.write_text(yaml.dump(data2))
    assert not MDRDissipation().run(yml2) 