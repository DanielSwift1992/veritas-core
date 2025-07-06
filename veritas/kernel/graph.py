from __future__ import annotations
"""Minimal loader for *schema 4* logic-graph files.

Fails fast if provided YAML is not `schema: 4`. Only nodes / edges are
loaded; capsules are ignored in v1.0.
"""
import yaml, pathlib, typing

class Graph4(typing.NamedTuple):
    nodes: dict[str, dict]
    edges: list[dict]


def load(path: str | pathlib.Path = "logic-graph.yml") -> Graph4 | None:
    p = pathlib.Path(path)
    if not p.exists():
        return None
    data = yaml.safe_load(p.read_text()) or {}
    if data.get("schema") != 4:
        raise ValueError("veritas-core expects schema = 4")
    nodes = {n["id"]: n for n in data.get("nodes", []) if "id" in n}
    edges = data.get("edges", [])
    return Graph4(nodes, edges) 