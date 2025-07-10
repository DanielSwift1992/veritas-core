from __future__ import annotations
"""Minimal loader for *schema 1* logic-graph files.

Fails fast if provided YAML is not `schema: 1`. Only nodes / edges are
loaded; capsules are ignored in v1.0.
"""
import yaml, pathlib, typing

class Graph1(typing.NamedTuple):
    nodes: dict[str, dict]
    edges: list[dict]


def load(path: str | pathlib.Path = "logic-graph.yml") -> Graph1 | None:
    p = pathlib.Path(path)
    if not p.exists():
        return None
    data = yaml.safe_load(p.read_text()) or {}
    if data.get("schema") != 1:
        import sys
        print("veritas-core expects schema = 1", file=sys.stderr)
        raise SystemExit(1)
    nodes = {n["id"]: n for n in data.get("nodes", []) if "id" in n}
    edges = data.get("edges", [])
    return Graph1(nodes, edges)


def extract_subgraph(graph: Graph1, uid: str, depth: int | None = None) -> Graph1:
    """Извлекает подграф из graph, начиная с uid, на глубину depth (или все descendants)."""
    try:
        import networkx as nx
    except ImportError:
        return Graph1({}, [])
    G = nx.DiGraph()
    G.add_nodes_from(graph.nodes.keys())
    G.add_edges_from((e["from"], e["to"]) for e in graph.edges)
    if uid not in G:
        return Graph1({}, [])
    if depth is None:
        sub_nodes = nx.descendants(G, uid) | {uid}
    else:
        sub_nodes = {n for n, d in nx.single_source_shortest_path_length(G, uid, cutoff=depth).items() if d <= depth}
    nodes = {n: graph.nodes[n] for n in sub_nodes if n in graph.nodes}
    edges = [e for e in graph.edges if e["from"] in sub_nodes and e["to"] in sub_nodes]
    return Graph1(nodes, edges) 