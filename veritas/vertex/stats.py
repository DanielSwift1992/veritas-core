"""veritas.vertex.stats – graph metrics & profiling (requires networkx)."""
from __future__ import annotations
import collections
from typing import Dict, Any

try:
    import networkx as nx  # type: ignore
except ImportError:  # pragma: no cover
    nx = None  # type: ignore

__all__ = ["analyse", "render"]

def _build_nx(graph) -> nx.DiGraph:
    g = nx.DiGraph()
    g.add_nodes_from(graph.nodes.keys())
    g.add_edges_from((e["from"], e["to"]) for e in graph.edges)
    return g

def analyse(graph, timings: Dict[str, float] | None = None) -> dict:
    if nx is None:
        raise RuntimeError("networkx not installed – install 'veritas-core[stats]' to use graph metrics")
    G = _build_nx(graph)
    kinds = collections.Counter(e["obligation"] for e in graph.edges)
    self_edges = sum(1 for e in graph.edges if e["from"] == e["to"])
    cross_refs = len(graph.edges) - self_edges
    if G.number_of_nodes() == 0:
        diameter_val = "∞"
    elif G.number_of_nodes() == 1:
        diameter_val = 0
    else:
        diameter_val = nx.diameter(G) if nx.is_weakly_connected(G) else "∞"
    stats: dict = {
        "n_nodes": G.number_of_nodes(),
        "n_edges": G.number_of_edges(),
        "density": round(nx.density(G), 3) if G.number_of_nodes() > 1 else 0,
        "diameter": diameter_val,
        "kinds": kinds,
        "self_pct": self_edges / G.number_of_nodes() if G.number_of_nodes() else 1.0,
        "cross_refs": cross_refs,
    }
    if timings:
        stats["timings"] = dict(sorted(timings.items(), key=lambda x: x[1], reverse=True))
    return stats


def _fmt(sec: float) -> str:
    return f"{sec:.2f}s"

def render(stats: dict, *, show_profile: bool = False) -> str:
    parts: list[str] = []
    parts.append(
        f"Nodes: {stats['n_nodes']}  (self-checked {int(stats['self_pct']*100)}%)\n"
        f"Edges: {stats['n_edges']}  •  density {stats['density']}  •  diameter {stats['diameter']}"
    )
    kinds = ", ".join(f"{k}({v})" for k, v in stats["kinds"].most_common())
    parts.append(f"Obligations: {len(stats['kinds'])} kinds – {kinds}")
    if show_profile and "timings" in stats:
        top = list(stats["timings"].items())[:3]
        parts.append("Slowest: " + ", ".join(f"{k} {_fmt(t)}" for k, t in top))
    return "\n".join(parts) 