from __future__ import annotations
import pathlib
from veritas.vertex.plugin_api import BaseCheck, CheckResult

class MDRDissipation(BaseCheck):
    obligation = "mdr_dissipation"

    def run(self, artifact: pathlib.Path, **kw):
        try:
            import yaml, networkx as nx
        except ImportError:
            return CheckResult.failed("missing deps: yaml/networkx")
        data = yaml.safe_load(artifact.read_text())
        G = nx.DiGraph()
        G.add_nodes_from(n["id"] for n in data["nodes"])
        G.add_edges_from((e["from"], e["to"]) for e in data["edges"])
        try:
            nx.find_cycle(G, orientation="original")
            return CheckResult.failed("cycle detected (dissipation > 0)")
        except nx.exception.NetworkXNoCycle:
            return CheckResult.passed() 