"""veritas.engine – single execution engine.

Responsibilities:
1. Load logic-graph.yml (schema-1) → build in-memory graph.
2. Execute obligations via registered plugins.
3. Publish events on bus (graph.built, check.completed).

Currently synchronous, but design allows future asyncio gather.
"""
from __future__ import annotations
import pathlib, sys, subprocess
from typing import Any, Dict, List, Callable

from .bus import publish
from .plugin_api import discover_plugins
from ..kernel.graph import load as load_graph, Graph1
import hashlib, json, networkx as nx, time
import yaml, importlib

# Registry of built-in shell morphisms (fallback)
_MORPHISMS: Dict[str, List[Callable[[dict[str, Any]], None]]] = {
    "produce": [],
    "assert": [],
    "observe": [],
}


def register(kind: str, fn: Callable[[dict[str, Any]], None]) -> None:
    if kind not in _MORPHISMS:
        raise KeyError(kind)
    _MORPHISMS[kind].append(fn)


# default shell executor ------------------------------------------------------

def _shell(step: dict[str, Any]) -> None:
    cmd = step.get("cmd")
    if not cmd:
        raise ValueError("shell morphism requires 'cmd'")
    subprocess.check_call(cmd, shell=True)


register("produce", _shell)
register("assert", _shell)


def _observe_print(step: dict[str, Any]) -> None:
    name, val = step.get("name"), step.get("value")
    print(f"[observe] {name} = {val}")


register("observe", _observe_print)


# ---------------------------------------------------------------------------


def _resolve_plugin(name: str):
    plugins = discover_plugins()
    cls = plugins.get(name)
    return cls() if cls else None


# ---------------------------------------------------------------------------

def _import_declared_plugins(cfg: str | pathlib.Path):
    p = pathlib.Path(cfg)
    if not p.exists():
        return
    try:
        raw = yaml.safe_load(p.read_text()) or {}
    except Exception:
        return
    for ident in raw.get("plugins", []):
        if isinstance(ident, str):
            if ident.startswith(('./', '../')):
                pkg_path = pathlib.Path(ident).resolve()
                if pkg_path.is_dir():
                    sys.path.insert(0, str(pkg_path.parent))
                    pkg_name = pkg_path.name
                else:
                    continue
            else:
                pkg_name = ident
            try:
                importlib.import_module(pkg_name.replace('/', '.'))
            except ImportError:
                print(f"[veritas] plugin package '{pkg_name}' not importable", file=sys.stderr)


def run(cfg_path: str | pathlib.Path = "logic-graph.yml", *, collect_stats: bool = False, profile: bool = False) -> dict[str, Any]:
    """Execute checks; optionally return stats and timing info."""

    # Import plugins declared in graph before full load
    _import_declared_plugins(cfg_path)

    # Load v4 graph file ----------------------------------------------------
    graph = load_graph(cfg_path)
    if graph is not None:
        passed = failed = 0
        timings: dict[str, float] = {}
        nodes = graph.nodes
        for edge in graph.edges:
            check = edge.get("obligation", edge.get("check"))
            frm = edge.get("from")
            to = edge.get("to")
            if check is None or frm not in nodes or to not in nodes:
                failed += 1
                print(f"[veritas] malformed edge {edge}")
                continue
            plugin = _resolve_plugin(check)
            if not plugin:
                failed += 1
                print(f"[veritas] unknown check plugin {check}")
                continue
            boundary = pathlib.Path(nodes[frm].get("boundary", ""))
            t0 = time.perf_counter()
            meta = edge.get("meta", {})
            res = plugin.run(boundary, cfg=meta, **meta)
            dt = time.perf_counter() - t0
            if profile:
                timings.setdefault(check, 0.0)
                timings[check] += dt
            if res:
                passed += 1
            else:
                failed += 1
                print(f"[veritas] check failed: {frm}->{to} via {check}: {res.details}")
        # orphan-lint ----------------------------------------------------
        referenced = set()
        for e in graph.edges:
            referenced.add(e.get("from"))
            referenced.add(e.get("to"))
        orphans = set(nodes.keys()) - referenced
        if orphans:
            failed += len(orphans)
            print(f"[veritas] orphan nodes: {', '.join(sorted(orphans)[:10])} ...")

        # cycle detection via networkx ----------------------------------
        g = nx.DiGraph()
        g.add_nodes_from(nodes.keys())
        g.add_edges_from(
            (
                e["from"],
                e["to"]
            )
            for e in graph.edges if e["from"] != e["to"]
        )
        has_cycle = False
        try:
            nx.find_cycle(g, orientation="original")
            has_cycle = True
        except nx.exception.NetworkXNoCycle:
            has_cycle = False
        if has_cycle:
            failed += 1
            print("[veritas] cycle detected in graph")

        # Whole-hash -----------------------------------------------------
        if failed==0:
            canon = json.dumps({"nodes": nodes, "edges": graph.edges}, sort_keys=True).encode()
            whole_hash = hashlib.sha256(canon).hexdigest()[:12]
            pathlib.Path("whole.lock").write_text(whole_hash)
            print(f"[veritas] Whole OK – trust-stamp {whole_hash}")

        summary = {"checks_passed": passed, "checks_failed": failed}
        if collect_stats:
            from . import stats as _stats
            summary["stats"] = _stats.analyse(graph, timings if profile else None)
            publish("stats.ready", summary["stats"])
        publish("check.completed", summary)
        if summary["checks_failed"] == 0:
            # Try to update README via external markdown reporter if available
            try:
                from veritas_markdown.report import update_readme as _upd  # type: ignore
                _upd()
            except ImportError:
                try:
                    from .markdown_reporter import update_readme as _upd  # type: ignore
                    _upd()
                except ImportError:
                    pass
        return summary

    # If graph could not be loaded, fail early --------------------------------
    raise SystemExit(f"[veritas] {cfg_path} not found or invalid schema (expected schema=1)")


def run_graph(graph: Graph1, *, collect_stats: bool = False, profile: bool = False) -> dict[str, Any]:
    """Run checks directly on a Graph1 object (for subgraph checking, kb, etc)."""
    if graph is not None:
        passed = failed = 0
        timings: dict[str, float] = {}
        nodes = graph.nodes
        for edge in graph.edges:
            check = edge.get("obligation", edge.get("check"))
            frm = edge.get("from")
            to = edge.get("to")
            if check is None or frm not in nodes or to not in nodes:
                failed += 1
                print(f"[veritas] malformed edge {edge}")
                continue
            plugin = _resolve_plugin(check)
            if not plugin:
                failed += 1
                print(f"[veritas] unknown check plugin {check}")
                continue
            boundary = pathlib.Path(nodes[frm].get("boundary", ""))
            t0 = time.perf_counter()
            meta = edge.get("meta", {})
            res = plugin.run(boundary, cfg=meta, **meta)
            dt = time.perf_counter() - t0
            if profile:
                timings.setdefault(check, 0.0)
                timings[check] += dt
            if res:
                passed += 1
            else:
                failed += 1
                print(f"[veritas] check failed: {frm}->{to} via {check}: {res.details}")
        # orphan-lint ----------------------------------------------------
        referenced = set()
        for e in graph.edges:
            referenced.add(e.get("from"))
            referenced.add(e.get("to"))
        orphans = set(nodes.keys()) - referenced
        if orphans:
            failed += len(orphans)
            print(f"[veritas] orphan nodes: {', '.join(sorted(orphans)[:10])} ...")
        # cycle detection via networkx ----------------------------------
        g = nx.DiGraph()
        g.add_nodes_from(nodes.keys())
        g.add_edges_from(
            (
                e["from"],
                e["to"]
            )
            for e in graph.edges if e["from"] != e["to"]
        )
        has_cycle = False
        try:
            nx.find_cycle(g, orientation="original")
            has_cycle = True
        except nx.exception.NetworkXNoCycle:
            has_cycle = False
        if has_cycle:
            failed += 1
            print("[veritas] cycle detected in graph")
        # Whole-hash -----------------------------------------------------
        if failed==0:
            canon = json.dumps({"nodes": nodes, "edges": graph.edges}, sort_keys=True).encode()
            whole_hash = hashlib.sha256(canon).hexdigest()[:12]
            pathlib.Path("whole.lock").write_text(whole_hash)
            print(f"[veritas] Whole OK – trust-stamp {whole_hash}")
        summary = {"checks_passed": passed, "checks_failed": failed}
        if collect_stats:
            from . import stats as _stats
            summary["stats"] = _stats.analyse(graph, timings if profile else None)
            publish("stats.ready", summary["stats"])
        publish("check.completed", summary)
        if summary["checks_failed"] == 0:
            try:
                from veritas_markdown.report import update_readme as _upd  # type: ignore
                _upd()
            except ImportError:
                try:
                    from .markdown_reporter import update_readme as _upd  # type: ignore
                    _upd()
                except ImportError:
                    pass
        return summary
    raise SystemExit(f"[veritas] run_graph: invalid graph object")

__all__ = ["run", "run_graph"]

# TODO(v1.1): replace sequential loop with asyncio.gather for >1k checks performance 