"""veritas.engine – single execution engine.

Responsibilities:
1. Load logic-graph.yml (schema-1) → build in-memory graph.
2. Execute obligations via registered plugins.
3. Publish events on bus (graph.built, check.completed).

Currently synchronous, but design allows future asyncio gather.
"""
from __future__ import annotations
import pathlib, sys, subprocess
from typing import Any, Dict, List, Callable, Tuple

from .bus import publish
from .plugin_api import discover_plugins
from ..kernel.graph import load as load_graph, Graph1
import hashlib, json, networkx as nx, time
from concurrent.futures import ThreadPoolExecutor
import os
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


def _node_digraph(nodes: dict, edges: list[dict]) -> nx.DiGraph:
    """Build a DiGraph over nodes, ignoring self-edges for dependencies."""
    g = nx.DiGraph()
    g.add_nodes_from(nodes.keys())
    g.add_edges_from((e["from"], e["to"]) for e in edges if e.get("from") != e.get("to"))
    return g


def _topo_levels(graph: Graph1) -> List[List[dict]]:
    """Return edge levels based on topological generations of nodes.

    Edges are grouped by the topo-level of their `from` node. Self-edges do not
    contribute dependencies and are placed according to their node level. Within
    a level, the original order from graph.edges is preserved.
    """
    G = _node_digraph(graph.nodes, graph.edges)
    try:
        gens = list(nx.topological_generations(G))
    except Exception:
        gens = []
    level_of: Dict[str, int] = {}
    for idx, gen in enumerate(gens):
        for n in gen:
            level_of[str(n)] = idx
    if not gens and graph.nodes:
        for n in graph.nodes.keys():
            level_of[str(n)] = 0
    max_level = max(level_of.values(), default=-1)
    levels: List[List[dict]] = [[] for _ in range(max_level + 1)] if max_level >= 0 else []
    for edge in graph.edges:
        frm = str(edge.get("from"))
        lvl = level_of.get(frm, 0)
        if max_level < 0:
            levels = [[]]
            max_level = 0
        while len(levels) <= lvl:
            levels.append([])
        levels[lvl].append(edge)
    return levels


def _auto_workers() -> int:
    try:
        cpu = os.cpu_count() or 4
    except Exception:
        cpu = 4
    return min(32, max(1, cpu))


def _run_levels(
    graph: Graph1,
    *,
    collect_stats: bool,
    profile: bool,
    concurrency: int | str,
    fail_fast: bool,
) -> dict[str, Any]:
    passed = failed = 0
    timings: dict[str, float] = {}
    nodes = graph.nodes

    # Basic validation
    malformed = False
    def _has_float(x) -> bool:
        if isinstance(x, float):
            return True
        if isinstance(x, dict):
            return any(_has_float(v) for v in x.values())
        if isinstance(x, (list, tuple)):
            return any(_has_float(v) for v in x)
        return False

    for edge in graph.edges:
        if edge.get("obligation", edge.get("check")) is None:
            malformed = True
            failed += 1
            print(f"[veritas] malformed edge {edge}")
        elif edge.get("from") not in nodes or edge.get("to") not in nodes:
            malformed = True
            failed += 1
            print(f"[veritas] malformed edge {edge}")
        else:
            meta = edge.get("meta", {})
            if _has_float(meta):
                malformed = True
                failed += 1
                print(f"[veritas] meta contains floating-point value(s), forbidden for determinism: {edge}")

    # Cycle detection
    has_cycle = False
    try:
        nx.find_cycle(_node_digraph(nodes, graph.edges), orientation="original")
        has_cycle = True
    except nx.exception.NetworkXNoCycle:
        has_cycle = False
    if has_cycle:
        failed += 1
        print("[veritas] cycle detected in graph")

    # Event: graph built & run started
    try:
        publish("graph.built", {"n_nodes": len(nodes), "n_edges": len(graph.edges)})
    except Exception:
        pass
    try:
        publish(
            "run.started",
            {
                "concurrency": (concurrency if isinstance(concurrency, str) else int(concurrency)),
                "fail_fast": bool(fail_fast),
                "profile": bool(profile),
            },
        )
    except Exception:
        pass

    levels = _topo_levels(graph)
    workers = _auto_workers() if (isinstance(concurrency, str) and concurrency == "auto") else int(concurrency)
    workers = max(1, workers)

    stop_scheduling = has_cycle or malformed
    last_level_idx = -1
    for level_idx, edges_level in enumerate(levels):
        last_level_idx = level_idx
        if stop_scheduling and fail_fast:
            break
        with ThreadPoolExecutor(max_workers=workers) as pool:
            futures: List[Tuple[int, dict, Any]] = []
            scheduled_in_level = 0
            for edge_idx, edge in enumerate(edges_level):
                check = edge.get("obligation", edge.get("check"))
                frm = edge.get("from")
                to = edge.get("to")
                if check is None or frm not in nodes or to not in nodes:
                    continue
                plugin = _resolve_plugin(check)
                if not plugin:
                    failed += 1
                    print(f"[veritas] unknown check plugin {check}")
                    stop_scheduling = stop_scheduling or fail_fast
                    continue
                boundary = pathlib.Path(nodes[frm].get("boundary", ""))
                meta = edge.get("meta", {})
                try:
                    publish("edge.started", {"from": frm, "to": to, "obligation": check, "level": level_idx, "index": edge_idx})
                except Exception:
                    pass

                def _run_one():
                    t0 = time.perf_counter()
                    res = plugin.run(boundary, cfg=meta, **meta)
                    dt = time.perf_counter() - t0
                    return res, dt, check, frm, to

                futures.append((edge_idx, edge, pool.submit(_run_one)))
                scheduled_in_level += 1

            # Collect in stable order
            results: Dict[int, Tuple[bool, str, float, str, dict]] = {}
            for edge_idx, edge, fut in futures:
                try:
                    res, dt, chk, frm, to = fut.result()
                    ok = bool(res)
                    details = getattr(res, "details", "")
                except Exception as e:
                    ok = False
                    details = f"plugin raised: {e}"
                    dt = 0.0
                    chk = edge.get("obligation", edge.get("check"))
                    frm = edge.get("from")
                    to = edge.get("to")
                if profile and chk:
                    timings.setdefault(chk, 0.0)
                    timings[chk] += dt
                results[edge_idx] = (ok, details, dt, chk, edge)

            for edge_idx, edge in enumerate(edges_level):
                if edge_idx not in results:
                    continue
                ok, details, dt, chk, ed = results[edge_idx]
                frm = ed.get("from")
                to = ed.get("to")
                if ok:
                    passed += 1
                else:
                    failed += 1
                    print(f"[veritas] check failed: {frm}->{to} via {chk}: {details}")
                    stop_scheduling = stop_scheduling or fail_fast
                try:
                    publish("edge.finished", {"from": frm, "to": to, "obligation": chk, "level": level_idx, "index": edge_idx, "ok": ok, "details": details, "dt": dt})
                except Exception:
                    pass

    # orphan-lint
    referenced = set()
    for e in graph.edges:
        referenced.add(e.get("from"))
        referenced.add(e.get("to"))
    orphans = set(nodes.keys()) - referenced
    if orphans:
        failed += len(orphans)
        print(f"[veritas] orphan nodes: {', '.join(sorted(orphans)[:10])} ...")

    # Skipped edges due to fail_fast
    skipped = 0
    if stop_scheduling and fail_fast and last_level_idx < (len(levels) - 1):
        for rest_idx in range(last_level_idx + 1, len(levels)):
            skipped += len(levels[rest_idx])

    if failed == 0:
        canon = json.dumps({"nodes": nodes, "edges": graph.edges}, sort_keys=True).encode()
        whole_hash = hashlib.sha256(canon).hexdigest()[:12]
        pathlib.Path("whole.lock").write_text(whole_hash)
        print(f"[veritas] Whole OK – trust-stamp {whole_hash}")
        try:
            publish("whole_hash", {"hash": whole_hash})
        except Exception:
            pass

    summary = {"checks_passed": passed, "checks_failed": failed, "skipped": skipped}
    if collect_stats:
        from . import stats as _stats
        summary["stats"] = _stats.analyse(graph, timings if profile else None)
        publish("stats.ready", summary["stats"])  # best-effort
    publish("check.completed", summary)
    try:
        publish(
            "run.finished",
            {
                "ok": summary.get("checks_failed", 0) == 0,
                "checks_passed": summary.get("checks_passed", 0),
                "checks_failed": summary.get("checks_failed", 0),
                "skipped": summary.get("skipped", 0),
            },
        )
    except Exception:
        pass
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


def run(
    cfg_path: str | pathlib.Path = "logic-graph.yml",
    *,
    collect_stats: bool = False,
    profile: bool = False,
    concurrency: int | str = 1,
    fail_fast: bool = False,
) -> dict[str, Any]:
    """Execute checks; optionally return stats and timing info.

    Args:
        cfg_path: Path to logic-graph.yml
        collect_stats: Include graph stats in summary
        profile: Collect per-plugin timing
        concurrency: int number of workers or "auto"
        fail_fast: Stop scheduling next levels after first failure
    """

    # Import plugins declared in graph before full load
    _import_declared_plugins(cfg_path)

    # Load v4 graph file ----------------------------------------------------
    graph = load_graph(cfg_path)
    if graph is not None:
        return _run_levels(
            graph,
            collect_stats=collect_stats,
            profile=profile,
            concurrency=concurrency,
            fail_fast=fail_fast,
        )

    # If graph could not be loaded, fail early --------------------------------
    raise SystemExit(f"[veritas] {cfg_path} not found or invalid schema (expected schema=1)")


def run_graph(
    graph: Graph1,
    *,
    collect_stats: bool = False,
    profile: bool = False,
    concurrency: int | str = 1,
    fail_fast: bool = False,
) -> dict[str, Any]:
    """Run checks directly on a Graph1 object (for subgraph checking, kb, etc)."""
    if graph is not None:
        return _run_levels(
            graph,
            collect_stats=collect_stats,
            profile=profile,
            concurrency=concurrency,
            fail_fast=fail_fast,
        )
    raise SystemExit(f"[veritas] run_graph: invalid graph object")

__all__ = ["run", "run_graph"]

# TODO(v1.1): replace sequential loop with asyncio.gather for >1k checks performance 