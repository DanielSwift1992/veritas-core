"""Veritas Core CLI (MVP)."""
from __future__ import annotations
import pathlib, sys, contextlib, io
import typer
from .plugin_api import discover_plugins
from .env_gen import generate_dockerfile, generate_conda_yaml
from ._util import render_stats as _render_stats

app = typer.Typer(help="Veritas Core CLI")
# Determine repository root (directory that contains 'artifact/' or 'logic-graph.yml')
ROOT = pathlib.Path(__file__).resolve()
while not ((ROOT / "artifact").exists() or (ROOT / "logic-graph.yml").exists()) and ROOT != ROOT.parent:
    ROOT = ROOT.parent

# Preferred entry point for CI/local verification
@app.command()
def check(
    markdown: bool = typer.Option(True, "--markdown/--no-markdown", help="Update README"),
    quiet: bool = typer.Option(False, "--quiet", help="Suppress plugin output, only summary line"),
    debug: bool = typer.Option(False, "--debug", help="Verbose output (no suppression)"),
    stats: bool = typer.Option(False, "--stats", help="Print graph summary after run"),
    json_out: bool = typer.Option(False, "--json", help="Output stats as JSON instead of pretty text"),
    pretty: bool = typer.Option(False, "--pretty", help="Force pretty human text even in CI"),
    template: pathlib.Path | None = typer.Option(None, "--template", help="Render stats via Jinja2 template"),
    profile: bool = typer.Option(False, "--profile", help="Measure plugin timings"),
) -> None:
    """Run verification via engine then (optionally) update status."""

    from .engine import run as engine_run

    # skip_lean option removed; no Lean dependency in core
    if quiet and debug:
        typer.secho("--quiet and --debug are mutually exclusive", fg=typer.colors.RED, err=True)
        raise typer.Exit(1)

    # Auto-select JSON in CI unless --pretty given
    import os
    if not pretty and not json_out and os.environ.get("CI", "").lower() == "true":
        json_out = True

    # Capture stdout/stderr if quiet
    if quiet:
        buf_out, buf_err = io.StringIO(), io.StringIO()
        with contextlib.redirect_stdout(buf_out), contextlib.redirect_stderr(buf_err):
            summary = engine_run(collect_stats=stats, profile=profile)
    else:
        summary = engine_run(collect_stats=stats, profile=profile)

    # Print binary summary line
    ok = summary.get("checks_failed", 0) == 0
    typer.echo(f"CHECKS PASSED={summary.get('checks_passed', 0)} FAILED={summary.get('checks_failed', 0)}")

    if stats and "stats" in summary:
        stats_data = summary["stats"]
        if json_out:
            import json as _json
            typer.echo(_json.dumps(stats_data, indent=2))
        elif template:
            try:
                import jinja2
                tpl = jinja2.Template(template.read_text())
                typer.echo(tpl.render(stats=stats_data))
            except ImportError:
                typer.secho("[veritas] jinja2 not installed", fg=typer.colors.RED)
                raise typer.Exit(1)
        else:
            from .stats import render
            typer.echo(render(stats_data, show_profile=profile))

    if not ok:
        raise typer.Exit(1)

    if markdown:
        _update_readme()

@app.command("list-plugins")
def list_plugins() -> None:
    """Print table of all discovered plugins."""
    from rich.table import Table
    from rich.console import Console

    plugins = discover_plugins()
    tbl = Table("name", "module")
    for name, cls in sorted(plugins.items()):
        tbl.add_row(name, f"{cls.__module__}:{cls.__qualname__}")
    Console().print(tbl)

# ----------------------------------------------------------------------
# Attestation bundle
# ----------------------------------------------------------------------

def _sha256(p: pathlib.Path) -> str:
    import hashlib

    h = hashlib.sha256()
    with p.open("rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()

@app.command()
def attest(
    dest: pathlib.Path = typer.Option(
        pathlib.Path("veritas_bundle.tar.gz"), "--dest", help="Output archive path"
    ),
    include_readme: bool = typer.Option(True, "--readme/--no-readme"),
) -> None:
    """Create reproducibility bundle + attest.json with SHA256 hashes.

    Currently packs all files under `artifact/` plus `logic-graph.yml` and README.
    """

    import tarfile, json, os, platform, datetime, hashlib

    console = typer.echo

    root = ROOT
    paths: list[pathlib.Path] = []
    # Add key directories if they exist
    for rel in ["artifact", "logic-graph.yml"]:
        p = root / rel
        if p.exists():
            if p.is_dir():
                paths.extend(p.rglob("*"))
            else:
                paths.append(p)
    if include_readme and (root / "README.md").exists():
        paths.append(root / "README.md")

    # Filter to files
    files = [p for p in paths if p.is_file()]

    # Compute hashes
    manifest = {
        "created": datetime.datetime.utcnow().isoformat() + "Z",
        "python": platform.python_version(),
        "platform": platform.platform(),
        "files": {str(p.relative_to(root)): _sha256(p) for p in files},
    }

    attest_path = dest.with_suffix(".attest.json")

    # Write JSON first so it can be included
    attest_path.write_text(json.dumps(manifest, indent=2))

    # Create tar.gz
    console(f"[veritas] creating bundle {dest} with {len(files)} files…")
    with tarfile.open(dest, "w:gz") as tar:
        for p in files:
            tar.add(p, arcname=str(p.relative_to(root)))
        tar.add(attest_path, arcname=attest_path.name)
    console("[veritas] bundle created.")
    console(f"[veritas] manifest → {attest_path}")

# ----------------------------------------------------------------------
# Environment generator (Dockerfile / conda)
# ----------------------------------------------------------------------

@app.command()
def env(
    docker: bool = typer.Option(True, "--docker/--no-docker", help="Generate Dockerfile"),
    conda: bool = typer.Option(False, "--conda", help="Generate conda environment.yml"),
) -> None:
    """Generate Dockerfile or conda env based on project requirements."""

    if docker:
        typer.echo(generate_dockerfile())
    elif conda:
        typer.echo(generate_conda_yaml())
    else:
        typer.secho("Specify --docker or --conda", fg=typer.colors.RED)

# ----------------------------------------------------------------------
# Status / report commands now use in-process reporter
# ----------------------------------------------------------------------

@app.command()
def status(markdown: bool = typer.Option(True, "--markdown/--no-markdown", help="Insert README block")) -> None:
    """Generate status tables and (optionally) insert into README."""
    if markdown:
        typer.echo("[veritas] updating README status block…")
        _update_readme()
    else:
        typer.echo("[veritas] status (markdown flag disabled) – nothing to do")

# Backward-compat alias
@app.command()
def report(markdown: bool = typer.Option(True, "--markdown/--no-markdown", help="Insert README block")) -> None:
    typer.secho("[veritas] 'report' is deprecated, use 'status' instead", fg=typer.colors.YELLOW)
    if markdown:
        _update_readme()

@app.command()
def scan(
    cfg: pathlib.Path = typer.Option(pathlib.Path("logic-graph.yml"), "--cfg", help="output file"),
    interactive: bool = typer.Option(False, "--interactive", help="ask confirmation before overwrite"),
) -> None:
    """Auto-generate minimal `logic-graph.yml` via **external** `veritas-autoscan` plugin.

    The implementation was removed from *veritas-core* to keep the kernel lean.
    Install the helper:

        pip install veritas-autoscan
    """

    # Resolve generator from external package -------------------------
    gen = None
    try:
        # Preferred: dedicated package
        from importlib import import_module as _imp
        gen = _imp("veritas_autoscan").generate_cfg
    except Exception:
        pass

    if gen is None:
        typer.secho("[veritas] auto-scan plugin not installed.\n"
                   "Install via `pip install veritas-autoscan` or provide your own generator.",
                   fg=typer.colors.RED)
        raise typer.Exit(1)

    if interactive and cfg.exists():
        typer.echo(f"[veritas] {cfg} already exists. Overwrite? [y/N] ", nl=False)
        ans = input().strip().lower()
        if ans not in ("y", "yes"):
            typer.echo("[veritas] Aborted by user.")
            raise typer.Exit(1)

    gen(cfg)

# ----------------------------------------------------------------------
# Helper: update README via external plugin (veritas-markdown)
# ----------------------------------------------------------------------

def _update_readme() -> None:
    """Call `veritas_markdown.report.update_readme()` if available.

    Falls back to former internal path ``veritas.vertex.markdown_reporter`` for
    backward-compatibility, but core no longer ships that module.
    """

    try:
        from veritas_markdown.report import update_readme as _upd  # type: ignore
        _upd()
        return
    except ImportError:
        pass
    # Legacy fallback (pre-0.9)
    try:
        from .markdown_reporter import update_readme as _upd  # type: ignore
        _upd()
    except ImportError:
        # Reporter not installed → silently skip
        pass

# ----------------------------------------------------------------------
# Ask command – read-only graph introspection
# ----------------------------------------------------------------------

@app.command()
def ask(
    json_out: bool = typer.Option(False, "--json", help="Output stats as JSON instead of pretty text"),
    pretty: bool = typer.Option(False, "--pretty", help="Force pretty human text even in CI"),
    template: pathlib.Path | None = typer.Option(None, "--template", help="Render stats via Jinja2 template"),
) -> None:
    """Display graph metrics without running obligations."""

    from ..kernel.graph import load as _load_graph
    from . import stats as _stats
    from .bus import publish

    graph = _load_graph()
    if graph is None:
        typer.secho("[veritas] logic-graph.yml not found; run 'veritas scan' first", fg=typer.colors.RED)
        raise typer.Exit(1)

    try:
        data = _stats.analyse(graph)
    except RuntimeError as exc:
        typer.secho(f"[veritas] {exc}", fg=typer.colors.RED)
        raise typer.Exit(1)

    publish("stats.ready", data)
    _render_stats(data, json_out=json_out, template=template, pretty=pretty)

if __name__ == "__main__":
    app()
