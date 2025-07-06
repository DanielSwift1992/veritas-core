"""Shared helpers for CLI commands (pretty/JSON/template output)."""
from __future__ import annotations
import json, pathlib, typer
from typing import Any, Dict


def render_stats(stats: Dict[str, Any], *, json_out: bool, template: pathlib.Path | None, pretty: bool, show_profile: bool = False) -> None:  # noqa: D401
    """Render *stats* either as JSON, via Jinja2 template or pretty text.

    Mirrors logic previously duplicated between `check --stats` and `ask`.
    """
    if json_out:
        typer.echo(json.dumps(stats, indent=2))
        return
    if template:
        try:
            import jinja2
        except ImportError:  # pragma: no cover
            typer.secho("[veritas] jinja2 not installed", fg=typer.colors.RED)
            raise typer.Exit(1)
        tpl = jinja2.Template(template.read_text(encoding="utf-8"))
        typer.echo(tpl.render(stats=stats))
        return
    # pretty text (default)
    from .stats import render as _render
    typer.echo(_render(stats, show_profile=show_profile)) 