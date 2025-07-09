"""Light-weight plugin system for Veritas.

Only **interface** and discovery are implemented here – all 
language-specific logic lives in separate packages exposed via the
``veritas_plugins`` entry-point.
"""
from __future__ import annotations

import sys, pathlib, importlib, pkgutil
from typing import Protocol, Any, Dict, runtime_checkable, abstractmethod
from importlib import metadata

__all__ = ["CheckResult", "discover_plugins"]

# ensure local path on sys.path for editable installs
cwd = str(pathlib.Path().resolve())
if cwd not in sys.path:
    sys.path.insert(0, cwd)

class CheckResult:
    """Uniform outcome returned by every plugin."""

    __slots__ = ("ok", "details", "verbosity_hint")

    def __init__(self, ok: bool, details: str | None = None, *, verbosity_hint: str | None = None):
        self.ok = bool(ok)
        self.details = details or ""
        # verbosity_hint: "quiet", "normal", "verbose" – core may use to filter logs
        self.verbosity_hint = verbosity_hint or "normal"

    # Convenience helpers -------------------------------------------------
    @classmethod
    def passed(cls, details: str | None = None, *, verbosity_hint: str | None = None) -> "CheckResult":  # noqa: D401
        return cls(True, details, verbosity_hint=verbosity_hint)

    @classmethod
    def failed(cls, details: str | None = None, *, verbosity_hint: str | None = None) -> "CheckResult":  # noqa: D401
        return cls(False, details, verbosity_hint=verbosity_hint)

    # Dunder helpers -------------------------------------------------------
    def __bool__(self) -> bool:  # pragma: no cover
        return self.ok

    def __repr__(self) -> str:  # pragma: no cover
        return f"<CheckResult ok={self.ok} details={self.details!r}>"


@runtime_checkable
class BaseCheck(Protocol):
    """Runtime contract for a single check implementation."""
    @abstractmethod
    def run(self, artifact: pathlib.Path, *, args: list[str] | None = None, **kw: Any) -> CheckResult:
        ...


# ----------------------------------------------------------------------
# Plugin discovery via importlib.metadata entry-points
# ----------------------------------------------------------------------

def _scan_local_plugins() -> dict[str, type[BaseCheck]]:
    """Discover plugin classes inside `veritas.vertex.plugins` package (source tree).

    Required for editable installs where entry-points are not yet registered.
    """
    mods: dict[str, type[BaseCheck]] = {}
    try:
        pkg = importlib.import_module("veritas.vertex.plugins")
    except ModuleNotFoundError:
        return mods
    for finder, name, ispkg in pkgutil.iter_modules(pkg.__path__):
        sub = importlib.import_module(f"{pkg.__name__}.{name}")
        for attr in dir(sub):
            obj = getattr(sub, attr)
            if isinstance(obj, type) and issubclass(obj, BaseCheck) and getattr(obj, "obligation", None):
                mods[obj.obligation] = obj
    return mods


def discover_plugins() -> dict[str, type[BaseCheck]]:
    """Return mapping obligation → plugin class.

    Precedence:
    1. Entry-points (installed packages)
    2. Inline @plugin-decorated classes within current process
    3. Source-tree modules under ``veritas.vertex.plugins`` (editable install)
    """
    eps = {ep.name: ep.load() for ep in metadata.entry_points(group="veritas_plugins")}
    local = _scan_local_plugins()
    # Inline decorators override nothing deliberately; entry-points win.
    combined = {**local, **_inline}
    combined.update(eps)  # entry-points have highest priority
    return combined


_inline: Dict[str, type[BaseCheck]] = {}

def plugin(name: str):
    """Class decorator: register *cls* under obligation *name* at import time.
    Usage:
        from veritas.plugin import plugin, BaseCheck, CheckResult
        @plugin("my_check")
        class MyCheck(BaseCheck):
            ...
    """
    def _wrap(cls):
        _inline[name] = cls
        return cls
    return _wrap 