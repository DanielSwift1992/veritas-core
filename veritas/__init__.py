"""Veritas Core – minimal package stub."""

from importlib import metadata as _metadata

try:
    __version__: str = _metadata.version(__name__)
except _metadata.PackageNotFoundError:  # package not installed (e.g. source checkout)
    __version__ = "0.9.0.dev0"

# Auto-register optional reporters (best-effort, ignore failures)
try:
    import veritas_latex_reporter  # noqa: F401
except Exception:  # pragma: no cover – reporter optional
    pass

# --------------------------------------------------------------------
import sys as _sys
from importlib import import_module
from types import ModuleType as _ModuleType

# Public subpackages
from . import kernel as kernel  # noqa
from . import vertex as vertex  # noqa

# Lazily expose legacy module paths
_engine: _ModuleType = import_module(".vertex.engine", __name__)
_sys.modules[__name__ + ".engine"] = _engine
try:
    _cli: _ModuleType = import_module(".vertex.cli", __name__)
    _sys.modules[__name__ + ".cli"] = _cli
except Exception:
    pass
_bus: _ModuleType = import_module(".vertex.bus", __name__)
_sys.modules[__name__ + ".bus"] = _bus

__all__ = ["kernel", "vertex"]
