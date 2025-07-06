# Built-in fallback plugins for veritas-core

from __future__ import annotations

__all__: list[str] = []  # populated by dynamic imports

# automatically import submodules to register their classes via entry-points
from importlib import import_module
import pkgutil

_pkg = __name__
for _finder, _name, _ispkg in pkgutil.iter_modules(__path__):
    import_module(f"{_pkg}.{_name}")
    __all__.append(_name) 