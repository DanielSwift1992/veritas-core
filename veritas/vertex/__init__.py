"""veritas.vertex – Core Veritas engine and utilities."""

from .engine import run
from .bus import publish, subscribe  
from .plugin_api import plugin, BaseCheck, CheckResult, discover_plugins
from .lock_manager import create_lock, check_lock, check_and_lock, on_change, on_any_change

__all__ = [
    # Engine
    "run",
    # Event bus  
    "publish", "subscribe",
    # Plugin API
    "plugin", "BaseCheck", "CheckResult", "discover_plugins",
    # Lock management
    "create_lock", "check_lock", "check_and_lock", "on_change", "on_any_change"
]