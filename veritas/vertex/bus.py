"""veritas.bus – minimal read-only observer bus (≈ 20 LOC).

Listeners subscribe via `subscribe(topic, fn)` where *fn* receives an
immutable copy of the payload (dict).  Core publishes events; exceptions
in listeners are caught and logged, never propagate.
"""
from __future__ import annotations

import sys
from typing import Callable, Dict, List
from copy import deepcopy

_Subscribers: Dict[str, List[Callable[[dict], None]]] = {}


def subscribe(topic: str, fn: Callable[[dict], None]) -> None:  # noqa: D401
    """Register *fn* to receive events of *topic*."""
    _Subscribers.setdefault(topic, []).append(fn)


def publish(topic: str, payload: dict) -> None:  # noqa: D401
    """Send *payload* to all subscribers of *topic* (read-only copy)."""
    for fn in _Subscribers.get(topic, []):
        try:
            fn(deepcopy(payload))
        except Exception as exc:  # pragma: no cover – errors swallowed
            print(f"[bus] listener error on {topic}: {exc}", file=sys.stderr)

__all__ = ["subscribe", "publish"] 