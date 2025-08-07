"""veritas.vertex.lock_manager – Simple custom object lock functions.

Extends Veritas whole.lock pattern to arbitrary objects with minimal API.

Usage:
    from veritas.vertex.lock_manager import create_lock, check_lock, on_change
    
    # Simple lock creation
    hash = create_lock("plugins", ["setup.py", "plugins/checks.py"])
    
    # Check if changed
    changed, current, stored = check_lock("plugins", ["setup.py", "plugins/checks.py"])
    
    # Subscribe to changes
    on_change("plugins", lambda event: print(f"Plugins changed!"))
"""
from __future__ import annotations

import pathlib
import json
import hashlib
from typing import List, Tuple, Union, Callable, Dict, Any

from .bus import publish, subscribe


def _calculate_object_hash(name: str, files: List[Union[str, pathlib.Path]], root: pathlib.Path = None) -> str:
    """Calculate Veritas-compatible hash for object."""
    if root is None:
        root = pathlib.Path.cwd()
    
    # Convert to Path objects
    file_paths = [pathlib.Path(f) if isinstance(f, str) else f for f in files]
    
    # Create object definition like Veritas
    object_def = {
        "name": name,
        "files": []
    }
    
    for file_path in sorted(file_paths):
        if file_path.exists():
            content = file_path.read_bytes()
            file_hash = hashlib.sha256(content).hexdigest()[:16]
            object_def["files"].append({
                "path": str(file_path.relative_to(root)) if file_path.is_absolute() else str(file_path),
                "hash": file_hash,
                "size": len(content)
            })
        else:
            object_def["files"].append({
                "path": str(file_path.relative_to(root)) if file_path.is_absolute() else str(file_path),
                "missing": True
            })
    
    # Calculate canonical hash like Veritas (12 chars)
    canon = json.dumps(object_def, sort_keys=True).encode()
    return hashlib.sha256(canon).hexdigest()[:12]


def create_lock(name: str, files: List[Union[str, pathlib.Path]], root: pathlib.Path = None) -> str:
    """Create/update lock file for object. Returns hash."""
    if root is None:
        root = pathlib.Path.cwd()
    
    current_hash = _calculate_object_hash(name, files, root)
    lock_file = root / f"{name}.lock"
    lock_file.write_text(current_hash)
    
    publish("object.locked", {
        "name": name,
        "hash": current_hash,
        "files": [str(f) for f in files],
        "lock_file": str(lock_file)
    })
    
    return current_hash


def check_lock(name: str, files: List[Union[str, pathlib.Path]], root: pathlib.Path = None) -> Tuple[bool, str, str]:
    """Check if object changed. Returns (changed, current_hash, stored_hash)."""
    if root is None:
        root = pathlib.Path.cwd()
    
    current_hash = _calculate_object_hash(name, files, root)
    lock_file = root / f"{name}.lock"
    
    if lock_file.exists():
        try:
            stored_hash = lock_file.read_text().strip()
            changed = stored_hash != current_hash
            
            if changed:
                publish("object.changed", {
                    "name": name,
                    "old_hash": stored_hash,
                    "new_hash": current_hash,
                    "files": [str(f) for f in files]
                })
            
            return changed, current_hash, stored_hash
        except Exception:
            return True, current_hash, "corrupted"
    else:
        publish("object.created", {
            "name": name,
            "hash": current_hash,
            "files": [str(f) for f in files]
        })
        return True, current_hash, "missing"


def check_and_lock(name: str, files: List[Union[str, pathlib.Path]], root: pathlib.Path = None) -> Tuple[bool, str]:
    """Check for changes and update lock if needed. Returns (was_changed, current_hash)."""
    changed, current_hash, stored_hash = check_lock(name, files, root)
    
    if changed:
        create_lock(name, files, root)
        return True, current_hash
    else:
        return False, current_hash


def on_change(name: str, callback: Callable[[Dict[str, Any]], None]) -> None:
    """Subscribe to changes for specific object."""
    def filtered_callback(event: Dict[str, Any]) -> None:
        if event.get("name") == name:
            callback(event)
    
    subscribe("object.changed", filtered_callback)
    subscribe("object.created", filtered_callback)


def on_any_change(callback: Callable[[Dict[str, Any]], None]) -> None:
    """Subscribe to all object changes."""
    subscribe("object.changed", callback)
    subscribe("object.created", callback) 
    subscribe("object.locked", callback)


__all__ = [
    "create_lock",
    "check_lock", 
    "check_and_lock",
    "on_change",
    "on_any_change"
]