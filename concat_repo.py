#!/usr/bin/env python3
"""Concatenate all relevant text/source files in the repository into one file.

The script walks the project tree (starting from the directory where the script
is located) and collects the contents of *human-readable* files (source code,
docs, configs). Binary files, caches, and large artefacts are automatically
skipped.  Each file is preceded by a clear header containing its relative path
and a line of dashes for readability.

Usage:
    $ python concat_repo.py               # writes repo_concat.txt in cwd
    $ python concat_repo.py --out dump.md # custom output
"""
from __future__ import annotations

import argparse
import os
import hashlib
import fnmatch
from pathlib import Path
from typing import Iterable

# File extensions that are considered meaningful for analysis.
# Extend this tuple if needed.
INCLUDE_EXT: tuple[str, ...] = (
    ".py", ".cpp", ".c", ".h", ".lean", ".md", ".txt", ".tex", ".sh", ".rst",
    ".csv", ".json", ".yaml", ".yml", ".ini", ".cfg", ".make", ".mk",
)

# Directories to ignore entirely.
EXCLUDE_DIRS: set[str] = {
    ".git", "__pycache__", ".mypy_cache", ".pytest_cache", "node_modules",
    "dist", "build", ".venv", "venv", ".idea", ".vscode", "lake-packages", ".lake", ".elan",
}

# Files to ignore by exact name.
EXCLUDE_FILES: set[str] = {"LICENSE", "repo_concat.txt", "repo_concat_small.txt"}

# Maximum file size (in bytes) to include (skip huge datasets/binaries)
MAX_BYTES = 200_000  # 200 KB default

# Default maximum lines per file in output to keep concat readable
DEFAULT_LINE_LIMIT = 400


def iter_files(root: Path, extra_patterns: list[str]) -> Iterable[Path]:
    """Yield paths of files that should be included."""
    for dirpath, dirnames, filenames in os.walk(root):
        # Modify dirnames in-place to prune excluded directories during walk.
        dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIRS and not d.startswith('.')]
        for name in filenames:
            if name in EXCLUDE_FILES or name.startswith('.'):
                continue
            path = Path(dirpath) / name
            # pattern-based ignore
            if any(fnmatch.fnmatch(path.as_posix(), pat) for pat in extra_patterns):
                continue
            if path.suffix.lower() not in INCLUDE_EXT:
                continue
            if path.stat().st_size > MAX_BYTES:
                continue
            yield path.relative_to(root)


def sha256_of(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(8192), b""):
            h.update(chunk)
    return h.hexdigest()


def write_concat(root: Path, out_path: Path, add_sha: bool = False, line_limit: int = DEFAULT_LINE_LIMIT, extra_patterns: list[str] = []) -> None:
    with out_path.open("w", encoding="utf-8", errors="ignore") as fout:
        for rel_path in sorted(iter_files(root, extra_patterns)):
            # Header
            header = f"===== {rel_path} ====="
            fout.write(header + "\n")
            fout.write("-" * len(header) + "\n")
            # Optional SHA256 line
            if add_sha:
                fout.write(f"SHA256: {sha256_of(root / rel_path)}\n")
            # Content
            raw = (root / rel_path).read_text(encoding="utf-8", errors="ignore").splitlines()
            if line_limit and len(raw) > line_limit:
                slice_ = raw[:line_limit]
                slice_.append(f"... (truncated {len(raw)-line_limit} lines) ...")
            else:
                slice_ = raw
            fout.write("\n".join(slice_) + "\n\n")
    print(f"Wrote {out_path} with concatenated content of {sum(1 for _ in iter_files(root, extra_patterns))} files.")


def main() -> None:
    parser = argparse.ArgumentParser(description="Concatenate repository source files into one file.")
    parser.add_argument("--out", default="repo_concat.txt", help="Output file path (default: repo_concat.txt)")
    parser.add_argument("--sha", action="store_true", help="Append SHA256 for each file header")
    parser.add_argument("--limit", type=int, default=DEFAULT_LINE_LIMIT, help="Max lines per file (0=no limit)")
    parser.add_argument("--exclude", action="append", default=[], help="Glob pattern to exclude (can repeat)")
    args = parser.parse_args()

    root = Path(__file__).resolve().parent
    write_concat(root, Path(args.out), add_sha=args.sha, line_limit=args.limit, extra_patterns=args.exclude)


if __name__ == "__main__":
    main() 