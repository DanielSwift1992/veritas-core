"""veritas.env_gen – generate Dockerfile or conda environment from project context.

MVP implementation: very naive –
* reads requirements.txt or requirements-dev.txt if present;
* minimal base image python:3.11-slim;
* copies repo and installs requirements.

Future versions will parse veritas.yml for explicit dependencies.
"""
from __future__ import annotations
import pathlib, textwrap
from typing import Tuple, List

ROOT = pathlib.Path(__file__).resolve().parents[2]


def _find_requirements() -> List[pathlib.Path]:
    files = []
    for name in ("requirements.txt", "requirements-dev.txt"):  # order of preference
        p = ROOT / name
        if p.exists():
            files.append(p)
    return files


def generate_dockerfile() -> str:
    reqs = _find_requirements()
    rels = [p.relative_to(ROOT) for p in reqs]
    docker = textwrap.dedent(
        f"""
        FROM python:3.11-slim
        WORKDIR /app
        COPY . /app
    """
    )
    if rels:
        for r in rels:
            docker += f"RUN pip install -r {r}\n"
    docker += "CMD [\"veritas\", \"check\"]\n"
    return docker


def generate_conda_yaml() -> str:
    reqs = _find_requirements()
    deps: List[str] = []
    for p in reqs:
        deps.extend(line.strip() for line in p.read_text().splitlines() if line.strip() and not line.startswith("#"))
    content = textwrap.dedent(
        """
        name: veritas-env
        channels: [defaults, conda-forge]
        dependencies:
          - python=3.11
    """
    )
    for d in deps:
        content += f"  - {d}\n"
    return content 