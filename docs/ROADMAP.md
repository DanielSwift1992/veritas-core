# Veritas Roadmap

_Last updated: 2024-07-04_

This document tracks the concrete steps needed to reach a stable v1.0 of **Veritas** – a small tool that checks whether the research artefacts in a repository are still in sync with each other.

| Period | Goal | What we will actually ship |
| ------ | ---- | -------------------------- |
| **Now** | MVP inside LogicSubstrat | • `veritas run / status` commands<br/>• Lean & pytest checks<br/>• README table auto-update |
| **2024-Q3** | First external repo | • Move code to standalone repo `veritas-core`<br/>• Publish alpha on PyPI (`0.5.x`)<br/>• `veritas.yml` schema v1<br/>• Plugin SDK (`Check` base-class, entry-points) |
| **2024-Q4** | CI & usability | • Off-the-shelf GitHub Action<br/>• Badge endpoint (`/status.svg`)<br/>• Cache & diff runner (skip unaffected checks) |
| **2025-Q1** | Ecosystem start | • Minimal plugin set: `lean`, `pytest`, `jupyter`, `ruff`, `shell`<br/>• Docs site with typedoc-style API and quick-start<br/>• Cookiecutter starter template |
| **2025-Q2** | v1.0 Stable | • SemVer-locked core API<br/>• Conda feedstock<br/>• Signed releases, SBOM |
| **2025-H2** | Community | • "Veritas Exchange" – index of third-party plugins<br/>• First reproducibility workshop / hackathon |

Everything after v1.0 will be re-evaluated with real user feedback – no speculation beyond that. 