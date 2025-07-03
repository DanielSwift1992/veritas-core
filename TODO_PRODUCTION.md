# Production Roadmap for Δ-Kernel

This living document captures medium-term tasks that are **not** yet reflected by the auto-generated status table in `README.md`.

The status table already answers "what is complete today".  This file lists *where we are going next* and is maintained manually.

---

## 1  Formal proofs (Lean)

| Correspondence | Current status* | Action | Owner | Priority |
| -------------- | -------------- | ------ | ----- | -------- |
| Shannon | partial | finish entropy equality proof | — | ★★★ |
| Euler–Lagrange | partial | lift 1-D lemma → general functional | — | ★★ |
| Navier–Stokes | none | prove energy identity via vorticity | — | ★★ |
| Stokes | none | mini-solver lemma → Lean | — | ★ |
| PID / HJB | none | formal optimal-control link | — | ★★ |
| Gradient descent | none | convert Lyapunov argument to Lean | — | ★★ |

<sup>* See live status table for up-to-date flag.</sup>

## 2  Numeric demos

* Extend `ns_energy.py` to 2-D grid, tighten tolerance.
* GPU version of `nash_gradient.py` (PyTorch) for benchmarking.
* Param sweep notebook for `hh_spike.py` (energy vs temperature).

## 3  Continuous Integration

* Add GitHub Actions matrix `ubuntu-latest`, `macos-latest`.
* Cache Lean olean files.
* Publish docker image to GHCR; read-only Binder link (`--skip-lean`).

## 4  Documentation automation

* Auto-insert status numbers into LaTeX (`status.tex`).
* Generate HTML dag of dependencies via `networkx`.

## 5  Release engineering

* `concat_repo.py --sha` for archival bundle.
* Draft Zenodo workflow; insert DOI after first green release.

---

Last updated: <!-- AUTO-DATE -->