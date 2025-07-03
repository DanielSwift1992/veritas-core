# Δ-Kernel Reference Implementation

![CI](https://github.com/logicflow/delta/actions/workflows/ci.yml/badge.svg)

This repository contains a minimal, fully reproducible package that verifies
12 cross-disciplinary correspondences of the Δ-Kernel master equation

\[
E = \int_{M} F \cdot \nabla P\, dM.
\]

## Quick start

```bash
# clone and build
git clone <repo-url> && cd delta-kernel
./build.sh
```

To run only the numeric demos (skipping Lean proofs), add the flag `--skip-lean`:

```bash
./build.sh --skip-lean
```

A successful run prints the CI banner below, indicating that both Lean proofs and numeric demos are verified.

```
CI PASSED: Lean proofs and 12 numeric correspondences verified
```

## Directory map

See `paper/blueprint.md` for a full schematic. Key paths:

* `artifact/code/` – runnable demos (≤ 2 s each with `--ci` flag)
* `artifact/proofs/` – Lean 4 sources; zero `#sorry`
* `artifact/tests/` – pytest + Lean test runner
* `docker/` – Dockerfile for offline CI

## Verification matrix

| Component | Methodology | Scope | Status |
|-----------|------------|-------|--------|
| **Core theorems** | Lean 4 + mathlib | `artifact/proofs/` | ✅ machine-checked, **0 `#sorry`** |
| **Numerical demos** | pytest + NumPy | `artifact/code/` | ✅ 12/12 tests pass |
| **External deps** | mathlib, std4, aesop | pulled via `lake` | ⚠️ may include `sorry` in **their own test dirs** – *not compiled in CI* |

> The artifact purposefully separates *formal* Lean proofs from *auxiliary* numeric demonstrations.  CI fails if any `#sorry` appears in `artifact/proofs/`; external library test files are excluded from compilation.  See `build.sh` for the exact guard.

## License

MIT – see `LICENSE` for details. 