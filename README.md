# Δ-Kernel Reference Implementation

![CI](https://github.com/logicflow/delta/actions/workflows/ci.yml/badge.svg)

This repository contains a minimal, fully reproducible package that aims to verify
cross-disciplinary correspondences of the Δ-Kernel master equation.  At the moment
there are multiple numeric demos and Lean correspondences in varying stages of completeness. The continuous-integration pipeline
executes all tests (numeric demos + Lean compilation) and fails if any `sorry`
or an out-of-sync status tag is detected.

## Verification status (auto-generated)
<!-- STATUS-START -->

| Metric | Count |
|--------|-------|
| Lean files (core) | 11 |
| &nbsp; • completed proofs | 11 |
| &nbsp; • placeholders | 0 |
| &nbsp; • with `sorry` | 0 |
| Python demos verified | 12 |
| Total pytest tests passed | 13 |

| Correspondence | Lean | Demo |
|--------------|------|------|
| Boundary | ✅ | - |
| DeltaKernel | ✅ | - |
| FokkerPlanck | ✅ | True |
| GradientDescent | ❌ | True |
| Guardian | ✅ | ✅ |
| HH_Spike | ❌ | True |
| Landauer | ✅ | True |
| NavierStokes | ✅ | True |
| Noether | ✅ | True |
| PID | ❌ | True |
| Shannon | ⚠ | True |
| Stokes | ❌ | True |
| Uniqueness | ✅ | - |

### Attempted falsification (property-based guardian)

*Inside-domain counter-examples*: **0** (CI would fail otherwise; *200 random C¹ instances per run – override via `$HYPOTHESIS_MAX_EXAMPLES`*)  
*Outside-domain cases logged*: **0** – see `artifact/disproof/cases_outside.json`.

<!-- STATUS-END -->

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
CI PASSED: Lean compilation and all tests verified
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
| **Core theorems** | Lean 4 + mathlib | `artifact/proofs/` | ✅ compiles, **0 `#sorry`** |
| **Numerical demos** | pytest + NumPy | `artifact/code/` | ✅ 13/13 demos pass |
| **External deps** | mathlib, std4, aesop | pulled via `lake` | ⚠️ may include `sorry` in **their own test dirs** – *not compiled in CI* |

> The artifact purposefully separates *formal* Lean proofs from *auxiliary* numeric demonstrations.  CI fails if any `#sorry` appears in `artifact/proofs/`; external library test files are excluded from compilation.  See `build.sh` for the exact guard.

## License

MIT – see `LICENSE` for details. 

The project contains **numerical demos** and **Lean proofs** for each correspondence.
The continuous-integration pipeline executes all numeric demos plus a Lean compilation test; it fails if any
`sorry` or an out-of-sync status tag is found in source or YAML. 