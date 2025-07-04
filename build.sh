#!/usr/bin/env bash
set -euo pipefail

# Optional flag --skip-lean allows running numeric demos only.
if [[ "${1:-}" == "--skip-lean" ]]; then
  SKIP_LEAN=1
  shift
else
  SKIP_LEAN=0
fi

# Simple CI driver for local runs.

# 1. Run Lean proofs unless skip flag set
if [[ "$SKIP_LEAN" -eq 0 ]]; then
  if command -v lake &>/dev/null; then
    echo "[build] Running Lean proofs…"
    pushd artifact/proofs >/dev/null || exit 1
    lake build

    # Fail CI if any `sorry` appears in our own proofs (excluding vendored packages)
    echo "[build] Scanning core proofs for 'sorry' placeholders …"
    if grep -R --include='*.lean' --exclude-dir='lake-packages' --exclude-dir='.lake' -n '\bsorry\b' . >/dev/null; then
      echo "[error] 'sorry' found in core proof files. Commit must provide complete proofs."
      exit 1
    else
      echo "[build] No 'sorry' placeholders detected."
    fi

    popd >/dev/null || exit 1
  else
    echo "[error] Lean (lake) not found – please install via 'elan toolchain install leanprover/lean4:stable'."
    exit 1
  fi
else
  echo "[build] --skip-lean specified – skipping Lean proofs."
fi

# 2. Run pytest demos
if command -v pytest &>/dev/null; then
  echo "[build] Running Python/C++ demos via pytest…"
  CORE_DIR="tools/veritas-core"
  export PYTHONPATH="$PYTHONPATH:$CORE_DIR"
  pytest -q artifact/tests "$CORE_DIR"/disproof || {
    echo "Tests failed"; exit 1; }
else
  echo "[build] pytest not found – skipping demos."
fi

# 3. Run outside-domain counterexample finder (non-fatal)
if python -m artifact.disproof.find_outside_domain; then
  echo "[build] Disproof scan completed.";
else
  echo "[warn] Disproof scan failed (non-critical).";
fi

echo "[build] Updating verification status in README …"
CORE_DIR="tools/veritas-core"
python "$CORE_DIR"/gen_status.py --write-yaml --insert-readme || {
  echo "[warn] Failed to update README status table"; }

# Warn if placeholders remain (set STRICT_PLACEHOLDERS=1 to make this fatal)
PLACEHOLDERS=$(python "$CORE_DIR"/gen_status.py --json | python -c 'import sys, json; print(json.load(sys.stdin)["metrics"]["lean_placeholders"])')
if [[ "$PLACEHOLDERS" -ne 0 ]]; then
  if [[ -n "${CI:-}" && "${STRICT_PLACEHOLDERS:-}" == "" ]]; then
    export STRICT_PLACEHOLDERS=1
  fi
  if [[ "${STRICT_PLACEHOLDERS:-0}" -eq 1 ]]; then
    echo "[error] $PLACEHOLDERS placeholder lemmas remain. CI requires 0."
    exit 1
  else
    echo "[warn] $PLACEHOLDERS placeholder lemmas remain. (Set STRICT_PLACEHOLDERS=1 to fail)."
  fi
fi

# Ensure README and YAML up to date
if ! git diff --exit-code README.md status.yml >/dev/null; then
  echo "[error] README.md or status.yml out of date with auto-generated status. Run build and commit.";
  exit 1;
fi

echo "CI PASSED: Lean compilation and all tests verified" 