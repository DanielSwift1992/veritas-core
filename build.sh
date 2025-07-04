#!/usr/bin/env bash
set -euo pipefail

# Simple CI driver – delegate to Veritas

veritas check --markdown "$@"

# Ensure README and status.yml consistent
if ! git diff --exit-code README.md status.yml >/dev/null; then
  echo "[error] README.md or status.yml out of date. Commit auto-generated changes." >&2
  exit 1
fi

echo "CI PASSED – Veritas checks green" 