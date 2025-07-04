#!/usr/bin/env bash
set -euo pipefail

# Single CI entry-point – executes all checks via veritas
python -m veritas.cli check

echo "CI ✓ – all green" 