#!/usr/bin/env bash
set -euo pipefail

# Single CI entry-point – executes all checks via veritas
veritas check

echo "CI ✓ – all green" 