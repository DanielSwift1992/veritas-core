#!/usr/bin/env bash
set -euo pipefail

# Single CI entry-point – executes all checks via veritas
python -m veritas.cli check

# Generate SBOM (optional, non-fatal)
scripts/generate_sbom.sh || echo "SBOM generation skipped"

echo "CI ✓ – all green" 