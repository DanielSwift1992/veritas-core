#!/usr/bin/env bash
set -euo pipefail

# Generate CycloneDX SBOM for the current Python environment
# Requires cyclonedx-bom; install if missing.
if ! command -v cyclonedx-py &> /dev/null; then
  pip install --quiet cyclonedx-bom
fi

cyclonedx-py env -o sbom.json

echo "[security] SBOM generated → sbom.json" 