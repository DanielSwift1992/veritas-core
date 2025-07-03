#!/usr/bin/env bash
set -euo pipefail

cd ../proofs
lake build
lean --run TableCorrespondence.lean 