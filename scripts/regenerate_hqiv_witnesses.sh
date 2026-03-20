#!/usr/bin/env bash
# Regenerate `data/hqiv_witnesses.json`.
#
# This requires compiling Lean dependencies (heavy). Use only when you
# explicitly want to re-derive witnesses from the current Lean sources.
set -euo pipefail

cd "$(dirname "$0")/.."

echo "Regenerating data/hqiv_witnesses.json ..."

# Ensure Python path doesn't matter for Lean; witnesses are Lean-exported.
lake env lean -q --run scripts/export_witnesses.lean

echo "Done."

