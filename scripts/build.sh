#!/usr/bin/env bash
# Avoid exit 134 (stack overflow in GeneratorsLieClosureData).
# No args: build HQIVPhysics only (geometry + physics, no generator stack).
# With args: set larger stack and run lake build (e.g. ./scripts/build.sh HQIVLEAN).
# Run this script from a terminal; IDE-triggered builds may not inherit ulimit.
set -e
if [[ $# -eq 0 ]]; then
  exec lake build HQIVPhysics
else
  ulimit -s 131072 2>/dev/null || ulimit -s 65536 2>/dev/null || true
  exec lake build "$@"
fi
