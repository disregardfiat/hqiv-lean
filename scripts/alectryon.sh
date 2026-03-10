#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

OUTDIR="$ROOT/docs/interactive"
mkdir -p "$OUTDIR"

ALECTRYON="alectryon"
if ! command -v "$ALECTRYON" >/dev/null 2>&1; then
  if [[ -x "$ROOT/.venv/bin/alectryon" ]]; then
    ALECTRYON="$ROOT/.venv/bin/alectryon"
  else
    echo "error: 'alectryon' not found (PATH nor ./.venv/bin/alectryon)" >&2
    echo "hint: python3 -m venv .venv && . .venv/bin/activate && pip install -r requirements.txt" >&2
    exit 127
  fi
fi

if ! command -v leanInk >/dev/null 2>&1; then
  echo "error: 'leanInk' not found in PATH (required for Lean 4 annotation)" >&2
  echo "hint: install LeanInk (binary) from https://github.com/leanprover/LeanInk#installation" >&2
  echo "hint: run: sh -c \"\$(curl -sSf https://raw.githubusercontent.com/leanprover/LeanInk/main/init.sh)\"" >&2
  exit 127
fi

echo "[Alectryon] Rendering interactive HTML into docs/interactive/ …" >&2

render_one () {
  local in="$1"
  local base="$2"
  local out="$OUTDIR/$base.html"

  if [[ ! -f "$ROOT/$in" ]]; then
    echo "error: missing input file: $in" >&2
    exit 2
  fi

  # Prefer inheriting LEAN_PATH from `lake build Alectryon` (no nested Lake).
  # Also pass `--lake lakefile.lean` so LeanInk runs with the correct Lake
  # project context (resolving mathlib + local packages).
  if [[ -n "${LEAN_PATH:-}" ]]; then
    "$ALECTRYON" --frontend lean4 --lake lakefile.lean -o "$out" "$in"
  else
    lake env "$ALECTRYON" --frontend lean4 --lake lakefile.lean -o "$out" "$in"
  fi
  echo "  wrote: $out" >&2
}

render_one "Hqiv/Algebra/Triality.lean" "Triality"
render_one "Hqiv/Algebra/SMEmbedding.lean" "SMEmbedding"
render_one "Hqiv/Algebra/AnomalyCancellation.lean" "AnomalyCancellation"
render_one "Hqiv/Physics/SM_GR_Unification.lean" "SM_GR_Unification"

echo "[Alectryon] Done." >&2
