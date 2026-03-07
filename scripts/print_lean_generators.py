#!/usr/bin/env python3
"""
Print the 28 so(8) generators from HQVM/matrices.py as Lean 4 theorems.

Paths (with ~ = /home/jr):
  HQIV_LEAN = ~/Repos/HQIV_LEAN   (this Lean project)
  HQIV      = ~/Repos/HQIV        (HQVM lives inside this repo)

To generate the matrices, run ONE of these from a terminal:

  Option A — from HQIV_LEAN (recommended):
    cd ~/Repos/HQIV_LEAN
    PYTHONPATH=~/Repos/HQIV python3 scripts/print_lean_generators.py

  Option B — from HQIV:
    cd ~/Repos/HQIV
    python3 ~/Repos/HQIV_LEAN/scripts/print_lean_generators.py

The script adds ~/Repos/HQIV to sys.path so "from HQVM.matrices import ..."
finds HQIV/HQVM/matrices.py. Copy the printed defs into Hqiv/Generators.lean
(replace the placeholder generator_0 .. generator_27), then fill gaps manually.
"""

from __future__ import annotations

import sys
from pathlib import Path

# So "from HQVM.matrices import ..." finds HQIV/HQVM/matrices.py
_REPO_LEAN = Path(__file__).resolve().parent.parent  # HQIV_LEAN
_REPO_HQIV = _REPO_LEAN.parent / "HQIV"              # sibling repo ~/Repos/HQIV
if _REPO_HQIV.exists():
    sys.path.insert(0, str(_REPO_HQIV))

TOL = 1e-12  # treat |x| < TOL as 0 for Lean output


def to_lean_real(x: float) -> str:
    if abs(x) < TOL:
        return "(0 : ℝ)"
    if abs(x - 1) < TOL:
        return "(1 : ℝ)"
    if abs(x + 1) < TOL:
        return "(-1 : ℝ)"
    return f"({x:.14g} : ℝ)"


def matrix_to_lean(M) -> str:
    """Format an 8x8 matrix M (list of lists or numpy array) as Lean !![...] literal."""
    rows = []
    for i in range(8):
        row = ", ".join(to_lean_real(float(M[i][j])) for j in range(8))
        rows.append("    " + row)
    return "!![\n" + ";\n".join(rows) + "\n  ]"


def matrix_to_lean_match(M) -> str:
    """Format an 8x8 matrix as Matrix.of (fun i j => match i, j with ...) so (M i j) reduces for all i, j."""
    lines = ["  match i, j with"]
    for i in range(8):
        row_vals = [to_lean_real(float(M[i][j])) for j in range(8)]
        line = f"  | {i}, 0 => {row_vals[0]} | {i}, 1 => {row_vals[1]} | {i}, 2 => {row_vals[2]} | {i}, 3 => {row_vals[3]} | {i}, 4 => {row_vals[4]} | {i}, 5 => {row_vals[5]} | {i}, 6 => {row_vals[6]} | {i}, 7 => {row_vals[7]}"
        lines.append(line)
    lines.append("  )")
    return "Matrix.of (fun i j =>\n" + "\n".join(lines)


def main() -> None:
    import argparse
    parser = argparse.ArgumentParser(description="Print so(8) generators as Lean 4 definitions.")
    parser.add_argument("--match", action="store_true", help="Use Matrix.of + match form so (M i j) reduces (fixes antisymm proof).")
    args = parser.parse_args()
    use_match = args.match
    try:
        import numpy as np
    except ImportError:
        print(" numpy not found; install with: pip install numpy", file=sys.stderr)
        sys.exit(1)

    basis = None
    # Try common entry points from the skill file
    try:
        from HQVM.matrices import OctonionHQIVAlgebra
        alg = OctonionHQIVAlgebra(verbose=False)
        dim, _ = alg.lie_closure_dimension(tol=1e-10)
        basis = alg.lie_closure_basis(tol=1e-10)
    except Exception as e:
        try:
            # Alternative: some codebases expose get_so8_basis or similar
            from HQVM import matrices as m
            if hasattr(m, "lie_closure_basis"):
                basis = m.lie_closure_basis(tol=1e-10)
            elif hasattr(m, "get_so8_basis"):
                basis = m.get_so8_basis()
        except Exception as e2:
            pass
        if basis is None:
            print("-- Could not import HQVM.matrices or get 28 basis matrices.", file=sys.stderr)
            print("-- Error:", e, file=sys.stderr)
            print("-- Run this script from the HQIV repo root (parent of HQVM), or set PYTHONPATH.", file=sys.stderr)
            print("-- Example output format for one generator (paste into Hqiv/Generators.lean):", file=sys.stderr)
            print()
            # Print one placeholder so the user sees the format
            zero = [[0.0] * 8 for _ in range(8)]
            print("/-- Placeholder (replace with output from matrices.py). -/")
            print("def generator_0 : Matrix (Fin 8) (Fin 8) ℝ := " + matrix_to_lean(zero))
            sys.exit(1)

    if len(basis) != 28:
        print(f"-- Warning: expected 28 generators, got {len(basis)}", file=sys.stderr)

    print("-- Paste the following into Hqiv/Generators.lean (replace the placeholder defs).")
    print("-- Generated from matrices.py lie_closure_basis." + (" Match form for reduction." if use_match else ""))
    print()
    for k, B in enumerate(basis):
        if k >= 28:
            break
        M = B.tolist() if hasattr(B, "tolist") else list(B)
        print(f"/-- Generator {k} (from matrices.py lie_closure_basis). -/")
        if use_match:
            print(f"def generator_{k} : Matrix (Fin 8) (Fin 8) ℝ := {matrix_to_lean_match(M)}")
        else:
            print(f"def generator_{k} : Matrix (Fin 8) (Fin 8) ℝ := {matrix_to_lean(M)}")
        print()
    print("-- Then define so8Generator (k : Fin 28) by matching k to generator_0 .. generator_27")
    print("-- and add theorems generator_k_eq : so8Generator k = generator_k := rfl.")
    if use_match:
        print("-- Antisymm proofs: use simp only [generator_K, Matrix.of_apply, add_apply, transpose_apply, zero_apply]; all_goals norm_num")


if __name__ == "__main__":
    main()
