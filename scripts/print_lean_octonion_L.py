#!/usr/bin/env python3
"""
Print the 7 octonion left-multiplication matrices L(e_1)..L(e_7) and Δ from
HQVM/matrices.py as Lean 4 definitions.

Same paths as print_lean_generators.py:
  cd ~/Repos/HQIV_LEAN
  PYTHONPATH=~/Repos/HQIV python3 scripts/print_lean_octonion_L.py

Paste the output into Hqiv/OctonionLeftMultiplication.lean (or GeneratorsFromAxioms.lean).
Used to prove the 28 so(8) generators come from the first assumptions (L, Δ, Lie closure).
"""

from __future__ import annotations

import sys
from pathlib import Path

_REPO_LEAN = Path(__file__).resolve().parent.parent
_REPO_HQIV = _REPO_LEAN.parent / "HQIV"
if _REPO_HQIV.exists():
    sys.path.insert(0, str(_REPO_HQIV))

TOL = 1e-12

def to_lean_real(x: float) -> str:
    if abs(x) < TOL:
        return "(0 : ℝ)"
    if abs(x - 1) < TOL:
        return "(1 : ℝ)"
    if abs(x + 1) < TOL:
        return "(-1 : ℝ)"
    return f"({x:.14g} : ℝ)"

def matrix_to_lean(M) -> str:
    rows = []
    for i in range(8):
        row = ", ".join(to_lean_real(float(M[i][j])) for j in range(8))
        rows.append("    " + row)
    return "!![\n" + ";\n".join(rows) + "\n  ]"

def main() -> None:
    try:
        from HQVM.matrices import OctonionHQIVAlgebra
    except Exception as e:
        print("-- Could not import HQVM.matrices.OctonionHQIVAlgebra.", file=sys.stderr)
        print("-- Error:", e, file=sys.stderr)
        print("-- Run: cd ~/Repos/HQIV_LEAN && PYTHONPATH=~/Repos/HQIV python3 scripts/print_lean_octonion_L.py", file=sys.stderr)
        sys.exit(1)

    alg = OctonionHQIVAlgebra(verbose=False)
    # alg.L is list of 7 matrices: L(e_1) .. L(e_7)
    print("-- Octonion left-multiplication matrices L(e_1) .. L(e_7) from matrices.py (Fano plane).")
    print("-- Paste into Hqiv/OctonionLeftMultiplication.lean")
    print()
    for k, B in enumerate(alg.L):
        M = B.tolist() if hasattr(B, "tolist") else list(B)
        print(f"/-- L(e_{k+1}) (imaginary unit {k+1}). -/")
        print(f"def octonionLeftMul_{k+1} : Matrix (Fin 8) (Fin 8) ℝ := {matrix_to_lean(M)}")
        print()
    print("-- Δ (phase-lift) is already defined in GeneratorsFromAxioms as phaseLiftDelta.")
    D = alg.Delta.tolist() if hasattr(alg.Delta, "tolist") else list(alg.Delta)
    print("-- For reference, Delta from matrices.py:")
    print(f"-- def phaseLiftDelta : Matrix (Fin 8) (Fin 8) ℝ := {matrix_to_lean(D)}")
    print()
    print("-- Next: prove each L(e_i) and Δ lie in the span of the 28 so8Generators.")

if __name__ == "__main__":
    main()
