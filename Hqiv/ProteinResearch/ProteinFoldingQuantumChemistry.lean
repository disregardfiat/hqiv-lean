import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

import Hqiv.ProteinResearch.AtomEnergyOSHoracleBridge

/-!
# Protein folding: quantum-chemistry justification layer (finite sites, Python-aligned)

This module is the **Lean contract** for the external Python folding stack:

* **Numbers** (coordinates, energies, gradients) are computed in Python.
* **Structure** (additive site budgets, nonnegative traces) is proved here so the numerics sit on
  HQIV definitions rather than ad hoc energies.

## Site-only / mean-field channel (`AtomEnergyOSHoracleBridge`)

* Per-residue horizon shell `m` maps to a **diagonal** site energy
  `latticeFullModeEnergy m = available_modes m * (φ(m)/2)` (ℏ = 1 convention in-bridge).
* Summing sites is **trace** of `atomSiteEnergyMatrix` — see `trace_atomSiteEnergyMatrix`.

## Coupling / hierarchical chemistry (separate formal chain)

Hierarchical **bond + bulk** folding energies (`foldEnergy`, `assemblyEnergy`) are proved in
`Hqiv.Physics.HQIVMolecules` / `HQIVAssembly` when that import chain is available; this file does
**not** import them (current `lake` graph: `HQIVNuclei` blocks the full molecules build). The Python
pipeline should still implement **E = E_site(HQIV) + E_pair** as separate summands; Lean pins
**nonnegativity and traceability of the HQIV site block** here.

## Dynamics

See `Hqiv.ProteinResearch.ProteinHKEMinimizer` (`HKEMinimizerSpec`) — abstract class for optimizers
that do not increase the formal `HKE` objective on coordinates.

No new `axiom`, no `sorry`, no floating-point.
-/

namespace Hqiv.ProteinResearch

open scoped BigOperators
open Matrix Finset
open Hqiv

variable {n : ℕ}

/-- Per-shell lattice zero-point site energy is nonnegative (modes ≥ 0, φ > 0). -/
theorem latticeFullModeEnergy_nonneg (m : ℕ) : 0 ≤ latticeFullModeEnergy m := by
  unfold latticeFullModeEnergy
  have hν : 0 ≤ Hqiv.available_modes m := by
    rw [Hqiv.available_modes_eq]
    have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hm]
  have hφ : 0 < phi_of_shell m := phi_of_shell_pos m
  have hhalf : 0 ≤ phi_of_shell m / 2 := by linarith
  exact mul_nonneg hν hhalf

/-- List-aligned site sum is nonnegative — matches a nonnegative Python port per residue. -/
theorem listLatticeEnergySum_nonneg (shells : List ℕ) : 0 ≤ listLatticeEnergySum shells := by
  unfold listLatticeEnergySum
  let R := List.range shells.length
  have hsum : 0 ≤ (R.map (fun i => latticeFullModeEnergy (shells.getD i 0))).sum := by
    induction R with
    | nil => simp
    | cons _ as ih =>
        simp [List.map_cons, List.sum_cons]
        exact add_nonneg (latticeFullModeEnergy_nonneg _) ih
  exact hsum

/-- Diagonal atomic site trace is nonnegative. -/
theorem atomSiteEnergyMatrix_trace_nonneg (shell : Fin n → ℕ) :
    0 ≤ trace (atomSiteEnergyMatrix shell) := by
  rw [trace_atomSiteEnergyMatrix]
  refine Finset.sum_nonneg fun i _ => latticeFullModeEnergy_nonneg _

/-!
## Fin-indexed residues = Python array layout

`Fin n → ℕ` is the typed version of a length-`n` shell vector passed from Python.
-/

structure ProteinFoldingSiteEnergySpec (n : ℕ) where
  /-- HQIV shell per residue / site. -/
  shell : Fin n → ℕ

/-- Canonical HQIV diagonal site energy trace for a folding configuration. -/
noncomputable def siteEnergyTrace {n : ℕ} (s : ProteinFoldingSiteEnergySpec n) : ℝ :=
  trace (atomSiteEnergyMatrix s.shell)

theorem siteEnergyTrace_nonneg (s : ProteinFoldingSiteEnergySpec n) : 0 ≤ siteEnergyTrace s :=
  atomSiteEnergyMatrix_trace_nonneg s.shell

end Hqiv.ProteinResearch
