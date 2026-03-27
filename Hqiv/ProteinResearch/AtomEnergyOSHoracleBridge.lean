import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.BoundStates
import Hqiv.QuantumComputing.DiscreteQuantumState
import Hqiv.QuantumComputing.OSHoracle

/-!
# Atom / multi-site energy matrices and OSHoracle sparse carriers

This module packages **additive, non-interacting** atomic (or site) energy bookkeeping into
real diagonal matrices, using only objects already in the HQIV closure:

* **Light-cone mode counting** `Hqiv.available_modes` and the auxiliary-field ladder
  `phi_of_shell` (`OctonionicLightCone`, `AuxiliaryField`),
* **Hydrogenic shell binding** `expectedGroundEnergyAtShell` (`BoundStates`, φ-driven α_eff),
* **OSHoracle** sparse registers (`OSHoracle`) with octonion basis carriers (`OctonionBasics`).

**Residual limitation (explicit):** matrices are **diagonal** in a fixed product basis (no
Coulomb coupling between sites in the matrix itself). Cross-terms belong in separate
two-body potentials (e.g. `valleyPotentialEM` in `HQIVAtoms`), not in this bridge.

No new axioms, no `sorry`, no floating-point numerics.
-/

namespace Hqiv.ProteinResearch

open scoped BigOperators
open Matrix
open Finset
open Hqiv
open Hqiv.Algebra
open Hqiv.Physics
open Hqiv.QuantumComputing

variable {n : ℕ}

/-- Per-shell **full lattice zero-point budget** (one `φ(m)/2` contribution per available mode,
ℏ = 1), matching the Casimir-style sum used in `HQIVNuclei.electronShellCasimirEnergy`. -/
noncomputable def latticeFullModeEnergy (m : ℕ) : ℝ :=
  Hqiv.available_modes m * (phi_of_shell m / 2)

/-- Diagonal matrix of independent site energies on `Fin n` (additive atomic / cluster model). -/
noncomputable def atomSiteEnergyMatrix (shell : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => latticeFullModeEnergy (shell i)

/-- Diagonal matrix of hydrogenic **ground** energies per site from `BoundStates`. -/
noncomputable def atomBindingGroundMatrix (shell : Fin n → ℕ) (Z : Fin n → ℕ) (μ c : ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => expectedGroundEnergyAtShell (shell i) (Z i) μ c

/-- Rational **φ-ladder shadow** matrix (same diagonal shape, values in `ℚ`). -/
def phiRatSiteMatrix (shell : Fin n → ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  diagonal fun i => phiRat (shell i)

theorem trace_atomSiteEnergyMatrix (shell : Fin n → ℕ) :
    trace (atomSiteEnergyMatrix shell) = ∑ i : Fin n, latticeFullModeEnergy (shell i) := by
  simp [atomSiteEnergyMatrix, trace_diagonal]

theorem trace_atomBindingGroundMatrix (shell : Fin n → ℕ) (Z : Fin n → ℕ) (μ c : ℝ) :
    trace (atomBindingGroundMatrix shell Z μ c)
      = ∑ i : Fin n, expectedGroundEnergyAtShell (shell i) (Z i) μ c := by
  simp [atomBindingGroundMatrix, trace_diagonal]

theorem trace_phiRatSiteMatrix (shell : Fin n → ℕ) :
    trace (phiRatSiteMatrix shell) = ∑ i : Fin n, phiRat (shell i) := by
  simp [phiRatSiteMatrix, trace_diagonal]

theorem atomSiteEnergyMatrix_isDiagonal (shell : Fin n → ℕ) (i j : Fin n) (hij : i ≠ j) :
    atomSiteEnergyMatrix shell i j = 0 := by
  simp [atomSiteEnergyMatrix, hij]

theorem atomBindingGroundMatrix_isDiagonal (shell : Fin n → ℕ) (Z : Fin n → ℕ) (μ c : ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    atomBindingGroundMatrix shell Z μ c i j = 0 := by
  simp [atomBindingGroundMatrix, hij]

/-- Standard basis octonions are **unit norm** in `octonionInner`. -/
theorem octonionBasis_unit (i : Fin 8) :
    octonionInner (octonionBasis i) (octonionBasis i) = 1 := by
  simp [octonionInner, octonionBasis]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij
    simp [octonionBasis, if_neg hij]
  · exact Finset.mem_univ i

/-- Site carrier in the octonion basis: shell index picks an imaginary direction modulo 8. -/
def siteOctonionCarrier (shellAtSite : ℕ) : OctonionVec :=
  octonionBasis ⟨shellAtSite % 8, Nat.mod_lt _ (by decide : 0 < 8)⟩

theorem siteOctonionCarrier_unit (s : ℕ) :
    octonionInner (siteOctonionCarrier s) (siteOctonionCarrier s) = 1 := by
  unfold siteOctonionCarrier
  exact octonionBasis_unit _

/-- Sum of per-ket norms along `List.range n`; each term is 1 regardless of `shells.getD`. -/
theorem sum_sparse_octonion_norm_range (shells : List ℕ) (n : ℕ) :
    (List.range n).map (fun i =>
        octonionInner (siteOctonionCarrier (shells.getD i 0)) (siteOctonionCarrier (shells.getD i 0)))
      |>.sum
      = (n : ℝ) := by
  induction n with
  | zero =>
      simp
  | succ k ih =>
      rw [Nat.succ_eq_add_one, List.range_succ, List.map_append, List.sum_append, List.map_singleton,
        List.sum_singleton]
      rw [ih, siteOctonionCarrier_unit]
      simp [Nat.cast_succ]

/-- Build an OSHoracle sparse register: one ket per list position, wrapped index, octonion carrier. -/
def sparseRegisterOfShells (L : ℕ) (shells : List ℕ) : SparseRegister L :=
  (List.range shells.length).map fun i =>
    (wrapIdx L i, siteOctonionCarrier (shells.getD i 0))

theorem sparseRegisterOfShells_length (L : ℕ) (shells : List ℕ) :
    (sparseRegisterOfShells L shells).length = shells.length := by
  simp [sparseRegisterOfShells]

theorem sparseRegisterOfShells_normSq (L : ℕ) (shells : List ℕ) :
    sparseNormSq (sparseRegisterOfShells L shells) = (shells.length : ℝ) := by
  unfold sparseNormSq sparseRegisterOfShells
  simpa using sum_sparse_octonion_norm_range shells shells.length

/-- Sum of lattice energies along the same site indices as `sparseRegisterOfShells`. -/
noncomputable def listLatticeEnergySum (shells : List ℕ) : ℝ :=
  (List.range shells.length).map (fun i => latticeFullModeEnergy (shells.getD i 0)) |>.sum

/-!
## Cast alignment: rational φ matrix shadow vs real ladder

`phiRat_coe_eq_phi_of_shell` is stated per shell in `DiscreteQuantumState`; summing over sites
commutes with casting `ℚ → ℝ`.
-/

theorem phiRat_trace_coe_eq_real_sum (shell : Fin n → ℕ) :
    (∑ i : Fin n, (phiRat (shell i) : ℝ)) = ∑ i : Fin n, phi_of_shell (shell i) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  exact phiRat_coe_eq_phi_of_shell (shell i)

#print latticeFullModeEnergy
#print atomSiteEnergyMatrix
#print atomBindingGroundMatrix
#print phiRatSiteMatrix
#print sparseRegisterOfShells
#print listLatticeEnergySum

#check trace_atomSiteEnergyMatrix
#check trace_atomBindingGroundMatrix
#check trace_phiRatSiteMatrix
#check sparseRegisterOfShells_length
#check sparseRegisterOfShells_normSq
#check octonionBasis_unit
#check phiRat_trace_coe_eq_real_sum

end Hqiv.ProteinResearch
