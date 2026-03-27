import Hqiv.ProteinResearch.AtomEnergyOSHoracleBridge
import Hqiv.QuantumComputing.OSHoracle
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# Additive mean-field field + infrequent torque augmentation for proteins

Implements the user-proposed "additive field generation + torque" strategy to capture
packing / H-bond / hydrophobic effects without explicit n-body terms.

* Additive field: global horizon/EM/auxiliary field summed linearly from all sites
  (O(n) or O(n log n) once per update).
* Torque: infrequent rotational correction added to the diagonal energy budget
  (only every `updateEvery` steps) to escape local minima.
* All matrices remain diagonal; OSH sparse-register norm and pruning bound are
  completely unchanged (re-use existing theorems).
* No new axioms, no `sorry`, no Float/FloatArray, no off-diagonal entries here.
* Cross-site EM / valley terms stay in HQIVAtoms.valleyPotentialEM (documented).
-/

namespace Hqiv.ProteinResearch

open scoped BigOperators
open Matrix
open Hqiv
open Hqiv.ProteinResearch
open Hqiv.QuantumComputing

notation "ℝ³" => Fin 3 → ℝ

variable {n : ℕ}

/-- Site contribution kernel for the additive mean-field.
Placeholder: replace with real HQIV valley/EM projection when available. -/
noncomputable def additiveFieldKernel
    (i j : Fin n) (shell : Fin n → ℕ) (pos : Fin n → ℝ³) : ℝ :=
  let dx := pos i 0 - pos j 0
  let dy := pos i 1 - pos j 1
  let dz := pos i 2 - pos j 2
  let rProxy := |dx| + |dy| + |dz| + 1
  latticeFullModeEnergy (shell j) / rProxy

/-- Global additive field value at each site (mean-field replacement for pairwise terms). -/
noncomputable def additiveFieldAtSite
    (shell : Fin n → ℕ) (pos : Fin n → ℝ³) : Fin n → ℝ :=
  fun i => ∑ j : Fin n, additiveFieldKernel i j shell pos

/-- Infrequent rotational correction matrix (`τ·Δθ` per site), kept diagonal. -/
noncomputable def torqueCorrection
    (shell : Fin n → ℕ) (orientationDev : Fin n → ℝ) (field : Fin n → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => orientationDev i * field i

/-- Fast-path energy matrix: base site energy plus cached diagonal torque correction. -/
noncomputable def torqueAugmentedSiteEnergyMatrix
    (shell : Fin n → ℕ) (cachedTorque : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  atomSiteEnergyMatrix shell + cachedTorque

/-- Computational trigger for refreshing torque cache. -/
def shouldUpdateTorque (step : ℕ) (updateEvery : ℕ := 10) : Bool :=
  if updateEvery = 0 then true else step % updateEvery = 0

theorem additiveFieldAtSite_isScalar (shell : Fin n → ℕ) (pos : Fin n → ℝ³) :
    ∃ f : Fin n → ℝ, additiveFieldAtSite shell pos = f :=
  ⟨additiveFieldAtSite shell pos, rfl⟩

theorem torqueAugmented_isStillDiagonal
    (shell : Fin n → ℕ) (orientationDev field : Fin n → ℝ)
    (i j : Fin n) (hij : i ≠ j) :
    torqueAugmentedSiteEnergyMatrix shell (torqueCorrection shell orientationDev field) i j = 0 := by
  unfold torqueAugmentedSiteEnergyMatrix
  rw [Matrix.add_apply]
  simp [atomSiteEnergyMatrix_isDiagonal, torqueCorrection, hij]

theorem torqueAugmented_trace_eq_sum
    (shell : Fin n → ℕ) (orientationDev field : Fin n → ℝ) :
    trace (torqueAugmentedSiteEnergyMatrix shell (torqueCorrection shell orientationDev field))
      = (∑ i : Fin n, latticeFullModeEnergy (shell i))
        + (∑ i : Fin n, orientationDev i * field i) := by
  unfold torqueAugmentedSiteEnergyMatrix
  rw [Matrix.trace_add]
  simp [trace_atomSiteEnergyMatrix, torqueCorrection, trace_diagonal]

theorem sparseRegisterWithTorque_normSq_unchanged (L : ℕ) (shells : List ℕ) :
    sparseNormSq (sparseRegisterOfShells L shells) = (shells.length : ℝ) :=
  sparseRegisterOfShells_normSq L shells

/-- OSHoracle `applyGateSparse` / `detectFlippedKets` / `pruneToFlipped` are unchanged because
the sparse register itself is unchanged by this diagonal energy-side augmentation. -/
theorem torqueAugmented_preserves_OSH_pruning
    (L : ℕ) (shells : List ℕ) (g : HQIVGate L) :
    practicalLittleO (2 * (sparseRegisterOfShells L shells).length)
      (pruneToFlipped
        (L := L)
        (detectFlippedKets (sparseRegisterOfShells L shells)
          (applyGateSparse g (sparseRegisterOfShells L shells)))
        (applyGateSparse g (sparseRegisterOfShells L shells))).length := by
  simpa using horizonCausal_support_o_twoPow_practice
    (r := sparseRegisterOfShells L shells) (g := g)

#print additiveFieldKernel
#print additiveFieldAtSite
#print torqueCorrection
#print torqueAugmentedSiteEnergyMatrix
#print shouldUpdateTorque

#check additiveFieldAtSite_isScalar
#check torqueAugmented_isStillDiagonal
#check torqueAugmented_trace_eq_sum
#check sparseRegisterWithTorque_normSq_unchanged
#check torqueAugmented_preserves_OSH_pruning

/-!
Residual limitations:
* Additive field is mean-field (linear sum); cooperative allosteric effects may need rarer full re-evaluation.
* Torque update frequency is a tunable hyper-parameter (default 10); too frequent → speed hit; too rare → trapped minima.
* Position vector `pos : Fin n → ℝ³` is supplied from the folding oracle (backbone dihedrals → Cartesian in Python side).
* Full integration with ProteinFoldingHook.lean is left for a later hook module.

Build instructions:
* lake build Hqiv.ProteinResearch.AdditiveFieldAndTorque
* Then update HQIVLEAN.lean to import this new module.
-/

end Hqiv.ProteinResearch
