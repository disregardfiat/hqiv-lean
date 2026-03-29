import Mathlib.Algebra.Order.Floor.Semiring
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric
import Hqiv.Physics.ContinuumOmaxwellClosure
import Hqiv.QuantumMechanics.HorizonLimitedRenormLocality
import Hqiv.QuantumMechanics.MinkowskiFieldOperatorScaffold
import Hqiv.QuantumMechanics.PauliCommutatorExample
import Hqiv.QuantumMechanics.CCRFiniteDimObstruction
import Hqiv.QuantumMechanics.LocalAlgebraNetScaffold
import Hqiv.QuantumMechanics.PatchQFTBridge

/-!
# Light cone → continuum Maxwell → QM/QFT scaffold (functional link)

This module is the **single import hub** for the idea:

* **Down (geometry / same null ladder):** discrete light-cone data (`Hqiv.Geometry.OctonionicLightCone`, mode
  capacity) feeds **continuum** φ–Maxwell slots on `Fin 4 → ℝ` via
  `Hqiv.Physics.ContinuumOmaxwellClosure` and metric-raised gradients in
  `Hqiv.Geometry.ContinuumMetricGradient`.

* **Mass/couplings (same ladder):** `Hqiv.Physics.HarmonicLadderMass` proves the definitional
  chain from `phi_of_shell` / `shell_shape` through `one_over_alpha_eff` and `alphaEffAtShell` to
  hydrogenic binding scales at shell `m`.

* **Up (same ladder → asymptotic modes):** the **proved** shell/harmonic ratio limit
  (`shell_to_harmonic_limit_holds` in `ContinuumManyBodyQFTScaffold`) is exactly the first
  `HorizonContinuumAxiomsMinimal.shell_to_harmonic_limit` obligation used in
  `HorizonLimitedRenormLocality`.

`LightConeFunctionalBridge` pairs a **minimal axiom record** with a **proof** of its shell slot, so you
do not “cross a valley” informally: `toContinuumClosureHQIV` is just
`horizon_continuum_closure_minimal_HQIV` with that bundle, and `toFullPackageMinimalHQIV` is the same
for `horizon_qm_qft_full_package_minimal_HQIV` (finite Born/kernel layer + that continuum conclusion).

Renorm/cluster/scattering in `horizonContinuumAxiomsMinimal_ratioWitness` use **structured**
scaffold witnesses (`renormalization_in_domain_trivial_holds`, `cluster_decomposition_zero_kernel_holds`,
`scattering_consistency_zero_channel_holds`). For **Minkowski** microcausality, see
`continuum_many_body_closure_minkowskiMicroWitness` (zero commutator kernel) and
`continuum_many_body_closure_minkowskiIntervalWitness` (`commutatorKernelIntervalMax` = `max 0 η`, nontrivial
on timelike pairs — `ContinuumManyBodyQFTScaffold`).  **Operators on `ℂ⁴`:** `MinkowskiFieldOperatorScaffold`
(`fieldOpFromChart`) and `HorizonFreeFieldScaffold.opCommutator`; **noncommutative toy:** `PauliCommutatorExample`;
**no exact CCR on finite matrices:** `CCRFiniteDimObstruction.not_exists_matrix_CCR_one`; **local net scaffold:**
`LocalAlgebraNetScaffold.diagonalSmearedNet` (isotony + commuting regions); **support-restricted patch net**
(`patchAlgebraAt`, `WeightSupportInRegion`, `patchChartPoint`, `patchEventChartFour`,
`spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions`) in `PatchQFTBridge`.  **Finite patch + limit:**
`accessibleModeBudgetUpToShell`, `accessibleModeBudgetUpToShell_eq_sum_new_modes`,
`accessiblePatch_modeBudget_div_harmonic_tends_four`, `accessiblePatch_shellToHarmonicLimit`,
`PhotonHorizonModeLimit` / `PhotonHorizonModeLimitValue` / `photonHorizonModeLimit_tendsto` (**definite** ratio
limit **`4`** — photon-sector / null-ladder vs `S²` harmonics).
**Time ↔ shell (same ladder as `phi_of_shell`, `timeAngle`):** `shellIndexFromTimeAngle`,
`accessibleModeBudgetUpToTimeAngle`, `accessibleModeBudgetUpToPhiTime`, and the unit-time budget match
(`accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit`).  Next layers: region-restricted
supports tied to the light-cone patch—without positing a single global infinite-dimensional Hilbert space
as the HQIV setting.
-/

namespace Hqiv.Physics

open scoped BigOperators Topology
open Finset Filter Topology
open Hqiv
open Hqiv.QM

/-- Same chart type as `coordsGradientComponents` / `contravariantGradientComponentsAt` (continuum hook). -/
abbrev MaxwellQFTChart : Type :=
  Fin 4 → ℝ

/-!
## Discrete ladder → continuum axiom (same object as `ContinuumManyBodyQFTScaffold`)

The shell/harmonic ratio limit is proved from `Hqiv.available_modes` and
`sphericalHarmonicCumulativeCount` (via `SphericalHarmonicsBridge`); this is the discrete
light-cone capacity feeding the first `HorizonContinuumAxiomsMinimal` slot in the QM/QFT package.

### Finite patch (“accessible up to shell `M`”)

HQIV does **not** require a global infinite-dimensional carrier: formal statements live on **finite**
cutoffs, with **asymptotic** content packaged as limits as the shell index grows. The ℝ-valued budget
for shells `0 … M` inclusive is exactly `Hqiv.available_modes M` — cumulative new modes on the null
lattice (`Hqiv.sum_new_modes_eq_available_modes`). The named alias `accessibleModeBudgetUpToShell`
makes that “patch size” reading grepable and ties one place to the shell→harmonic ratio limit.

### Time angle `φ·t` ↔ discrete shell (HQVM × auxiliary ladder)

On the HQVM track, `Hqiv.timeAngle φ t = φ * t` (`HQVMetric`).  Tying `φ` to the shell ladder via
`φ = phi_of_shell m` gives `timeAngle (phi_of_shell m) t = 2 (m+1) t` (`phi_of_shell_closed_form`).
Normalizing by `phiTemperatureCoeff = 2` yields `(m+1) t - 1` after subtracting `1`, whose nonnegative
floor is a **discrete shell index** scaffold (`shellIndexFromTimeAngle`).  At **unit coordinate time**
`t = 1`, this floor is exactly `m`, so the mode budget matches `accessibleModeBudgetUpToShell m`
(`accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit`).
-/

/-- ℝ-valued **accessible mode budget** on shells `0 … M` inclusive: cumulative capacity on the
discrete null ladder (`Hqiv.sum_new_modes_eq_available_modes`). Same as `Hqiv.available_modes M`. -/
noncomputable def accessibleModeBudgetUpToShell (M : ℕ) : ℝ :=
  Hqiv.available_modes M

@[simp]
theorem accessibleModeBudgetUpToShell_eq_available (M : ℕ) :
    accessibleModeBudgetUpToShell M = Hqiv.available_modes M :=
  rfl

theorem accessibleModeBudgetUpToShell_eq_sum_new_modes (M : ℕ) :
    accessibleModeBudgetUpToShell M = ∑ i ∈ range (M + 1), Hqiv.new_modes i :=
  (Hqiv.sum_new_modes_eq_available_modes M).symm

/-- Ratio built from the per-patch budget tends to the octonion factor `4` as `M → ∞`
(same `Tendsto` as `continuum_shell_harmonic_ratio_limit` / `shell_to_harmonic_limit_holds`). -/
theorem accessiblePatch_modeBudget_div_harmonic_tends_four :
    Tendsto (fun M : ℕ => accessibleModeBudgetUpToShell M / Hqiv.sphericalHarmonicCumulativeCount M)
      atTop (𝓝 (4 : ℝ)) := by
  simpa [accessibleModeBudgetUpToShell] using continuum_shell_harmonic_ratio_limit

/-- `ShellToHarmonicLimit` — same proposition and proof as `lightCone_discreteModes_shellToHarmonicLimit`;
use this name when narrating **finite-patch** limits (`accessibleModeBudgetUpToShell`). -/
theorem accessiblePatch_shellToHarmonicLimit : ShellToHarmonicLimit :=
  shell_to_harmonic_limit_holds

/-!
### Definite photon / horizon refinement limit (EM mode ladder → `4`)

Massless EM modes live on the **same** discrete null-ladder capacity as the rest of HQIV; when
compared to cumulative angular (`S²`) mode counting, the ratio has a **proved** `Tendsto` to a single
real number — the octonionic factor **`4`**.  There is no continuous parameter: this is the
**definite** asymptotic lock (“photon bookkeeping meets horizon angular refinement”).  A separate
curvature–horizon ratio story uses `Hqiv.omega_k_partial` / `Hqiv.omega_k_partial_tends_to_atTop` in
`OctonionicLightCone` (ratio of curvature integrals, not the `4` here).
-/

/-- **Numeric value** of the asymptotic mode-ratio limit (octonion factor). -/
def PhotonHorizonModeLimitValue : ℝ :=
  4

/-- Same `Prop` as `ShellToHarmonicLimit` — packaged under the photon / horizon refinement name. -/
abbrev PhotonHorizonModeLimit : Prop :=
  ShellToHarmonicLimit

theorem photonHorizonModeLimit_holds : PhotonHorizonModeLimit :=
  shell_to_harmonic_limit_holds

theorem PhotonHorizonModeLimit_iff_shellToHarmonicLimit :
    PhotonHorizonModeLimit ↔ ShellToHarmonicLimit :=
  Iff.rfl

/-- The ratio tends to **neighbourhoods of `PhotonHorizonModeLimitValue = 4`**. -/
theorem photonHorizonModeLimit_tendsto :
    Tendsto (fun M : ℕ => accessibleModeBudgetUpToShell M / Hqiv.sphericalHarmonicCumulativeCount M)
      atTop (𝓝 PhotonHorizonModeLimitValue) := by
  simpa [PhotonHorizonModeLimitValue] using accessiblePatch_modeBudget_div_harmonic_tends_four

theorem PhotonHorizonModeLimitValue_eq : PhotonHorizonModeLimitValue = 4 :=
  rfl

/-!
### Cumulative time angle → shell index → mode budget

`θ / phiTemperatureCoeff` is the continuous “(m+1)”-coordinate when `θ = timeAngle (phi_of_shell m) 1`
(`realShellPlusOneFromTimeAngle_timeAngle_phi_shell_unit`).  The floor below packages a **ℕ** shell
index for pairing with `accessibleModeBudgetUpToShell`.
-/

/-- Continuous **(m+1)**-coordinate from cumulative phase: `θ / 2` with `phiTemperatureCoeff = 2`. -/
noncomputable def realShellPlusOneFromTimeAngle (θ : ℝ) : ℝ :=
  θ / phiTemperatureCoeff

theorem realShellPlusOneFromTimeAngle_timeAngle_phi_shell_unit (m : ℕ) :
    realShellPlusOneFromTimeAngle (timeAngle (phi_of_shell m) 1) = m + 1 := by
  unfold realShellPlusOneFromTimeAngle timeAngle
  simp only [mul_one, phi_of_shell_closed_form m, phiTemperatureCoeff_eq_two]
  field_simp

/-- Discrete shell index from cumulative time angle `θ` (nonnegative floor of `(θ/2) - 1`). -/
noncomputable def shellIndexFromTimeAngle (θ : ℝ) : ℕ :=
  ⌊max 0 (θ / phiTemperatureCoeff - 1)⌋₊

theorem shellIndexFromTimeAngle_timeAngle_phi_shell (m : ℕ) (t : ℝ) :
    shellIndexFromTimeAngle (timeAngle (phi_of_shell m) t) =
      ⌊max 0 ((m + 1 : ℝ) * t - 1)⌋₊ := by
  unfold shellIndexFromTimeAngle timeAngle
  have h :
      phi_of_shell m * t / phiTemperatureCoeff - 1 = (m + 1 : ℝ) * t - 1 := by
    rw [phi_of_shell_closed_form m, phiTemperatureCoeff_eq_two]
    ring
  simp [h]

theorem shellIndexFromTimeAngle_timeAngle_phi_shell_unit (m : ℕ) :
    shellIndexFromTimeAngle (timeAngle (phi_of_shell m) 1) = m := by
  rw [shellIndexFromTimeAngle_timeAngle_phi_shell m 1]
  simp only [mul_one]
  have hs : (m + 1 : ℝ) - 1 = (m : ℝ) := by ring
  rw [hs]
  rw [max_eq_right (Nat.cast_nonneg m)]
  exact Nat.floor_natCast (R := ℝ) m

/-- Mode budget reachable when the discrete shell index is inferred from `θ = φ·t` via
`shellIndexFromTimeAngle`. -/
noncomputable def accessibleModeBudgetUpToTimeAngle (θ : ℝ) : ℝ :=
  accessibleModeBudgetUpToShell (shellIndexFromTimeAngle θ)

/-- Same as `accessibleModeBudgetUpToTimeAngle (timeAngle (phi_of_shell m) t)`. -/
noncomputable def accessibleModeBudgetUpToPhiTime (m : ℕ) (t : ℝ) : ℝ :=
  accessibleModeBudgetUpToTimeAngle (timeAngle (phi_of_shell m) t)

theorem accessibleModeBudgetUpToTimeAngle_timeAngle_phi_shell_unit (m : ℕ) :
    accessibleModeBudgetUpToTimeAngle (timeAngle (phi_of_shell m) 1) =
      accessibleModeBudgetUpToShell m := by
  unfold accessibleModeBudgetUpToTimeAngle accessibleModeBudgetUpToShell
  simp [shellIndexFromTimeAngle_timeAngle_phi_shell_unit m]

theorem accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit (m : ℕ) :
    accessibleModeBudgetUpToPhiTime m 1 = accessibleModeBudgetUpToShell m :=
  accessibleModeBudgetUpToTimeAngle_timeAngle_phi_shell_unit m

/-- `available_modes / sphericalHarmonicCumulativeCount → 4` along `atTop` (discrete ↔ harmonic bridge). -/
theorem lightCone_discreteModes_shellToHarmonicLimit : ShellToHarmonicLimit :=
  shell_to_harmonic_limit_holds

/-- Constant scalar on `MaxwellQFTChart` ⇒ zero `coordsGradientComponents`; emergent O–Maxwell RHS matches `general`. -/
theorem lightCone_emergent_coordsField_constPhi_eq_general (J_src : Fin 8 → Fin 4 → ℝ) (r : ℝ)
    (c : MaxwellQFTChart) (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_coordsField J_src (fun _ => r) c a ν =
      emergentMaxwellInhomogeneous_O_general J_src a ν :=
  emergent_coordsField_const_eq_general J_src r c a ν

/-- Minimal continuum axioms together with a proof witness for the shell/harmonic field. -/
structure LightConeFunctionalBridge where
  minimal : HorizonContinuumAxiomsMinimal
  /-- Discharges `minimal.shell_to_harmonic_limit` (typically from `shell_to_harmonic_limit_holds`). -/
  shellProof : minimal.shell_to_harmonic_limit

/-- The ratio scaffold + lattice microcausality witness from `HorizonLimitedRenormLocality`. -/
def LightConeFunctionalBridge.ratioWitnessBridge : LightConeFunctionalBridge where
  minimal := horizonContinuumAxiomsMinimal_ratioWitness
  shellProof := shell_to_harmonic_limit_holds

/-- `ratioWitnessBridge.shellProof` is definitionally the discrete-mode limit (`lightCone_discreteModes_shellToHarmonicLimit`). -/
theorem lightCone_ratioWitnessBridge_shellProof_eq_discreteLimit :
    LightConeFunctionalBridge.ratioWitnessBridge.shellProof = lightCone_discreteModes_shellToHarmonicLimit :=
  rfl

/-- Feed a bridge + proofs of the other minimal slots into `horizon_continuum_closure_minimal_HQIV`. -/
theorem LightConeFunctionalBridge.toContinuumClosureHQIV (b : LightConeFunctionalBridge)
    (hRenorm : b.minimal.renormalization_in_domain)
    (hMicro : b.minimal.microcausality_in_domain)
    (hCluster : b.minimal.cluster_decomposition_in_domain)
    (hScatter : b.minimal.scattering_consistency_in_domain) :
    HorizonContinuumClosureStatementCoreHQIV :=
  horizon_continuum_closure_minimal_HQIV b.minimal b.shellProof hRenorm hMicro hCluster hScatter

/-- Finite Born/kernel layer + continuum closure: same as `horizon_qm_qft_full_package_minimal_HQIV`
    with `A` and `hShell` taken from the bridge. -/
theorem LightConeFunctionalBridge.toFullPackageMinimalHQIV (b : LightConeFunctionalBridge)
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ)
    (hRenorm : b.minimal.renormalization_in_domain)
    (hMicro : b.minimal.microcausality_in_domain)
    (hCluster : b.minimal.cluster_decomposition_in_domain)
    (hScatter : b.minimal.scattering_consistency_in_domain) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
      (normSq ψ
          = redshiftedEnergyN (normSq (collapseTo i ψ))
              (birefringenceRedshiftN betaRad kappaBeta)
              * Real.exp (betaRad / kappaBeta)
            + auxTransferForOutcome i ψ) ∧
      HorizonContinuumClosureStatementCoreHQIV :=
  horizon_qm_qft_full_package_minimal_HQIV ψ hψ κ i betaRad kappaBeta b.minimal b.shellProof hRenorm hMicro
    hCluster hScatter

/-- Full package with `ratioWitnessBridge` (structured renorm/cluster/scattering; lattice microcausality). -/
theorem lightConeMaxwellQFT_fullPackage_ratioWitness
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
      (normSq ψ
          = redshiftedEnergyN (normSq (collapseTo i ψ))
              (birefringenceRedshiftN betaRad kappaBeta)
              * Real.exp (betaRad / kappaBeta)
            + auxTransferForOutcome i ψ) ∧
      HorizonContinuumClosureStatementCoreHQIV :=
  LightConeFunctionalBridge.toFullPackageMinimalHQIV LightConeFunctionalBridge.ratioWitnessBridge ψ hψ κ i
    betaRad kappaBeta renormalization_in_domain_trivial_holds microcausality_in_domain_free_lattice_holds
    cluster_decomposition_zero_kernel_holds scattering_consistency_zero_channel_holds

/-- Same proof as applying `horizon_qm_qft_full_package_minimal_HQIV` to `horizonContinuumAxiomsMinimal_ratioWitness`. -/
theorem lightConeMaxwellQFT_fullPackage_ratioWitness_eq {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ) :
    lightConeMaxwellQFT_fullPackage_ratioWitness ψ hψ κ i betaRad kappaBeta =
      horizon_qm_qft_full_package_minimal_HQIV ψ hψ κ i betaRad kappaBeta horizonContinuumAxiomsMinimal_ratioWitness
        shell_to_harmonic_limit_holds renormalization_in_domain_trivial_holds
        microcausality_in_domain_free_lattice_holds cluster_decomposition_zero_kernel_holds
        scattering_consistency_zero_channel_holds :=
  rfl

/-- Same conclusion as `continuum_many_body_closure_ratioWitness_trivialRest`, reachable from Physics
    via `LightConeFunctionalBridge` (structured renorm/cluster/scattering; lattice microcausality). -/
theorem lightConeMaxwellQFT_continuumClosure_ratioWitness :
    HorizonContinuumClosureStatementCoreHQIV :=
  LightConeFunctionalBridge.toContinuumClosureHQIV LightConeFunctionalBridge.ratioWitnessBridge
    renormalization_in_domain_trivial_holds microcausality_in_domain_free_lattice_holds
    cluster_decomposition_zero_kernel_holds scattering_consistency_zero_channel_holds

/-- The bridge theorem is definitionally the same proof as `continuum_many_body_closure_ratioWitness_trivialRest`. -/
theorem lightConeMaxwellQFT_continuumClosure_ratioWitness_eq :
    lightConeMaxwellQFT_continuumClosure_ratioWitness =
      continuum_many_body_closure_ratioWitness_trivialRest :=
  rfl

end Hqiv.Physics
