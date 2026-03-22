import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

import Hqiv.Physics.HQIVNuclei
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.Physics.BoundStates
import Hqiv.Physics.SpinStatistics

/-!
# HQIV atoms: AtomicSurface, Fresnel electron shells, excited promotions

Packages the nuclear `CasimirSurface` as the atomic nucleus and models electron
shells as **horizon indices** `m` whose Fresnel radii are `R_m` (same convention
as `NuclearAndAtomicSpectra` / `HQIVNuclei`). Excited states bump one shell
index, increasing the Casimir zero-point budget at that layer; lifetimes link to
`resonance_half_life` via the existing `spin_statistics_determines_half_life`
bridge in `HQIVNuclei`.

No new physical axioms: only definitions and lemmas from the closed imports.
-/

namespace Hqiv.Physics

open scoped BigOperators

/-!
## Canonical Casimir surface (constructive witness at any shell)
-/

/-- Constructive proton-tagged Casimir data at shell `m` (for bookkeeping and
energy identities that hold for *any* `CasimirSurface m`). -/
noncomputable def mkCasimirSurface (m : ℕ) : CasimirSurface m :=
  { horizon := { isospin := IsospinLabel.proton }
  , harmonics :=
      { cumulativeCount := Hqiv.sphericalHarmonicCumulativeCount m
      , hcum := rfl }
  , vacuumModes :=
      { count := Hqiv.available_modes m
      , hcount := rfl }
  , metaInfo :=
      { isospinThird := 1
      , spinHalf := true
      , parityEven := true } }

/-!
## Atomic surface: nucleus + electron shell indices
-/

/-- Atom: nucleus as a closed Casimir surface at `nucleus_m`, and one Fresnel
shell index per electron (`Fin electrons → ℕ`; higher `m` = outer / promoted layers). -/
structure AtomicSurface (Z : ℕ) (electrons : ℕ) where
  nucleus_m : ℕ
  nucleus : CasimirSurface nucleus_m
  /-- Effective horizon index for each electron shell (Fresnel layer). -/
  electron_shell_m : Fin electrons → ℕ
  /-- Bookkeeping for total promotions away from the reference configuration. -/
  excitedStateLevel : ℕ := 0

/-- Atom with a fixed nuclear shell index `m` (shared across a molecular tree for
well-typed `valleyPotentialEM` bonds). -/
structure AtomicSurfaceAt (m : ℕ) where
  Z : ℕ
  e : ℕ
  surf : AtomicSurface Z e
  h : surf.nucleus_m = m

/-- Vacuum-mode density proxy for the first indexed shell (`i = 0`); requires at least one electron. -/
noncomputable def atomicCausticDensity {Z e : ℕ} (a : AtomicSurface Z e) (h : 0 < e) : ℝ :=
  (availableModesNat (a.electron_shell_m ⟨0, h⟩) : ℝ) / R_m (a.electron_shell_m ⟨0, h⟩)

/-- Casimir zero-point budget at shell `m` (any surface; equals `CasimirEnergySurface`). -/
noncomputable def electronShellCasimirEnergy (m : ℕ) : ℝ :=
  Hqiv.available_modes m * (omegaCasimir m / 2)

theorem electronShellCasimirEnergy_eq_casimir {m : ℕ} (S : CasimirSurface m) :
    electronShellCasimirEnergy m = CasimirEnergySurface S := by
  unfold electronShellCasimirEnergy CasimirEnergySurface omegaCasimir
  exact (casimir_energy_full_mode_sum S).symm

/-!
### Geometry: nuclear boundary and electron Fresnel shells share `R_m`
-/

/-- Electron/nucleon Fresnel radius is the meta-horizon radius `R_m`. -/
theorem atomic_shell_from_nuclear_boundary {m : ℕ} (S : CasimirSurface m) :
    (fresnelCaustic S).radius = R_m m ∧
      (sphericalFresnelEnvelope S.harmonics S.horizon).radius = R_m m :=
  ⟨fresnel_meta_horizon_driven S, sphericalFresnelEnvelope_radius S.harmonics S.horizon⟩

/-- Spherical harmonic envelope and vacuum-mode Fresnel share the same radius assignment;
curvatures agree with their respective mode densities over `R_m`. -/
theorem atomic_geometry_from_nuclear (m : ℕ) (S : CasimirSurface m) :
    (sphericalFresnelEnvelope S.harmonics S.horizon).radius =
      (fresnelCaustic S).radius ∧
        (sphericalFresnelEnvelope S.harmonics S.horizon).curvature =
          S.harmonics.cumulativeCount / R_m m ∧
        (fresnelCaustic S).curvature = S.vacuumModes.count / R_m m :=
  ⟨by rw [sphericalFresnelEnvelope_radius, fresnel_meta_horizon_driven],
   rfl,
   causticCurvature_eq_vacuumModeDensity S⟩

/-!
## Excited-state promotion (one shell index steps by 1)
-/

/-- Promote shell `i` by `m ↦ m+1`; increments `excitedStateLevel`. -/
def promoteElectron {Z e : ℕ} (a : AtomicSurface Z e) (i : Fin e) : AtomicSurface Z e :=
  { a with
    electron_shell_m := fun j => if h : j = i then a.electron_shell_m i + 1 else a.electron_shell_m j
    excitedStateLevel := a.excitedStateLevel + 1 }

/-- Energy step for the promoted shell: difference of full Casimir sums at `m+1` vs `m`. -/
noncomputable def casimirPromotionDelta (m : ℕ) : ℝ :=
  electronShellCasimirEnergy (m + 1) - electronShellCasimirEnergy m

/-- Casimir energy gap between consecutive shells equals `casimirPromotionDelta`. -/
theorem casimir_promotion_delta_sub {m : ℕ} (S : CasimirSurface m) (S' : CasimirSurface (m + 1)) :
    CasimirEnergySurface S' - CasimirEnergySurface S = casimirPromotionDelta m := by
  rw [electronShellCasimirEnergy_eq_casimir S, electronShellCasimirEnergy_eq_casimir S']
  unfold casimirPromotionDelta electronShellCasimirEnergy
  ring

/-- Promotion ΔE equals the shell-step Casimir gap; half-life uses `decayWidth_per_s ΔE = ΔE / ħ`. -/
theorem excited_state_energy_budget {m : ℕ} (S : CasimirSurface m) (S' : CasimirSurface (m + 1))
    (hΔ : 0 < casimirPromotionDelta m) :
    CasimirEnergySurface S' - CasimirEnergySurface S = casimirPromotionDelta m ∧
      half_life_from_width (decayWidth_per_s (casimirPromotionDelta m)) =
        resonance_half_life (casimirPromotionDelta m) :=
  ⟨casimir_promotion_delta_sub S S', spin_statistics_determines_half_life hΔ⟩

theorem excited_state_half_life_link {ΔE : ℝ} (hΔ : 0 < ΔE) :
    half_life_from_width (decayWidth_per_s ΔE) = resonance_half_life ΔE :=
  spin_statistics_determines_half_life hΔ

/-- Joint atom energy bookkeeping: nucleus shell uses `expectedGroundEnergyAtShell`. -/
noncomputable def atomicGroundEnergy (μ c : ℝ) {Z e : ℕ} (a : AtomicSurface Z e) : ℝ :=
  expectedGroundEnergyAtShell a.nucleus_m Z μ c

theorem atomic_ground_energy_def (μ c : ℝ) {Z e : ℕ} (a : AtomicSurface Z e) :
    atomicGroundEnergy μ c a = expectedGroundEnergyAtShell a.nucleus_m Z μ c :=
  rfl

/-!
## Dihedral / torque placeholder (shared with `HQIVMolecules`)
-/

/-- Abstract dihedral angle between two torque-tree nodes (pole alignment proxy). -/
noncomputable def dihedralAngleBetweenValleys (_ _ : Unit) : ℝ := 0

/-- EM + valley torque budget with explicit dihedral penalty `κ * (1 - cos θ)`;
minimum at `θ = 0` for `0 < κ`. -/
noncomputable def valleyPotentialEMWithDihedral (κ θ : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) : ℝ :=
  valleyPotentialEM m n₁ n₂ Z_eff r + κ * (1 - Real.cos θ)

theorem valleyPotentialEMWithDihedral_eq_base (κ θ : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) :
    valleyPotentialEMWithDihedral κ θ m n₁ n₂ Z_eff r =
      valleyPotentialEM m n₁ n₂ Z_eff r + κ * (1 - Real.cos θ) :=
  rfl

theorem pole_cancellation_saturates_valleys (κ θ : ℝ) (hθ : θ = 0) :
    κ * (1 - Real.cos θ) = 0 := by
  rw [hθ, Real.cos_zero]
  ring

theorem dihedral_penalty_nonneg (κ θ : ℝ) (hκ : 0 ≤ κ) : 0 ≤ κ * (1 - Real.cos θ) := by
  have hcos : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have : 0 ≤ 1 - Real.cos θ := sub_nonneg.mpr hcos
  exact mul_nonneg hκ this

theorem allowed_binding_angles_minimize_budget (κ : ℝ) (_hκ : κ ≠ 0) :
    deriv (fun θ : ℝ => κ * (1 - Real.cos θ)) 0 = 0 := by
  have h1 : HasDerivAt (fun θ : ℝ => (1 : ℝ) - Real.cos θ) (Real.sin 0) 0 :=
    HasDerivAt.const_sub (1 : ℝ) (Real.hasDerivAt_cos 0)
  simpa [Real.sin_zero, mul_zero] using (HasDerivAt.const_mul κ h1).deriv

/-!
### pH / ligand / solvent: explicit EM rescaling (no new axioms)
-/

/-- Solvent / ligand / pH encoded as a nonnegative multiplier on the EM piece of
`valleyPotentialEM` (same structural move as rescaling `α_EM` in the Coulomb term). -/
noncomputable def valleyPotentialEM_rescaled (cEM : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) : ℝ :=
  valleyPotential n₁ n₂ + cEM * (Hqiv.alpha_EM_at_MZ * Z_eff / r)

theorem valleyPotentialEM_rescaled_eq (cEM : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) (hc : cEM = 1) :
    valleyPotentialEM_rescaled cEM m n₁ n₂ Z_eff r = valleyPotentialEM m n₁ n₂ Z_eff r := by
  unfold valleyPotentialEM_rescaled valleyPotentialEM
  rw [hc, one_mul]

/-- **Water / high-ε dielectric:** divide the Coulomb distance scale by `ε_r > 0`
(effective `r ↦ ε_r · r` in the EM term, same as rescaling `α_EM Z / r`). -/
noncomputable def waterDielectricValley (ε_r : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) : ℝ :=
  valleyPotential n₁ n₂ + Hqiv.alpha_EM_at_MZ * Z_eff / (ε_r * r)

theorem water_dielectric_rescaling (ε_r : ℝ) (_hε : ε_r ≠ 0) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) :
    waterDielectricValley ε_r m n₁ n₂ Z_eff r =
      valleyPotential n₁ n₂ + Hqiv.alpha_EM_at_MZ * Z_eff / (ε_r * r) :=
  rfl

theorem water_dielectric_rescaling_eq_EM (ε_r : ℝ) (_hε : ε_r ≠ 0) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) :
    waterDielectricValley ε_r m n₁ n₂ Z_eff r = valleyPotentialEM m n₁ n₂ Z_eff (ε_r * r) := by
  unfold waterDielectricValley valleyPotentialEM
  ring

/-- **pH / protonation:** shift effective charge `Z_eff ↦ Z_eff + δZ` (acid–base bookkeeping). -/
theorem pH_charge_flip_effect (δZ Z_eff r : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m) :
    valleyPotentialEM m n₁ n₂ (Z_eff + δZ) r =
      valleyPotentialEM m n₁ n₂ Z_eff r + Hqiv.alpha_EM_at_MZ * δZ / r := by
  unfold valleyPotentialEM valleyPotential
  ring

end Hqiv.Physics
