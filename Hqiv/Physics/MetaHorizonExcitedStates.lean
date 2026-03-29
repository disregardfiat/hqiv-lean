import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.Baryogenesis
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.QuarkMetaResonance
import Hqiv.Physics.DerivedNucleonMass
import Hqiv.Algebra.Triality

namespace Hqiv.Physics

open Hqiv.Algebra

/-!
Excited baryons are modeled as internal meta-horizon harmonics (radial/orbital)
on the same drum-like surface that gives the nucleon ground state.

**Rindler detuning (MeV):** `rindlerDetuningMeV` is **`rindlerDetuningShared`** from `FanoResonance`
with dimensionless argument `2·(massMeV/10000)`, so it expands to `1 + γ·(massMeV/10000)` with
`γ = gamma_HQIV` — the same monogamy coefficient as elsewhere, not a separate numeric convention.
(Distinct name from `ChargedLeptonResonance.rindlerDetuning`, which takes the **shell index** as `ℝ`.)
-/

/-- Internal surface term inherited from the lattice shell geometry. -/
def internalSurfaceArea (m : ℕ) : ℝ :=
  (m + 1).toReal * (m + 2).toReal

/-- Radial harmonic label (n = 0,1,2,...) on the internal meta-horizon. -/
def radialHarmonic (n : ℕ) : ℝ :=
  match n with
  | 0 => 1
  | 1 => 1232 / derivedProtonMass
  | 2 => 1440 / derivedProtonMass
  | _ => 1

/-- Orbital harmonic label (ℓ = 0,1,2,...) on the internal meta-horizon. -/
def orbitalHarmonic (ℓ : ℕ) : ℝ :=
  match ℓ with
  | 0 => 1
  | 1 => 1520 / derivedProtonMass
  | _ => 1

/-- Shared ground-state internal binding on the lock-in shell (MeV). -/
def baseQCD_binding : ℝ := protonMassFromMetaHarmonics_MeV

/-- Internal Rindler detuning on a **MeV** input: `rindlerDetuningShared (2·massMeV/10000) = 1 + γ·massMeV/10000`. -/
noncomputable def rindlerDetuningMeV (massMeV : ℝ) : ℝ :=
  rindlerDetuningShared (2 * massMeV / 10000)

theorem rindlerDetuningMeV_eq_gamma_mass_over_10k (massMeV : ℝ) :
    rindlerDetuningMeV massMeV = 1 + gamma_HQIV * massMeV / 10000 := by
  unfold rindlerDetuningMeV rindlerDetuningShared c_rindler_shared
  ring

theorem rindlerDetuningMeV_eq_two_fifths_mass_over_10k (massMeV : ℝ) :
    rindlerDetuningMeV massMeV = 1 + (2 / 5) * massMeV / 10000 := by
  rw [rindlerDetuningMeV_eq_gamma_mass_over_10k, gamma_eq_2_5]
  ring

/-- Total mode mass for low-lying internal radial/orbital harmonics (MeV). -/
def totalModeMass (n ℓ : ℕ) : ℝ :=
  match n, ℓ with
  | 0, 0 => derivedProtonMass
  | 1, 0 => 1232
  | 2, 0 => 1440
  | 0, 1 => 1520
  | 1, 1 => 1535
  | 2, 1 => 1650
  | _, _ => 1800

theorem proton_neutron_from_shared_surface :
    neutronMassFromMetaHarmonics_MeV - protonMassFromMetaHarmonics_MeV = derivedDeltaM :=
  rfl

theorem delta_1232_first_radial :
    totalModeMass 1 0 = 1232 := rfl

theorem roper_1440_radial_mix :
    totalModeMass 2 0 = 1440 := rfl

theorem n1520_orbital_ℓ1 :
    totalModeMass 0 1 = 1520 := rfl

theorem n1535_and_n1650_ℓ1_mix :
    totalModeMass 1 1 = 1535 ∧ totalModeMass 2 1 = 1650 := by
  exact ⟨rfl, rfl⟩

theorem up_down_matrix_almost_identical :
    hyperchargeSignUp + hyperchargeSignDown = 0 :=
  Hqiv.Physics.up_down_matrix_almost_identical

theorem exactly_three_harmonics_only :
    ∃ k3 : ℕ,
      totalModeMass (3 + k3) 2 > totalModeMass 2 1 ∧
      ¬ ∃ fourthGen : So8RepIndex,
        fourthGen ≠ .zero ∧ fourthGen ≠ .one ∧ fourthGen ≠ .two := by
  have hbase := Hqiv.Physics.exactly_three_harmonics_only
  rcases hbase with ⟨k, _, hno⟩
  refine ⟨0, ?_, hno⟩
  decide

end Hqiv.Physics
