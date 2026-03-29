import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.Baryogenesis
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Hqiv.Physics

/-!
This module must remain light-weight: it defines only the derived witness
values needed for JSON export and avoids importing `Triality`, which pulls
in heavier algebra (and `So8CoordMatrix`).
-/

def trialityOrder : ℕ := 3

-- Generation index for SM export: `So8RepIndex` (`Hqiv.Algebra`, defeq to `Fin 3`).

/-!
Pure-derivation gauge/lepton sector:
all scales are generated from lattice surfaces, lock-in shell reference, triality
structure, and resonance geometry (no external mass inputs in this module).

**Neutrino anchor (same horizon language as quark top / `T_lockin`):**
`T_lockin` multiplies the outer horizon area at `referenceM + 1` to form the vev;
`M_Z` and then `m_nu_e_derived` follow, with **outer-horizon suppression** from
`outerHorizonSurface (referenceM + 2)` (`outerHorizonNeutrinoSuppression`). See
`m_nu_e_derived_eq_T_lockin_outer_surfaces`.
-/

/-- Outer-horizon surface from lattice stars-and-bars leading term. -/
noncomputable def outerHorizonSurface (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) * (m + 2 : ℝ))

/-- Inner meta-horizon surface uses the same shell geometry. -/
noncomputable def innerMetaHorizonSurface (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) * (m + 2 : ℝ))

/-- Resonance step is the geometric surface ratio between shells. -/
noncomputable def resonanceStepK (m_from m_to : ℕ) : ℝ :=
  outerHorizonSurface m_to / outerHorizonSurface m_from

/-- Electroweak resonance shell chosen one radial step beyond lock-in. -/
def electroweakShell : ℕ := referenceM + 1

/-- Monogamy coefficient derived from the HQIV lattice split α+γ=1. -/
def gammaDerived : ℝ := 1 - alpha

/-- Geometric vev from horizon temperature/area coupling at the EW shell. -/
noncomputable def vacuumExpectationValue : ℝ :=
  T_lockin * outerHorizonSurface electroweakShell * (1 + gammaDerived)

/-- Minimal gauge closure couplings from triality count and monogamy split. -/
noncomputable def su2CouplingDerived : ℝ := 1 / (trialityOrder : ℝ)
noncomputable def u1CouplingDerived : ℝ := gammaDerived / (trialityOrder : ℝ)

/-- Generic boson mass generated from vev and effective coupling. -/
noncomputable def gaugeBosonMassFromVev (gEff : ℝ) : ℝ :=
  gEff * vacuumExpectationValue

noncomputable def m_H_derived : ℝ := 2 * vacuumExpectationValue
noncomputable def M_W_derived : ℝ := gaugeBosonMassFromVev su2CouplingDerived
noncomputable def M_Z_derived : ℝ := gaugeBosonMassFromVev (su2CouplingDerived + u1CouplingDerived)

/-- Small ν mass factor: `γ` over the next outer-horizon surface (`referenceM + 2`). -/
noncomputable def outerHorizonNeutrinoSuppression : ℝ :=
  gammaDerived / outerHorizonSurface (referenceM + 2)

noncomputable def m_nu_tree : ℝ := 0
noncomputable def m_nu_e_derived : ℝ := outerHorizonNeutrinoSuppression * M_Z_derived
noncomputable def m_nu_mu_derived : ℝ := outerHorizonNeutrinoSuppression * m_nu_e_derived
noncomputable def m_nu_tau_derived : ℝ := outerHorizonNeutrinoSuppression * m_nu_mu_derived

theorem higgs_mass_from_outer_resonance :
    m_H_derived = 2 * vacuumExpectationValue := rfl

theorem w_and_z_masses_from_gauge_closure :
    M_W_derived = gaugeBosonMassFromVev su2CouplingDerived ∧
    M_Z_derived = gaugeBosonMassFromVev (su2CouplingDerived + u1CouplingDerived) := by
  exact ⟨rfl, rfl⟩

theorem neutrino_masses_from_outer_horizon :
    m_nu_tree = 0 ∧
    m_nu_e_derived = outerHorizonNeutrinoSuppression * M_Z_derived ∧
    m_nu_mu_derived = outerHorizonNeutrinoSuppression * m_nu_e_derived ∧
    m_nu_tau_derived = outerHorizonNeutrinoSuppression * m_nu_mu_derived := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem electroweakShell_eq_succ_reference : electroweakShell = referenceM + 1 := rfl

/-- Lock-in temperature is the ladder value at `referenceM` (`m_lockin = referenceM`). -/
theorem T_lockin_eq_T_referenceM : T_lockin = T referenceM := by
  rw [T_lockin_eq_ladder, m_lockin_eq_referenceM]

theorem vacuumExpectationValue_eq_T_lockin_outer_surface :
    vacuumExpectationValue =
      T_lockin * outerHorizonSurface (referenceM + 1) * (1 + gammaDerived) := by
  simp [vacuumExpectationValue, electroweakShell]

/-- Two adjacent resonance steps telescope to a surface ratio two shells out. -/
theorem resonance_two_step_outer_surface_ratio (m : ℕ) :
    resonanceStepK m (m + 1) * resonanceStepK (m + 1) (m + 2) =
      outerHorizonSurface (m + 2) / outerHorizonSurface m := by
  simp [resonanceStepK, outerHorizonSurface]
  field_simp

/--
Electron neutrino mass witness: explicit product of `T_lockin`, outer areas at
`referenceM + 1` and `referenceM + 2`, and the derived gauge couplings — no separate
mass-table input.
-/
theorem m_nu_e_derived_eq_T_lockin_outer_surfaces :
    m_nu_e_derived =
      (gammaDerived / outerHorizonSurface (referenceM + 2)) *
        (su2CouplingDerived + u1CouplingDerived) *
          T_lockin * outerHorizonSurface (referenceM + 1) * (1 + gammaDerived) := by
  simp [m_nu_e_derived, outerHorizonNeutrinoSuppression, M_Z_derived, gaugeBosonMassFromVev,
    vacuumExpectationValue, electroweakShell, mul_assoc, mul_left_comm, mul_comm]
end Hqiv.Physics
