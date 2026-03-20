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

-- `So8RepIndex` comes from `QuarkMetaResonance` (the shared lightweight index type).

/-!
Pure-derivation gauge/lepton sector:
all scales are generated from lattice surfaces, lock-in shell reference, triality
structure, and resonance geometry (no external mass inputs in this module).
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

/-- Sterile overlap suppression on the same outer-horizon shell family. -/
noncomputable def sterileNeutrinoSuppression : ℝ :=
  gammaDerived / outerHorizonSurface (referenceM + 2)

noncomputable def m_nu_tree : ℝ := 0
noncomputable def m_nu_e_derived : ℝ := sterileNeutrinoSuppression * M_Z_derived
noncomputable def m_nu_mu_derived : ℝ := sterileNeutrinoSuppression * m_nu_e_derived
noncomputable def m_nu_tau_derived : ℝ := sterileNeutrinoSuppression * m_nu_mu_derived

theorem higgs_mass_from_outer_resonance :
    m_H_derived = 2 * vacuumExpectationValue := rfl

theorem w_and_z_masses_from_gauge_closure :
    M_W_derived = gaugeBosonMassFromVev su2CouplingDerived ∧
    M_Z_derived = gaugeBosonMassFromVev (su2CouplingDerived + u1CouplingDerived) := by
  exact ⟨rfl, rfl⟩

theorem neutrino_masses_from_sterile_overlap :
    m_nu_tree = 0 ∧
    m_nu_e_derived = sterileNeutrinoSuppression * M_Z_derived ∧
    m_nu_mu_derived = sterileNeutrinoSuppression * m_nu_e_derived ∧
    m_nu_tau_derived = sterileNeutrinoSuppression * m_nu_mu_derived := by
  exact ⟨rfl, rfl, rfl, rfl⟩
end Hqiv.Physics
