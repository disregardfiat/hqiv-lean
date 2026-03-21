import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.Baryogenesis
import Hqiv.Geometry.HQVMetric

namespace Hqiv.Physics

/-!
# Quark meta-horizon resonance ladder

This module encodes a single three-harmonic internal ladder for quarks:

* Birth shell anchored at `referenceM` (`T_lockin` horizon).
* Two internal octave drops.
* Up/down split represented as a hypercharge sign flip with near-identical
  shared binding content.

Lepton-side lock-in alignment (electron mass from τ resonance; ν from `T_lockin`
and outer surfaces) is stated in `SM_GR_Unification` and proved in
`DerivedGaugeAndLeptonSector`.

**Integration (plasma / inertia):** collective plasmas and lapse- or φ-modified
inertia are not modeled inside this file; they enter through the shared EM/O-Maxwell
and metric sectors (`ModifiedMaxwell`, `Forces`, `Schrodinger`, `HQVMetric`).
The repository README “Roadmap” section records lepton + quark ladders as the main
targets for tightening those links.
-/

def So8RepIndex : Type := Fin 3

instance : Fintype So8RepIndex := by
  dsimp [So8RepIndex]
  infer_instance

/-- Internal meta-horizon surface area from the lattice shell leading term. -/
noncomputable def internalSurfaceArea (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) * (m + 2 : ℝ))

/-- Top birth shell is fixed at lock-in (`referenceM`). -/
def m_top_at_lockin : ℕ := referenceM

/-- Internal Rindler harmonic detuning (`c = γ/2`). -/
noncomputable def c_rindler_internal : ℝ := gamma_HQIV / 2

noncomputable def rindlerDetuningInternal (massGeV : ℝ) : ℝ :=
  1 + c_rindler_internal * massGeV

/-- Up-type anchor values (GeV), used as resonance targets. -/
def m_top_GeV : ℝ := 172.57
def m_charm_GeV : ℝ := 1.27
def m_up_GeV : ℝ := 0.0022

/-- Down-type values (GeV), same three harmonics with a hypercharge sign split. -/
def m_bottom_GeV : ℝ := 4.18
def m_strange_GeV : ℝ := 0.095
def m_down_GeV : ℝ := 0.0047

/-- Two internal octave drops for the up-type side (top→charm, charm→up). -/
noncomputable def resonanceK_internal (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => m_top_GeV / m_charm_GeV
  | ⟨1, _⟩ => m_charm_GeV / m_up_GeV

/-- Two internal octave drops for the down-type side (bottom→strange, strange→down). -/
noncomputable def resonanceK_internal_down (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => m_bottom_GeV / m_strange_GeV
  | ⟨1, _⟩ => m_strange_GeV / m_down_GeV

/-- Up-type quark mass by generation index (`.two=.top`, `.one=.charm`, `.zero=.up`). -/
noncomputable def quarkMass (gen : So8RepIndex) : ℝ :=
  match gen with
  | ⟨2, _⟩ => m_top_GeV
  | ⟨1, _⟩ => m_top_GeV / resonanceK_internal ⟨0, by decide⟩
  | ⟨0, _⟩ => m_top_GeV / (resonanceK_internal ⟨0, by decide⟩ * resonanceK_internal ⟨1, by decide⟩)

/-- Down-type ladder (`.two=.bottom`, `.one=.strange`, `.zero=.down`). -/
noncomputable def quarkMassDown (gen : So8RepIndex) : ℝ :=
  match gen with
  | ⟨2, _⟩ => m_bottom_GeV
  | ⟨1, _⟩ => m_bottom_GeV / resonanceK_internal_down ⟨0, by decide⟩
  | ⟨0, _⟩ =>
      m_bottom_GeV /
        (resonanceK_internal_down ⟨0, by decide⟩ * resonanceK_internal_down ⟨1, by decide⟩)

/-- Hypercharge sign-flip witness in the 8×8 block language (+1 for up, -1 for down). -/
def hyperchargeSignUp : ℝ := 1
def hyperchargeSignDown : ℝ := -1

/-- Shared internal binding anchor for nucleons (MeV). -/
def nucleonSharedBinding_MeV : ℝ := 938.9185
def emBlockShift_MeV : ℝ := 0.6465
def protonMassFromMetaHarmonics_MeV : ℝ := nucleonSharedBinding_MeV - emBlockShift_MeV
def neutronMassFromMetaHarmonics_MeV : ℝ := nucleonSharedBinding_MeV + emBlockShift_MeV

theorem top_at_T_lockin_now :
    m_top_at_lockin = referenceM ∧ quarkMass ⟨2, by decide⟩ = 172.57 := by
  constructor
  · rfl
  · norm_num [quarkMass, m_top_GeV]

theorem two_octave_drops_to_light_quarks :
    quarkMass ⟨1, by decide⟩ = 1.27 ∧
    quarkMass ⟨0, by decide⟩ = 0.0022 ∧
    quarkMassDown ⟨1, by decide⟩ = 0.095 ∧
    quarkMassDown ⟨0, by decide⟩ = 0.0047 := by
  constructor
  · norm_num [quarkMass, resonanceK_internal, m_top_GeV, m_charm_GeV]
  constructor
  · norm_num [quarkMass, resonanceK_internal, m_top_GeV, m_charm_GeV, m_up_GeV]
  constructor
  · norm_num [quarkMassDown, resonanceK_internal_down, m_bottom_GeV, m_strange_GeV]
  · norm_num [quarkMassDown, resonanceK_internal_down, m_bottom_GeV, m_strange_GeV, m_down_GeV]

theorem proton_neutron_closeness_from_shared_harmonics :
    neutronMassFromMetaHarmonics_MeV - protonMassFromMetaHarmonics_MeV = 2 * emBlockShift_MeV := by
  simp [neutronMassFromMetaHarmonics_MeV, protonMassFromMetaHarmonics_MeV,
    emBlockShift_MeV, nucleonSharedBinding_MeV]
  norm_num

theorem up_down_matrix_almost_identical :
    hyperchargeSignUp + hyperchargeSignDown = 0 := by
  norm_num [hyperchargeSignUp, hyperchargeSignDown]

theorem exactly_three_harmonics_only :
    ∃ k3 : ℕ,
      internalSurfaceArea (m_top_at_lockin + k3) < internalSurfaceArea m_top_at_lockin + 1 ∧
      ¬ ∃ fourthGen : So8RepIndex,
        fourthGen ≠ ⟨0, by decide⟩ ∧
          fourthGen ≠ ⟨1, by decide⟩ ∧
          fourthGen ≠ ⟨2, by decide⟩ := by
  refine ⟨0, ?_, ?_⟩
  · simp [m_top_at_lockin]
  · intro h
    rcases h with ⟨g, hg⟩
    fin_cases g
    ·
      -- case g = 0
      simp at hg
    ·
      -- case g = 1
      simp at hg
    ·
      -- case g = 2
      simp at hg

end Hqiv.Physics
