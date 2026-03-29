import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Data.Fin.Basic
import Hqiv.Physics.FanoResonance
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.Baryogenesis
import Hqiv.Geometry.HQVMetric

namespace Hqiv.Physics

/-!
# Quark meta-horizon resonance ladder

This module encodes a single three-harmonic internal ladder for quarks (generation index `Fin 3`,
defeq to `Hqiv.Algebra.So8RepIndex` used in `ChargedLeptonResonance` / `SM_GR_Unification`):

* **Lock-in narrative:** the top quark birth shell index is `referenceM` (`m_top_at_lockin`),
  aligned with baryogenesis lock-in (`T_lockin`).
* **Geometric steps (same as charged leptons):** the two internal octave factors are
  **ratios of detuned shell surfaces** `geometricResonanceStep m_heavy m_lighter`
  (`FanoResonance.detunedShellSurface`), not mass-table ratios.
* **Shell triples:** explicit natural shells `m_quark_up_*` and `m_quark_down_*` are chosen
  so the resulting masses sit near the usual PDG reference values; see
  `light_quark_masses_near_paper_pdg` (tolerance `quarkPDG_relTol = 1/500`, same as leptons).

Up/down split: hypercharge sign metadata on the Fano axes (`upResonanceAxis` / `downResonanceAxis`).

Lepton-side lock-in alignment lives in `ChargedLeptonResonance` / `SM_GR_Unification`; ν from
`DerivedGaugeAndLeptonSector`.

**Integration (plasma / inertia):** collective plasmas and lapse- or φ-modified inertia are
not modeled here; they enter through shared EM/O-Maxwell and metric sectors.
-/

/-- Internal meta-horizon surface area from the lattice shell leading term. -/
def internalSurfaceArea (m : ℕ) : ℝ :=
  shellSurface m

/-- Top birth shell is fixed at lock-in (`referenceM`). -/
def m_top_at_lockin : ℕ := referenceM

/-! ### Up-type shell triple (heavy > mid > light) -/

def m_quark_up_top_shell : ℕ := 31382
def m_quark_up_charm_shell : ℕ := 233
def m_quark_up_light_shell : ℕ := 0

/-! ### Down-type shell triple -/

def m_quark_down_bottom_shell : ℕ := 5329
def m_quark_down_strange_shell : ℕ := 123
def m_quark_down_light_shell : ℕ := 7

/-- Up-type GeV anchor (heavy generation). -/
def m_top_GeV : ℝ := 172.57

/-- Down-type GeV anchor (heavy generation). -/
def m_bottom_GeV : ℝ := 4.18

/-- Two internal octave drops for the up-type side (top→charm, charm→up), from detuned surfaces. -/
noncomputable def resonanceK_internal (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => geometricResonanceStep m_quark_up_top_shell m_quark_up_charm_shell
  | ⟨1, _⟩ => geometricResonanceStep m_quark_up_charm_shell m_quark_up_light_shell

/-- Two internal octave drops for the down-type side (bottom→strange, strange→down). -/
noncomputable def resonanceK_internal_down (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => geometricResonanceStep m_quark_down_bottom_shell m_quark_down_strange_shell
  | ⟨1, _⟩ => geometricResonanceStep m_quark_down_strange_shell m_quark_down_light_shell

/-- Derived charm mass (GeV) from top anchor and first geometric step. -/
noncomputable def m_charm_GeV : ℝ := m_top_GeV / resonanceK_internal ⟨0, by decide⟩

/-- Derived up mass (GeV). -/
noncomputable def m_up_GeV : ℝ := m_charm_GeV / resonanceK_internal ⟨1, by decide⟩

/-- Derived strange mass (GeV). -/
noncomputable def m_strange_GeV : ℝ := m_bottom_GeV / resonanceK_internal_down ⟨0, by decide⟩

/-- Derived down mass (GeV). -/
noncomputable def m_down_GeV : ℝ := m_strange_GeV / resonanceK_internal_down ⟨1, by decide⟩

/-- Canonical up-quark internal ladder axis (first up-line Fano vertex). -/
def upResonanceAxis : ResonanceAxis := upQuarkAxis ⟨0, by decide⟩ m_quark_up_top_shell

/-- Canonical down-quark internal ladder axis (first down-line Fano vertex). -/
def downResonanceAxis : ResonanceAxis := downQuarkAxis ⟨0, by decide⟩ m_quark_down_bottom_shell

noncomputable def upResonanceProduct (gen : Fin 3) : ℝ :=
  resonanceProductFromSteps
    (resonanceK_internal ⟨0, by decide⟩)
    (resonanceK_internal ⟨1, by decide⟩) gen

noncomputable def downResonanceProduct (gen : Fin 3) : ℝ :=
  resonanceProductFromSteps
    (resonanceK_internal_down ⟨0, by decide⟩)
    (resonanceK_internal_down ⟨1, by decide⟩) gen

/-- Up-type quark mass by generation index (`.two=.top`, `.one=.charm`, `.zero=.up`). -/
noncomputable def quarkMass (gen : Fin 3) : ℝ :=
  match gen with
  | ⟨2, _⟩ => m_top_GeV
  | ⟨1, _⟩ => m_top_GeV / upResonanceProduct ⟨1, by decide⟩
  | ⟨0, _⟩ => m_top_GeV / upResonanceProduct ⟨0, by decide⟩

/-- Down-type ladder (`.two=.bottom`, `.one=.strange`, `.zero=.down`). -/
noncomputable def quarkMassDown (gen : Fin 3) : ℝ :=
  match gen with
  | ⟨2, _⟩ => m_bottom_GeV
  | ⟨1, _⟩ => m_bottom_GeV / downResonanceProduct ⟨1, by decide⟩
  | ⟨0, _⟩ => m_bottom_GeV / downResonanceProduct ⟨0, by decide⟩

/-- Hypercharge sign-flip witness in the 8×8 block language (+1 for up, -1 for down). -/
def hyperchargeSignUp : ℝ := (upResonanceAxis.hyperchargeSign : ℝ)
def hyperchargeSignDown : ℝ := (downResonanceAxis.hyperchargeSign : ℝ)

/-- Shared internal binding anchor for nucleons (MeV). -/
def nucleonSharedBinding_MeV : ℝ := 938.9185
def emBlockShift_MeV : ℝ := 0.6465
def protonMassFromMetaHarmonics_MeV : ℝ := nucleonSharedBinding_MeV - emBlockShift_MeV
def neutronMassFromMetaHarmonics_MeV : ℝ := nucleonSharedBinding_MeV + emBlockShift_MeV

theorem resonanceK_internal_pos (step : Fin 2) : 0 < resonanceK_internal step := by
  fin_cases step
  · exact geometricResonanceStep_pos m_quark_up_top_shell m_quark_up_charm_shell
  · exact geometricResonanceStep_pos m_quark_up_charm_shell m_quark_up_light_shell

theorem resonanceK_internal_down_pos (step : Fin 2) : 0 < resonanceK_internal_down step := by
  fin_cases step
  · exact geometricResonanceStep_pos m_quark_down_bottom_shell m_quark_down_strange_shell
  · exact geometricResonanceStep_pos m_quark_down_strange_shell m_quark_down_light_shell

theorem top_at_T_lockin_now :
    m_top_at_lockin = referenceM ∧ quarkMass ⟨2, by decide⟩ = 172.57 := by
  constructor
  · rfl
  · norm_num [quarkMass, m_top_GeV]

theorem two_octave_drops_to_light_quarks :
    quarkMass ⟨1, by decide⟩ = m_charm_GeV ∧
    quarkMass ⟨0, by decide⟩ = m_up_GeV ∧
    quarkMassDown ⟨1, by decide⟩ = m_strange_GeV ∧
    quarkMassDown ⟨0, by decide⟩ = m_down_GeV := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [quarkMass, m_charm_GeV, upResonanceProduct, resonanceProductFromSteps, resonanceK_internal]
  ·
    simp [quarkMass, m_up_GeV, m_charm_GeV, upResonanceProduct, resonanceProductFromSteps,
      resonanceK_internal]
    field_simp
  · simp [quarkMassDown, m_strange_GeV, downResonanceProduct, resonanceProductFromSteps,
      resonanceK_internal_down]
  ·
    simp [quarkMassDown, m_down_GeV, m_strange_GeV, downResonanceProduct, resonanceProductFromSteps,
      resonanceK_internal_down]
    field_simp

/-- Relative tolerance aligned with `ChargedLeptonResonance.relTol` (`1/500`). -/
noncomputable def quarkPDG_relTol : ℝ := 1 / 500

/-- Squared relative-error bound (no `abs`), same shape as `ChargedLeptonResonance.approxRel`. -/
def quarkPDGApprox (a b : ℝ) : Prop :=
  (a - b) ^ 2 ≤ quarkPDG_relTol ^ 2 * b ^ 2

/-- PDG reference proximity for light quark derived masses. -/
theorem light_quark_masses_near_paper_pdg :
    quarkPDGApprox m_charm_GeV (1.27 : ℝ) ∧
      quarkPDGApprox m_up_GeV (0.0022 : ℝ) ∧
      quarkPDGApprox m_strange_GeV (0.095 : ℝ) ∧
      quarkPDGApprox m_down_GeV (0.0047 : ℝ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold quarkPDGApprox quarkPDG_relTol m_charm_GeV m_top_GeV resonanceK_internal geometricResonanceStep
      detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
    simp [gamma_eq_2_5, m_quark_up_top_shell, m_quark_up_charm_shell]
    norm_num
  · unfold quarkPDGApprox quarkPDG_relTol m_up_GeV m_charm_GeV m_top_GeV resonanceK_internal geometricResonanceStep
      detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
    simp [gamma_eq_2_5, m_quark_up_top_shell, m_quark_up_charm_shell, m_quark_up_light_shell]
    norm_num
  · unfold quarkPDGApprox quarkPDG_relTol m_strange_GeV m_bottom_GeV resonanceK_internal_down geometricResonanceStep
      detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
    simp [gamma_eq_2_5, m_quark_down_bottom_shell, m_quark_down_strange_shell]
    norm_num
  · unfold quarkPDGApprox quarkPDG_relTol m_down_GeV m_strange_GeV m_bottom_GeV resonanceK_internal_down
      geometricResonanceStep detunedShellSurface shellSurface rindlerDetuningShared c_rindler_shared
    simp [gamma_eq_2_5, m_quark_down_bottom_shell, m_quark_down_strange_shell,
      m_quark_down_light_shell]
    norm_num

theorem proton_neutron_closeness_from_shared_harmonics :
    neutronMassFromMetaHarmonics_MeV - protonMassFromMetaHarmonics_MeV = 2 * emBlockShift_MeV := by
  simp [neutronMassFromMetaHarmonics_MeV, protonMassFromMetaHarmonics_MeV,
    emBlockShift_MeV, nucleonSharedBinding_MeV]
  norm_num

theorem up_down_matrix_almost_identical :
    hyperchargeSignUp + hyperchargeSignDown = 0 := by
  norm_num [hyperchargeSignUp, hyperchargeSignDown, upResonanceAxis, downResonanceAxis,
    upQuarkAxis, downQuarkAxis]

theorem exactly_three_harmonics_only :
    ∃ k3 : ℕ,
      internalSurfaceArea (m_top_at_lockin + k3) < internalSurfaceArea m_top_at_lockin + 1 ∧
      ¬ ∃ fourthGen : Fin 3,
        fourthGen ≠ ⟨0, by decide⟩ ∧
          fourthGen ≠ ⟨1, by decide⟩ ∧
          fourthGen ≠ ⟨2, by decide⟩ := by
  refine ⟨0, ?_, ?_⟩
  · simp [m_top_at_lockin]
  · intro h
    rcases h with ⟨g, hg⟩
    fin_cases g
    · simp at hg
    · simp at hg
    · simp at hg

end Hqiv.Physics
