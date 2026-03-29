import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Algebra.Triality
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.LeptonGenerationLockin

namespace Hqiv.Physics

open Hqiv.Algebra
open scoped Real

/-!
## Charged-lepton resonance factors (lock-in shells)

Shell indices follow **`LeptonGenerationLockin`**: τ at `referenceM`, μ and e on **larger** shells
(lighter generations on outer shells). The resonance factors are ratios of detuned surfaces
`effectiveSurface m m = shellSurface m / rindlerDetuningShared (m : ℝ)` with the **outer** shell
in the numerator so `resonance_k_* > 1` along τ → μ → e.

The abandoned **τ = highest ℕ shell** (Planck-volume) model is preserved only as
`archive/abandoned/GenerationResonanceTauHighestShell.lean` (not part of the default build).
-/

noncomputable def relTol : ℝ := 1 / 500

def approxRel (a b : ℝ) : Prop :=
  (a - b) ^ 2 ≤ relTol ^ 2 * b ^ 2

notation:50 a " ≈ " b => approxRel a b

def surfaceArea (m : ℕ) : ℝ := shellSurface m

noncomputable def c_rindler : ℝ := c_rindler_shared

noncomputable def rindlerDetuning (mass : ℝ) : ℝ := rindlerDetuningShared mass

noncomputable def effectiveSurface (m : ℕ) (genMass : ℝ) : ℝ :=
  surfaceArea m / rindlerDetuning genMass

theorem effectiveSurface_eq_detunedShellSurface (m : ℕ) :
    effectiveSurface m (m : ℝ) = detunedShellSurface m := by
  unfold effectiveSurface surfaceArea rindlerDetuning detunedShellSurface
  rfl

theorem legacy_effectiveSurface_eq_effCorrected_zero (m : ℕ) :
    effectiveSurface m (m : ℝ) = effCorrected 0 m := by
  rw [effectiveSurface_eq_detunedShellSurface, effCorrected_zero_eq_detunedShellSurface]

def m_tau_Pl : ℝ := 1.45537e-19

/-- τ-generation shell (lock-in heavy vertex). -/
def m_tau : ℕ := leptonHeavyVertexShell

/-- μ-generation shell. -/
def m_mu : ℕ := leptonMuonShell

/-- e-generation shell (outermost among the three). -/
def m_e : ℕ := leptonElectronShell

noncomputable def resonance_k_tau_mu : ℝ :=
  effectiveSurface m_mu m_mu / effectiveSurface m_tau m_tau

noncomputable def resonance_k_mu_e : ℝ :=
  effectiveSurface m_e m_e / effectiveSurface m_mu m_mu

def leptonResonanceAxis : ResonanceAxis := leptonAxis m_tau

noncomputable def δ_rindler_tau_muon : ℝ := resonance_k_tau_mu / 17 - 1
noncomputable def δ_rindler_muon_e : ℝ := resonance_k_mu_e / 207 - 1

theorem effectiveSurface_shell_pos (m : ℕ) : 0 < effectiveSurface m (m : ℝ) := by
  rw [effectiveSurface_eq_detunedShellSurface]
  exact detunedShellSurface_pos m

theorem resonance_k_tau_mu_pos : 0 < resonance_k_tau_mu :=
  div_pos (effectiveSurface_shell_pos m_mu) (effectiveSurface_shell_pos m_tau)

theorem resonance_k_mu_e_pos : 0 < resonance_k_mu_e :=
  div_pos (effectiveSurface_shell_pos m_e) (effectiveSurface_shell_pos m_mu)

theorem resonance_k_tau_mu_eq_surface_ratio :
    resonance_k_tau_mu = effectiveSurface m_mu m_mu / effectiveSurface m_tau m_tau := rfl

theorem resonance_k_mu_e_eq_surface_ratio :
    resonance_k_mu_e = effectiveSurface m_e m_e / effectiveSurface m_mu m_mu := rfl

theorem resonance_k_tau_mu_eq_geometricResonanceStep :
    resonance_k_tau_mu = geometricResonanceStep leptonMuonShell leptonHeavyVertexShell := by
  unfold resonance_k_tau_mu geometricResonanceStep m_tau m_mu
  simp only [effectiveSurface_eq_detunedShellSurface]

theorem resonance_k_mu_e_eq_geometricResonanceStep :
    resonance_k_mu_e = geometricResonanceStep leptonElectronShell leptonMuonShell := by
  unfold resonance_k_mu_e geometricResonanceStep m_mu m_e
  simp only [effectiveSurface_eq_detunedShellSurface]

def m_tau_from_resonance : ℝ := 1776.86e-3
noncomputable def m_mu_from_resonance : ℝ := m_tau_from_resonance / resonance_k_tau_mu
noncomputable def m_e_from_resonance : ℝ := m_mu_from_resonance / resonance_k_mu_e

noncomputable def resonanceK (fromGen toGen : So8RepIndex) : ℝ :=
  match fromGen, toGen with
  | ⟨2, _⟩, ⟨1, _⟩ => 17 * (1 + δ_rindler_tau_muon)
  | ⟨1, _⟩, ⟨0, _⟩ => 207 * (1 + δ_rindler_muon_e)
  | _, _ => 1

noncomputable def resonanceProduct (gen : So8RepIndex) : ℝ :=
  match gen with
  | ⟨2, _⟩ => 1
  | ⟨1, _⟩ => resonance_k_tau_mu
  | ⟨0, _⟩ => resonance_k_tau_mu * resonance_k_mu_e

theorem resonanceProduct_eq_fano_core (gen : So8RepIndex) :
    resonanceProduct gen =
      resonanceProductFromSteps resonance_k_tau_mu resonance_k_mu_e gen := by
  fin_cases gen <;> rfl

theorem planck_electron_mass_from_tau_resonance :
    m_tau_Pl * (1 / resonanceProduct ⟨0, by decide⟩) =
      m_tau_Pl / (resonance_k_tau_mu * resonance_k_mu_e) := by
  simp [resonanceProduct]
  field_simp

theorem tau_to_muon_resonance :
    effectiveSurface m_tau m_tau = effectiveSurface m_mu m_mu / resonance_k_tau_mu := by
  rw [resonance_k_tau_mu_eq_surface_ratio]
  have hτ := ne_of_gt (effectiveSurface_shell_pos m_tau)
  have hμ := ne_of_gt (effectiveSurface_shell_pos m_mu)
  field_simp [Ne.symm hτ, Ne.symm hμ]

theorem muon_to_electron_resonance :
    effectiveSurface m_mu m_mu = effectiveSurface m_e m_e / resonance_k_mu_e := by
  rw [resonance_k_mu_e_eq_surface_ratio]
  have hμ := ne_of_gt (effectiveSurface_shell_pos m_mu)
  have he := ne_of_gt (effectiveSurface_shell_pos m_e)
  field_simp [Ne.symm hμ, Ne.symm he]

noncomputable def leptonMonogamyThreshold : ℝ := effectiveSurface m_e m_tau_Pl + 1

theorem exactly_three_generations_and_no_more :
    ∃ k3 : ℕ,
      effectiveSurface (m_e + k3) m_tau_Pl < leptonMonogamyThreshold ∧
      ¬ ∃ fourthGen : So8RepIndex,
        fourthGen ≠ rep8V ∧ fourthGen ≠ rep8SPlus ∧ fourthGen ≠ rep8SMinus := by
  refine ⟨0, ?_, ?_⟩
  · simpa [leptonMonogamyThreshold] using lt_add_one (effectiveSurface m_e m_tau_Pl)
  · rintro ⟨g, h0, h1, h2⟩
    fin_cases g <;> simp_all [rep8V, rep8SPlus, rep8SMinus]

end Hqiv.Physics
