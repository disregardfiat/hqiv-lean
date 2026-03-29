import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.GlobalDetuning

/-!
# Charged-lepton resonance ladder, global-detuning obstruction

Independent of Triality / SO(8) Lie closure. Shared Rindler scaffolding lives in `GlobalDetuning`
(`effCorrected`, `effUnified`, `GlobalDetuningHypothesis`, lapse bridge).

Shell anchors **`m_tau`**, **`m_mu`**, **`m_e`** match **`LeptonGenerationLockin`** — keep in sync
(τ at lock-in; μ and e on larger shells).

**HQVM packaging:** see `GlobalDetuningHypothesis.fromLapseScalars` and
`deltaGlobal_eq_lambda_mul_lapseIncrement` (proved).

**No PDG closure.**
-/

namespace Hqiv.Physics.LeptonResonanceGlobalDetuning

open scoped Real

noncomputable section

/-!
### A. Local ladder
-/

/-- τ / μ / e shells — must match `LeptonGenerationLockin`. -/
def m_tau : ℕ := 4

def m_mu : ℕ := 81

def m_e : ℕ := 16336

noncomputable def eff (m : ℕ) : ℝ :=
  shellSurface m / rindlerDetuningShared (m : ℝ)

theorem eff_eq_detunedShellSurface (m : ℕ) : eff m = detunedShellSurface m := by
  unfold eff detunedShellSurface
  rfl

theorem eff_pos (m : ℕ) : 0 < eff m := by
  simpa [eff_eq_detunedShellSurface] using detunedShellSurface_pos m

theorem eff_eq_effCorrected_zero (m : ℕ) : eff m = effCorrected 0 m := by
  rw [eff_eq_detunedShellSurface, effCorrected_zero_eq_detunedShellSurface]

/-- μ–τ surface ratio (outer / inner); same direction as `ChargedLeptonResonance.resonance_k_tau_mu`. -/
noncomputable def kTauMu : ℝ :=
  eff m_mu / eff m_tau

/-- e–μ surface ratio (outer / inner); same direction as `ChargedLeptonResonance.resonance_k_mu_e`. -/
noncomputable def kMuE : ℝ :=
  eff m_e / eff m_mu

theorem kTauMu_pos : 0 < kTauMu :=
  div_pos (eff_pos m_mu) (eff_pos m_tau)

theorem kMuE_pos : 0 < kMuE :=
  div_pos (eff_pos m_e) (eff_pos m_mu)

theorem kTauMu_eq_eff_ratio : kTauMu = eff m_mu / eff m_tau :=
  rfl

theorem kMuE_eq_eff_ratio : kMuE = eff m_e / eff m_mu :=
  rfl

theorem kTauMu_eq_geometricResonanceStep : kTauMu = geometricResonanceStep m_mu m_tau := by
  unfold kTauMu geometricResonanceStep
  simp [eff_eq_detunedShellSurface]

theorem kMuE_eq_geometricResonanceStep : kMuE = geometricResonanceStep m_e m_mu := by
  unfold kMuE geometricResonanceStep
  simp [eff_eq_detunedShellSurface]

noncomputable def kTauMuCorrected (δ : ℝ) : ℝ :=
  effCorrected δ m_mu / effCorrected δ m_tau

noncomputable def kMuECorrected (δ : ℝ) : ℝ :=
  effCorrected δ m_e / effCorrected δ m_mu

/-!
### Algebraic obstruction
-/

theorem tau_mu_ratio_iff_delta_linear (δ r₁ : ℝ) (Sτ Sμ : ℝ) (τ μ : ℝ)
    (hSμ : Sμ ≠ 0) (hDτ : 1 + c_rindler_shared * τ + δ ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) :
    (Sτ / (1 + c_rindler_shared * τ + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) = r₁ ↔
      δ * (Sτ - r₁ * Sμ) = r₁ * Sμ * (1 + c_rindler_shared * τ) - Sτ * (1 + c_rindler_shared * μ) := by
  have hne : Sμ * (1 + c_rindler_shared * τ + δ) ≠ 0 := mul_ne_zero hSμ hDτ
  have hrewrite :
      (Sτ / (1 + c_rindler_shared * τ + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) =
        (Sτ * (1 + c_rindler_shared * μ + δ)) / (Sμ * (1 + c_rindler_shared * τ + δ)) := by
    field_simp [hSμ, hDτ, hDμ]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Sτ * (1 + c_rindler_shared * μ + δ) = r₁ * Sμ * (1 + c_rindler_shared * τ + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Sτ * (1 + c_rindler_shared * μ + δ) = r₁ * Sμ * (1 + c_rindler_shared * τ + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

theorem mu_tau_ratio_iff_delta_linear (δ r₁ : ℝ) (Sτ Sμ : ℝ) (τ μ : ℝ)
    (hSτ : Sτ ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) (hDτ : 1 + c_rindler_shared * τ + δ ≠ 0) :
    (Sμ / (1 + c_rindler_shared * μ + δ)) / (Sτ / (1 + c_rindler_shared * τ + δ)) = r₁ ↔
      δ * (Sμ - r₁ * Sτ) = r₁ * Sτ * (1 + c_rindler_shared * μ) - Sμ * (1 + c_rindler_shared * τ) := by
  have hne : Sτ * (1 + c_rindler_shared * μ + δ) ≠ 0 := mul_ne_zero hSτ hDμ
  have hrewrite :
      (Sμ / (1 + c_rindler_shared * μ + δ)) / (Sτ / (1 + c_rindler_shared * τ + δ)) =
        (Sμ * (1 + c_rindler_shared * τ + δ)) / (Sτ * (1 + c_rindler_shared * μ + δ)) := by
    field_simp [hSτ, hDμ, hDτ]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Sμ * (1 + c_rindler_shared * τ + δ) = r₁ * Sτ * (1 + c_rindler_shared * μ + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Sμ * (1 + c_rindler_shared * τ + δ) = r₁ * Sτ * (1 + c_rindler_shared * μ + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

theorem mu_e_ratio_iff_delta_linear (δ r₂ : ℝ) (Sμ Se : ℝ) (μ e : ℝ)
    (hSe : Se ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) (hDe : 1 + c_rindler_shared * e + δ ≠ 0) :
    (Sμ / (1 + c_rindler_shared * μ + δ)) / (Se / (1 + c_rindler_shared * e + δ)) = r₂ ↔
      δ * (Sμ - r₂ * Se) = r₂ * Se * (1 + c_rindler_shared * μ) - Sμ * (1 + c_rindler_shared * e) := by
  have hne : Se * (1 + c_rindler_shared * μ + δ) ≠ 0 := mul_ne_zero hSe hDμ
  have hrewrite :
      (Sμ / (1 + c_rindler_shared * μ + δ)) / (Se / (1 + c_rindler_shared * e + δ)) =
        (Sμ * (1 + c_rindler_shared * e + δ)) / (Se * (1 + c_rindler_shared * μ + δ)) := by
    field_simp [hSe, hDμ, hDe]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Sμ * (1 + c_rindler_shared * e + δ) = r₂ * Se * (1 + c_rindler_shared * μ + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Sμ * (1 + c_rindler_shared * e + δ) = r₂ * Se * (1 + c_rindler_shared * μ + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

theorem e_mu_ratio_iff_delta_linear (δ r₂ : ℝ) (Sμ Se : ℝ) (μ e : ℝ)
    (hSμ : Sμ ≠ 0) (hDe : 1 + c_rindler_shared * e + δ ≠ 0) (hDμ : 1 + c_rindler_shared * μ + δ ≠ 0) :
    (Se / (1 + c_rindler_shared * e + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) = r₂ ↔
      δ * (Se - r₂ * Sμ) = r₂ * Sμ * (1 + c_rindler_shared * e) - Se * (1 + c_rindler_shared * μ) := by
  have hne : Sμ * (1 + c_rindler_shared * e + δ) ≠ 0 := mul_ne_zero hSμ hDe
  have hrewrite :
      (Se / (1 + c_rindler_shared * e + δ)) / (Sμ / (1 + c_rindler_shared * μ + δ)) =
        (Se * (1 + c_rindler_shared * μ + δ)) / (Sμ * (1 + c_rindler_shared * e + δ)) := by
    field_simp [hSμ, hDe, hDμ]
  rw [hrewrite]
  constructor
  · intro h
    rw [div_eq_iff hne] at h
    have hmul : Se * (1 + c_rindler_shared * μ + δ) = r₂ * Sμ * (1 + c_rindler_shared * e + δ) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using h
    linear_combination hmul
  · intro h
    rw [div_eq_iff hne]
    have hmul : Se * (1 + c_rindler_shared * μ + δ) = r₂ * Sμ * (1 + c_rindler_shared * e + δ) := by
      linear_combination h
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul

noncomputable def Sτ : ℝ := shellSurface m_tau
noncomputable def Sμ : ℝ := shellSurface m_mu
noncomputable def Se : ℝ := shellSurface m_e

noncomputable def τr : ℝ := (m_tau : ℝ)
noncomputable def μr : ℝ := (m_mu : ℝ)
noncomputable def er : ℝ := (m_e : ℝ)

theorem shellSurface_ne_zero (m : ℕ) : shellSurface m ≠ 0 := by
  unfold shellSurface
  have h1 : (0 : ℝ) < (m + 1 : ℝ) := by exact_mod_cast Nat.succ_pos _
  have h2 : (0 : ℝ) < (m + 2 : ℝ) := by exact_mod_cast Nat.succ_pos _
  nlinarith

noncomputable def δNumTauMu (r₁ : ℝ) : ℝ :=
  r₁ * Sτ * (1 + c_rindler_shared * μr) - Sμ * (1 + c_rindler_shared * τr)

noncomputable def δDenTauMu (r₁ : ℝ) : ℝ :=
  Sμ - r₁ * Sτ

noncomputable def δNumMuE (r₂ : ℝ) : ℝ :=
  r₂ * Sμ * (1 + c_rindler_shared * er) - Se * (1 + c_rindler_shared * μr)

noncomputable def δDenMuE (r₂ : ℝ) : ℝ :=
  Se - r₂ * Sμ

noncomputable def singleDeltaCompatResidual (r₁ r₂ : ℝ) : ℝ :=
  δNumTauMu r₁ * δDenMuE r₂ - δNumMuE r₂ * δDenTauMu r₁

theorem kTauMuCorrected_eq_iff_delta_linear (δ r₁ : ℝ)
    (hDτ : rindlerDenWithDelta δ m_tau ≠ 0) (hDμ : rindlerDenWithDelta δ m_mu ≠ 0) :
    kTauMuCorrected δ = r₁ ↔
      δ * (Sμ - r₁ * Sτ) = δNumTauMu r₁ := by
  simpa [kTauMuCorrected, effCorrected, rindlerDenWithDelta, Sτ, Sμ, τr, μr, δNumTauMu]
    using mu_tau_ratio_iff_delta_linear δ r₁ _ _ _ _ (shellSurface_ne_zero m_tau) hDμ hDτ

theorem kMuECorrected_eq_iff_delta_linear (δ r₂ : ℝ)
    (hDμ : rindlerDenWithDelta δ m_mu ≠ 0) (hDe : rindlerDenWithDelta δ m_e ≠ 0) :
    kMuECorrected δ = r₂ ↔
      δ * (Se - r₂ * Sμ) = δNumMuE r₂ := by
  simpa [kMuECorrected, effCorrected, rindlerDenWithDelta, Sμ, Se, μr, er, δNumMuE]
    using e_mu_ratio_iff_delta_linear δ r₂ _ _ _ _ (shellSurface_ne_zero m_mu) hDe hDμ

theorem single_delta_both_ratios_implies_compat_aux (δ r₁ r₂ : ℝ)
    (h₁ : δ * (Sμ - r₁ * Sτ) = δNumTauMu r₁) (h₂ : δ * (Se - r₂ * Sμ) = δNumMuE r₂) :
    singleDeltaCompatResidual r₁ r₂ = 0 := by
  unfold singleDeltaCompatResidual δDenTauMu δDenMuE
  have hτ : δNumTauMu r₁ = δ * (Sμ - r₁ * Sτ) := h₁.symm
  have hμ : δNumMuE r₂ = δ * (Se - r₂ * Sμ) := h₂.symm
  rw [hτ, hμ]
  ring

theorem both_ratios_implies_compat_residual_zero (δ r₁ r₂ : ℝ)
    (hDτ : rindlerDenWithDelta δ m_tau ≠ 0) (hDμ : rindlerDenWithDelta δ m_mu ≠ 0)
    (hDe : rindlerDenWithDelta δ m_e ≠ 0)
    (hkm : kTauMuCorrected δ = r₁) (hke : kMuECorrected δ = r₂) :
    singleDeltaCompatResidual r₁ r₂ = 0 := by
  have h1' := (kTauMuCorrected_eq_iff_delta_linear δ r₁ hDτ hDμ).1 hkm
  have h2' := (kMuECorrected_eq_iff_delta_linear δ r₂ hDμ hDe).1 hke
  exact single_delta_both_ratios_implies_compat_aux δ r₁ r₂ h1' h2'

theorem necessary_compat_of_single_delta (δ r₁ r₂ : ℝ)
    (hDτ : rindlerDenWithDelta δ m_tau ≠ 0) (hDμ : rindlerDenWithDelta δ m_mu ≠ 0)
    (hDe : rindlerDenWithDelta δ m_e ≠ 0)
    (hkm : kTauMuCorrected δ = r₁) (hke : kMuECorrected δ = r₂) :
    singleDeltaCompatResidual r₁ r₂ = 0 :=
  both_ratios_implies_compat_residual_zero δ r₁ r₂ hDτ hDμ hDe hkm hke

theorem compat_residual_eq_zero_iff_deltaEq (r₁ r₂ : ℝ)
    (hden1 : Sμ - r₁ * Sτ ≠ 0) (hden2 : Se - r₂ * Sμ ≠ 0) :
    singleDeltaCompatResidual r₁ r₂ = 0 ↔
      δNumTauMu r₁ / (Sμ - r₁ * Sτ) = δNumMuE r₂ / (Se - r₂ * Sμ) := by
  unfold singleDeltaCompatResidual δDenTauMu δDenMuE
  rw [sub_eq_zero, ← div_eq_div_iff hden1 hden2]

/-!
### Open problem (documentation)
-/

def OpenProblem : Prop :=
  True

end

end Hqiv.Physics.LeptonResonanceGlobalDetuning
