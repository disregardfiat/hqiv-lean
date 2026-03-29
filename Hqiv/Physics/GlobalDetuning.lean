import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Hqiv.Physics.FanoResonance
import Hqiv.Geometry.HQVMetric

/-!
# Global Rindler detuning (shared across resonance ladders)

This module packages the **scalar shift** `δ` in the denominator
`1 + (γ/2)·m + δ` used for **δ-corrected detuned shell surfaces** and a **global**
hypothesis `λ · obs` reused on every ladder that shares the same stars-and-bars
numerator `(m+1)(m+2)`.

Used by:
* `LeptonResonanceGlobalDetuning` (charged leptons),
* `QuarkLadderGlobalDetuning` (internal quark steps),
* `HarmonicLadderGlobalDetuning` (link to the same shell index `m` as `phi_of_shell`).

**Identification:** `GlobalDetuningHypothesis.fromLapseScalars` sets `obs := Φ + φ·t`, i.e. the
**increment of `HQVM_lapse` above 1** (same combination as in the metric story). This is
**pure algebra** in Lean — no claim that a particular observer datum equals a PDG ratio.
-/

namespace Hqiv.Physics

open scoped Real

noncomputable section

/-!
### δ-corrected surfaces and geometric steps
-/

noncomputable def rindlerDenWithDelta (δ : ℝ) (m : ℕ) : ℝ :=
  1 + c_rindler_shared * (m : ℝ) + δ

theorem rindlerDenWithDelta_eq_rindler_plus_delta (δ : ℝ) (m : ℕ) :
    rindlerDenWithDelta δ m = rindlerDetuningShared (m : ℝ) + δ := by
  unfold rindlerDenWithDelta rindlerDetuningShared
  ring

theorem rindlerDenWithDelta_zero (m : ℕ) : rindlerDenWithDelta 0 m = rindlerDetuningShared (m : ℝ) := by
  rw [rindlerDenWithDelta_eq_rindler_plus_delta, add_zero]

noncomputable def effCorrected (δ : ℝ) (m : ℕ) : ℝ :=
  shellSurface m / rindlerDenWithDelta δ m

def RindlerDenDeltaPos (δ : ℝ) (m : ℕ) : Prop :=
  0 < rindlerDenWithDelta δ m

theorem effCorrected_pos (δ : ℝ) (m : ℕ) (h : RindlerDenDeltaPos δ m) : 0 < effCorrected δ m := by
  unfold effCorrected RindlerDenDeltaPos at *
  apply div_pos
  · unfold shellSurface; positivity
  · exact h

theorem effCorrected_zero_eq_detunedShellSurface (m : ℕ) : effCorrected 0 m = detunedShellSurface m := by
  unfold effCorrected detunedShellSurface
  congr 1
  exact rindlerDenWithDelta_zero m

theorem c_rindler_shared_eq_one_fifth : c_rindler_shared = (1 : ℝ) / 5 := by
  unfold c_rindler_shared
  rw [Hqiv.gamma_eq_2_5]
  norm_num

/-- For nonnegative global shift `δ`, the δ-corrected effective surface **strictly increases** with shell index. -/
theorem effCorrected_succ_lt {δ : ℝ} (hδ : 0 ≤ δ) (m : ℕ) :
    effCorrected δ m < effCorrected δ (Nat.succ m) := by
  unfold effCorrected shellSurface rindlerDenWithDelta
  rw [c_rindler_shared_eq_one_fifth]
  have hm : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hden0 : 0 < (1 : ℝ) + (1 : ℝ) / 5 * (m : ℝ) + δ := by linarith [hm, hδ]
  have hden1 : 0 < (1 : ℝ) + (1 : ℝ) / 5 * ((m : ℝ) + 1) + δ := by linarith [hm, hδ]
  have hne0 : (1 : ℝ) + (1 : ℝ) / 5 * (m : ℝ) + δ ≠ 0 := ne_of_gt hden0
  have hne1 : (1 : ℝ) + (1 : ℝ) / 5 * ((m : ℝ) + 1) + δ ≠ 0 := ne_of_gt hden1
  simp only [Nat.cast_succ]
  have hlt :
      ((m : ℝ) + 1) * ((m : ℝ) + 2) * ((1 : ℝ) + (1 : ℝ) / 5 * ((m : ℝ) + 1) + δ) <
        ((m : ℝ) + 2) * ((m : ℝ) + 3) * ((1 : ℝ) + (1 : ℝ) / 5 * (m : ℝ) + δ) := by
    ring_nf
    nlinarith [sq_nonneg ((m : ℝ) + 1), hm, hδ]
  have hfrac :
      (((m : ℝ) + 1) * ((m : ℝ) + 2) * ((1 : ℝ) + (1 : ℝ) / 5 * ((m : ℝ) + 1) + δ) -
          ((m : ℝ) + 1 + 1) * ((m : ℝ) + 1 + 2) * ((1 : ℝ) + (1 : ℝ) / 5 * (m : ℝ) + δ)) /
        (((1 : ℝ) + (1 : ℝ) / 5 * (m : ℝ) + δ) * ((1 : ℝ) + (1 : ℝ) / 5 * ((m : ℝ) + 1) + δ)) <
        0 := by
    have := div_neg_of_neg_of_pos (sub_lt_zero.mpr hlt) (mul_pos hden0 hden1)
    convert this using 1
    ring
  exact (mul_sub_mul_div_mul_neg_iff hne0 hne1).mp hfrac

/-- `effCorrected δ m < effCorrected δ (m + k + 1)` for every `k` (with `0 ≤ δ`). -/
theorem effCorrected_lt_add_dist {δ : ℝ} (hδ : 0 ≤ δ) (m k : ℕ) :
    effCorrected δ m < effCorrected δ (m + k + 1) := by
  induction k with
  | zero =>
    simpa using effCorrected_succ_lt hδ m
  | succ k ih =>
    simpa [add_assoc, add_comm, add_left_comm] using
      lt_trans ih (effCorrected_succ_lt hδ (m + k + 1))

/-- For `0 ≤ δ` and `m < n`, `effCorrected δ` is strictly monotone in the shell index. -/
theorem effCorrected_strictMono_nat {δ : ℝ} (hδ : 0 ≤ δ) {m n : ℕ} (hmn : m < n) :
    effCorrected δ m < effCorrected δ n := by
  have hn : n = m + (n - m - 1) + 1 := by omega
  rw [hn]
  exact effCorrected_lt_add_dist hδ m (n - m - 1)

/-- At fixed shell `m`, larger additive shift `δ` **lowers** `effCorrected` (larger denominator). -/
theorem effCorrected_lt_of_lt_delta {δ1 δ2 : ℝ} (m : ℕ) (hδ : δ1 < δ2)
    (h1 : RindlerDenDeltaPos δ1 m) (h2 : RindlerDenDeltaPos δ2 m) :
    effCorrected δ2 m < effCorrected δ1 m := by
  unfold effCorrected
  have hdenlt : rindlerDenWithDelta δ1 m < rindlerDenWithDelta δ2 m := by
    unfold rindlerDenWithDelta
    linarith [hδ]
  have hN : 0 < shellSurface m := by unfold shellSurface; positivity
  have hD1 : 0 < rindlerDenWithDelta δ1 m := h1
  have hD2 : 0 < rindlerDenWithDelta δ2 m := h2
  have hne1 : rindlerDenWithDelta δ1 m ≠ 0 := ne_of_gt hD1
  have hne2 : rindlerDenWithDelta δ2 m ≠ 0 := ne_of_gt hD2
  refine (mul_sub_mul_div_mul_neg_iff hne2 hne1).mp ?_
  have hsub :
      shellSurface m * rindlerDenWithDelta δ1 m - shellSurface m * rindlerDenWithDelta δ2 m < 0 := by
    have := mul_lt_mul_of_pos_left hdenlt hN
    linarith
  convert div_neg_of_neg_of_pos (sub_lt_zero.mpr hsub) (mul_pos hD2 hD1) using 1
  ring

/-- Corrected analogue of `geometricResonanceStep` (`FanoResonance`). -/
noncomputable def geometricResonanceStepCorrected (δ : ℝ) (m_from m_to : ℕ) : ℝ :=
  effCorrected δ m_from / effCorrected δ m_to

theorem geometricResonanceStepCorrected_eq (δ : ℝ) (m_from m_to : ℕ) :
    geometricResonanceStepCorrected δ m_from m_to =
      effCorrected δ m_from / effCorrected δ m_to :=
  rfl

theorem geometricResonanceStepCorrected_zero (m_from m_to : ℕ) :
    geometricResonanceStepCorrected 0 m_from m_to = geometricResonanceStep m_from m_to := by
  unfold geometricResonanceStepCorrected geometricResonanceStep
  rw [effCorrected_zero_eq_detunedShellSurface, effCorrected_zero_eq_detunedShellSurface]

/-!
### Global hypothesis and unified effective surface
-/

structure GlobalDetuningHypothesis where
  lambda : ℝ
  obs : ℝ

noncomputable def deltaGlobal (h : GlobalDetuningHypothesis) : ℝ :=
  h.lambda * h.obs

/-- Shell-independent shift `δ(m) = λ · obs` (placeholder; a richer model uses `ℕ → ℝ`). -/
noncomputable def deltaM (h : GlobalDetuningHypothesis) (_m : ℕ) : ℝ :=
  deltaGlobal h

noncomputable def effUnified (h : GlobalDetuningHypothesis) (m : ℕ) : ℝ :=
  shellSurface m / (rindlerDetuningShared (m : ℝ) + deltaM h m)

theorem effUnified_eq_shell_over_det (h : GlobalDetuningHypothesis) (m : ℕ) :
    effUnified h m = shellSurface m / (1 + c_rindler_shared * (m : ℝ) + deltaM h m) := by
  unfold effUnified rindlerDetuningShared
  ring

theorem deltaGlobal_eq_lambda_obs (h : GlobalDetuningHypothesis) : deltaGlobal h = h.lambda * h.obs :=
  rfl

/-!
### Cumulative rapidity budget (dynamic Rindler layer)

Small second-order correction `β_cum · (φ·t)` on top of `deltaGlobal`, using the same
informational time track as `timeAngle` (`HQVMetric`). Lattice-only: no continuum chart.
-/

/-- Cumulative rapidity budget: agrees with `timeAngle φ t` (`φ·t`). -/
noncomputable def phi_t_cum (φ t : ℝ) : ℝ :=
  φ * t

theorem phi_t_cum_eq_timeAngle (φ t : ℝ) : phi_t_cum φ t = timeAngle φ t := rfl

/-- **One-line extension:** global δ plus `β_cum` × cumulative rapidity (tightens detuning residuals). -/
noncomputable def delta_auxiliary_phi_per_shell (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) : ℝ :=
  deltaGlobal h + β_cum * phi_t_cum φ t

theorem delta_auxiliary_phi_per_shell_eq (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) :
    delta_auxiliary_phi_per_shell h φ t β_cum = deltaGlobal h + β_cum * phi_t_cum φ t := rfl

theorem delta_auxiliary_phi_per_shell_eq_delta_plus_beta_timeAngle (h : GlobalDetuningHypothesis)
    (φ t β_cum : ℝ) :
    delta_auxiliary_phi_per_shell h φ t β_cum = deltaGlobal h + β_cum * timeAngle φ t := by
  simp [delta_auxiliary_phi_per_shell, phi_t_cum_eq_timeAngle]

/-- δ-corrected Rindler denominator using `delta_auxiliary_phi_per_shell` (includes rapidity budget). -/
noncomputable def rindlerDenWithDeltaRapidity (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (m : ℕ) : ℝ :=
  rindlerDenWithDelta (delta_auxiliary_phi_per_shell h φ t β_cum) m

theorem rindlerDenWithDeltaRapidity_eq (h : GlobalDetuningHypothesis) (φ t β_cum : ℝ) (m : ℕ) :
    rindlerDenWithDeltaRapidity h φ t β_cum m =
      1 + c_rindler_shared * (m : ℝ) + deltaGlobal h + β_cum * phi_t_cum φ t := by
  unfold rindlerDenWithDeltaRapidity rindlerDenWithDelta delta_auxiliary_phi_per_shell
  ring

/-!
### HQVM packaging (proved identification at the level of real scalars)

`HQVM_lapse Φ φ t = 1 + Φ + φ·t` and `timeAngle φ t = φ·t` (`HQVMetric`).
We record the detuning `λ * (Φ + φ·t)` as `λ` times the **lapse increment** `(N - 1)`.
-/

/-- Use `obs := Φ + φ·t`, i.e. `HQVM_lapse Φ φ t - 1`. -/
noncomputable def GlobalDetuningHypothesis.fromLapseScalars (lam Φ φ t : ℝ) : GlobalDetuningHypothesis where
  lambda := lam
  obs := Φ + φ * t

theorem deltaGlobal_fromLapseScalars (lam Φ φ t : ℝ) :
    deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t) = lam * (Φ + φ * t) := by
  simp [deltaGlobal, GlobalDetuningHypothesis.fromLapseScalars]

theorem deltaGlobal_eq_lambda_mul_lapseIncrement (lam Φ φ t : ℝ) :
    deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t) =
      lam * (HQVM_lapse Φ φ t - 1) := by
  simp only [deltaGlobal, GlobalDetuningHypothesis.fromLapseScalars]
  refine congrArg (fun x => lam * x) ?_
  simp [HQVM_lapse]
  ring

theorem deltaGlobal_eq_lambda_mul_phi_plus_timeAngle (lam Φ φ t : ℝ) :
    deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t) =
      lam * (Φ + timeAngle φ t) := by
  simp [deltaGlobal, GlobalDetuningHypothesis.fromLapseScalars, timeAngle]

/-- `δ_global = λ·(Φ + φ·t)` is strictly increasing in `t` for `λ > 0`, `φ > 0`. -/
theorem deltaGlobal_strictMono_in_t (lam Φ φ t1 t2 : ℝ) (h_lam : 0 < lam) (h_phi : 0 < φ)
    (h_t : t1 < t2) :
    deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t1) <
      deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t2) := by
  rw [deltaGlobal_fromLapseScalars, deltaGlobal_fromLapseScalars]
  have hobs : Φ + φ * t1 < Φ + φ * t2 := by
    have hφt := mul_lt_mul_of_pos_left h_t h_phi
    linarith
  exact mul_lt_mul_of_pos_left hobs h_lam

/-- **Deprecated name:** earlier stub; use `deltaGlobal_eq_lambda_mul_lapseIncrement` / `fromLapseScalars`. -/
theorem physics_identification_global_detuning :
    ∀ lam Φ φ t : ℝ,
      deltaGlobal (GlobalDetuningHypothesis.fromLapseScalars lam Φ φ t) =
        lam * (HQVM_lapse Φ φ t - 1) :=
  deltaGlobal_eq_lambda_mul_lapseIncrement

end

end Hqiv.Physics
