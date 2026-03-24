import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Hqiv.QuantumMechanics.MonogamyTangles

namespace Hqiv.QM

open Hqiv

/-!
# Phi-Augmented Monotonicity Conditions (Turnkey)

This module gives explicit sufficient conditions for
`etaModePhi (m + 1) ≤ etaModePhi m`, then derives an unconditional
stepwise decoherence monotonicity theorem for the current HQIV
mode-count and auxiliary-field laws.
-/

/-- Closed form for `new_modes` in this HQIV ladder (`m = 0` and `m ≥ 1`). -/
theorem new_modes_linear (m : ℕ) : new_modes m = 8 * (m + 1 : ℝ) := by
  cases m with
  | zero =>
      rw [new_modes_zero, available_modes_eq]
      norm_num
  | succ k =>
      rw [new_modes_succ]
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_comm, add_left_comm]

/-- Closed form for the auxiliary field (`phiTemperatureCoeff = 2`). -/
theorem phi_of_shell_linear (m : ℕ) : phi_of_shell m = 2 * (m + 1 : ℝ) := by
  simpa [phiTemperatureCoeff_eq_two] using phi_of_shell_closed_form m

/--
`etaModePhi` is constant in shell index for the current HQIV laws.
In natural units this constant is `1/((referenceM+2)(referenceM+1))`.
-/
theorem etaModePhi_constant (m : ℕ) :
    etaModePhi m = 1 / (((referenceM + 2 : ℕ) : ℝ) * (referenceM + 1 : ℝ)) := by
  unfold etaModePhi etaMode
  rw [new_modes_linear, available_modes_eq referenceM, phi_of_shell_linear]
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]

/-- Immediate corollary: `etaModePhi` is nonincreasing (equality case). -/
theorem etaModePhi_nonincreasing (m : ℕ) :
    etaModePhi (m + 1) ≤ etaModePhi m := by
  rw [etaModePhi_constant (m + 1), etaModePhi_constant m]

/--
Sufficient-condition form:
if mode growth and φ-growth are linear with these coefficients,
then `etaModePhi` is nonincreasing.
-/
theorem etaModePhi_nonincreasing_of_linear_growth
    (h_new : ∀ m, new_modes m = 8 * (m + 1 : ℝ))
    (h_phi : ∀ m, phi_of_shell m = 2 * (m + 1 : ℝ))
    (m : ℕ) :
    etaModePhi (m + 1) ≤ etaModePhi m := by
  unfold etaModePhi etaMode
  rw [h_new (m + 1), h_new m, h_phi (m + 1), h_phi m]
  have hav : (available_modes referenceM) ≠ 0 := ne_of_gt (available_modes_pos referenceM)
  have hL :
      8 * (↑(m + 1) + 1) / available_modes referenceM / (2 * (↑(m + 1) + 1)) =
        4 / available_modes referenceM := by
    field_simp [hav]
    norm_num
  have hR :
      8 * (↑m + 1) / available_modes referenceM / (2 * (↑m + 1)) =
        4 / available_modes referenceM := by
    field_simp [hav]
    norm_num
  rw [hL, hR]

/--
Decoherence proxy monotonicity with no extra model assumptions:
for nonnegative intrinsic pairwise tangle, the φ-augmented coherence proxy
is nonincreasing step-to-step.
-/
theorem coherenceProxy_step_nonincreasing_unconditional (m : ℕ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    coherenceProxy (m + 1) τ ≤ coherenceProxy m τ := by
  exact coherenceProxy_step_nonincreasing m hτ (etaModePhi_nonincreasing m)

end Hqiv.QM
