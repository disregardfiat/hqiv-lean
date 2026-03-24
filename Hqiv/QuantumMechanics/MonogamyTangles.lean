import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField

namespace Hqiv.QM

open Hqiv

/-!
# Monogamy Through Tangles (HQIV mode-corrected)

This module gives a Lean-ready bridge between standard three-party tangle
monogamy (CKW style) and HQIV's discrete light-cone mode counting.

The key idea is to weight tangles by a shell-dependent HQIV factor
`etaMode m = new_modes m / available_modes referenceM`.
This can shift the effective monogamy budget relative to flat CKW.
-/

/-- Three-party tangle monogamy inequality (CKW form). -/
def ckwMonogamy (tauAB tauAC tauA_BC : ℝ) : Prop :=
  tauAB + tauAC ≤ tauA_BC

/-- HQIV mode-count correction from shell `m` to the lock-in reference shell. -/
noncomputable def etaMode (m : ℕ) : ℝ :=
  new_modes m / available_modes referenceM

theorem available_modes_pos (m : ℕ) : 0 < available_modes m := by
  rw [available_modes_eq]
  have h1 : 0 < (4 : ℝ) := by norm_num
  have h2 : 0 < (m : ℝ) + 2 := by positivity
  have h3 : 0 < (m : ℝ) + 1 := by positivity
  nlinarith

theorem new_modes_nonneg (m : ℕ) : 0 ≤ new_modes m := by
  cases m with
  | zero =>
      simpa [new_modes_zero] using le_of_lt (available_modes_pos 0)
  | succ k =>
      rw [new_modes_succ]
      positivity

theorem etaMode_nonneg (m : ℕ) : 0 ≤ etaMode m := by
  unfold etaMode
  exact div_nonneg (new_modes_nonneg m) (le_of_lt (available_modes_pos referenceM))

/-- Mode-corrected pair tangle at shell `m`. -/
noncomputable def correctedPairTangle (m : ℕ) (tau : ℝ) : ℝ :=
  etaMode m * tau

/-- Mode-corrected CKW inequality at shell `m`. -/
def correctedCkwMonogamy (m : ℕ) (tauAB tauAC tauA_BC : ℝ) : Prop :=
  correctedPairTangle m tauAB + correctedPairTangle m tauAC ≤ correctedPairTangle m tauA_BC

/--
If standard CKW monogamy holds, then HQIV mode-corrected monogamy holds with the
same tangle inputs after shell weighting.
-/
theorem corrected_monogamy_of_ckw (m : ℕ) {tauAB tauAC tauA_BC : ℝ}
    (hckw : ckwMonogamy tauAB tauAC tauA_BC) :
    correctedCkwMonogamy m tauAB tauAC tauA_BC := by
  unfold correctedCkwMonogamy correctedPairTangle ckwMonogamy at *
  have heta : 0 ≤ etaMode m := etaMode_nonneg m
  nlinarith [hckw, heta]

/--
If the mode factor is at most one, the HQIV correction tightens the total pairwise
tangle budget relative to the uncorrected sum.
-/
theorem corrected_pair_sum_le_uncorrected (m : ℕ) {tauAB tauAC : ℝ}
    (htau : 0 ≤ tauAB + tauAC) (heta : etaMode m ≤ 1) :
    correctedPairTangle m tauAB + correctedPairTangle m tauAC ≤ tauAB + tauAC := by
  unfold correctedPairTangle
  nlinarith [etaMode_nonneg m, htau, heta]

/-- φ-augmented shell factor: mode correction weighted by inverse auxiliary field. -/
noncomputable def etaModePhi (m : ℕ) : ℝ :=
  etaMode m / phi_of_shell m

theorem phi_of_shell_pos (m : ℕ) : 0 < phi_of_shell m := by
  rw [phi_of_shell_closed_form]
  have hcoeff : 0 < phiTemperatureCoeff := by
    norm_num [phiTemperatureCoeff]
  have hm : 0 < (m : ℝ) + 1 := by positivity
  nlinarith

theorem etaModePhi_nonneg (m : ℕ) : 0 ≤ etaModePhi m := by
  unfold etaModePhi
  exact div_nonneg (etaMode_nonneg m) (le_of_lt (phi_of_shell_pos m))

/-- φ-augmented corrected pair tangle. -/
noncomputable def correctedPairTanglePhi (m : ℕ) (tau : ℝ) : ℝ :=
  etaModePhi m * tau

/-- φ-augmented corrected CKW inequality. -/
def correctedCkwMonogamyPhi (m : ℕ) (tauAB tauAC tauA_BC : ℝ) : Prop :=
  correctedPairTanglePhi m tauAB + correctedPairTanglePhi m tauAC ≤
    correctedPairTanglePhi m tauA_BC

theorem corrected_monogamy_of_ckw_phi (m : ℕ) {tauAB tauAC tauA_BC : ℝ}
    (hckw : ckwMonogamy tauAB tauAC tauA_BC) :
    correctedCkwMonogamyPhi m tauAB tauAC tauA_BC := by
  unfold correctedCkwMonogamyPhi correctedPairTanglePhi ckwMonogamy at *
  have heta : 0 ≤ etaModePhi m := etaModePhi_nonneg m
  nlinarith [hckw, heta]

/--
Decoherence proxy from φ-augmented corrected pairwise budget.
Interpretation: for fixed nonnegative intrinsic pairwise tangle `tauPair`,
smaller shell factor implies less accessible coherent pairwise entanglement.
-/
noncomputable def coherenceProxy (m : ℕ) (tauPair : ℝ) : ℝ :=
  etaModePhi m * tauPair

/--
If the φ-augmented shell factor is nonincreasing across one shell step and
the intrinsic pairwise tangle is nonnegative, the coherence proxy is
nonincreasing across that step (formal decoherence monotonicity).
-/
theorem coherenceProxy_step_nonincreasing (m : ℕ) {tauPair : ℝ}
    (htau : 0 ≤ tauPair) (hstep : etaModePhi (m + 1) ≤ etaModePhi m) :
    coherenceProxy (m + 1) tauPair ≤ coherenceProxy m tauPair := by
  unfold coherenceProxy
  nlinarith [etaModePhi_nonneg m, etaModePhi_nonneg (m + 1), htau, hstep]

end Hqiv.QM
