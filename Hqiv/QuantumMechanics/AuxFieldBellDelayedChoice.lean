import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Geometry.AuxiliaryField
import Hqiv.QuantumMechanics.MonogamyTangles

namespace Hqiv.QM

open Hqiv

/-!
# AUX field, Bell structure, and delayed-choice eraser

This module gives a compact Lean formalization of two statements:

1. AUX scaling can push a CHSH-style correlator beyond the local bound.
2. A delayed-choice eraser can reshuffle coincidence channels while leaving
   singles rates unchanged (no-signaling style statement).

The setup stays algebraic and proof-oriented, so it can be reused as a
foundation for more detailed probability/amplitude models.
-/

/-- Local hidden-variable CHSH bound (normalized form). -/
def chshLocalBound : ℝ := 2

/--
AUX-scaled CHSH proxy at shell `m`.

The scale factor is `phi_of_shell m / 2`, so with `phi_of_shell m = 2(m+1)` the
effective multiplier is exactly `(m+1)`.
-/
noncomputable def auxChsh (m : ℕ) (S : ℝ) : ℝ :=
  (phi_of_shell m / phiTemperatureCoeff) * S

theorem auxChsh_closed_form (m : ℕ) (S : ℝ) :
    auxChsh m S = (m + 1 : ℝ) * S := by
  unfold auxChsh
  have hphi : phi_of_shell m = phiTemperatureCoeff * (m + 1 : ℝ) :=
    phi_of_shell_closed_form m
  rw [hphi]
  field_simp [phiTemperatureCoeff_eq_two]

/--
At shell `m = 0`, AUX scaling preserves the original CHSH value.
-/
theorem auxChsh_shell0 (S : ℝ) : auxChsh 0 S = S := by
  rw [auxChsh_closed_form]
  norm_num

/--
For baseline `S = 2`, the AUX-scaled CHSH proxy exceeds the local bound at every
nonzero shell (`m ≥ 1`).
-/
theorem auxChsh_violate_local_bound_of_one_le (m : ℕ) (hm : 1 ≤ m) :
    chshLocalBound < auxChsh m 2 := by
  rw [auxChsh_closed_form, chshLocalBound]
  have hm' : (2 : ℝ) < (m + 1 : ℝ) * 2 := by
    have hcast : (2 : ℝ) ≤ (m + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ hm
    nlinarith
  exact hm'

/-- Coincidence channel model used for delayed-choice eraser algebra. -/
noncomputable def coincidence (signal interference basis : ℝ) : ℝ :=
  signal + basis * interference

/-- Singles rate from averaging the two complementary eraser bases `+1` and `-1`. -/
noncomputable def singlesFromTwoBases (signal interference : ℝ) : ℝ :=
  (coincidence signal interference 1 + coincidence signal interference (-1)) / 2

/--
Complementary eraser choices produce opposite interference terms in coincidence
channels.
-/
theorem coincidence_complementary
    (signal interference : ℝ) :
    coincidence signal interference 1 - coincidence signal interference (-1)
      = 2 * interference := by
  unfold coincidence
  ring

/--
Delayed-choice eraser no-signaling statement:
after summing over complementary eraser outcomes, interference cancels and singles
depend only on `signal`.
-/
theorem singles_independent_of_eraser_choice
    (signal interference : ℝ) :
    singlesFromTwoBases signal interference = signal := by
  unfold singlesFromTwoBases coincidence
  ring

/--
Convex-mixture extension (two-component finite mixed-state proxy):
if each component has eraser-independent singles, any convex mixture does too.
-/
theorem singles_independent_of_eraser_choice_convex2
    (w signal1 signal2 interference1 interference2 : ℝ)
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) :
    w * singlesFromTwoBases signal1 interference1
      + (1 - w) * singlesFromTwoBases signal2 interference2
      = w * signal1 + (1 - w) * signal2 := by
  have _ := hw0
  have _ := hw1
  rw [singles_independent_of_eraser_choice signal1 interference1]
  rw [singles_independent_of_eraser_choice signal2 interference2]

/-!
## Measurement-collapse and energy bookkeeping (finite algebraic form)

These statements isolate what can be proved in a compact finite model:

1. If one keeps linear/calibrated evolution from basis states, nontrivial
   superpositions are not mapped to single-outcome states.
2. Therefore, obtaining a single definite outcome for nontrivial input requires
   an additional selection/collapse step (or equivalent nonlinearity).
3. Energy bookkeeping can remain explicit by routing any post-measurement deficit
   through an auxiliary/redshift channel.
-/

/-- Two-component toy state used for compact measurement algebra. -/
abbrev State2 := ℝ × ℝ

/-- Nontrivial superposition in the two-component toy model. -/
def nontrivialState (s : State2) : Prop :=
  s.1 ≠ 0 ∧ s.2 ≠ 0

/-- "Definite outcome" proxy: exactly one active component. -/
def definiteOutcome (s : State2) : Prop :=
  s.1 = 0 ∨ s.2 = 0

/-- Linear calibrated prediction for an input `(a,b)` in this toy layer. -/
def linearCalibratedPrediction (a b : ℝ) : State2 := (a, b)

/--
Linear calibrated evolution does not produce a definite single outcome
from a nontrivial superposition.
-/
theorem linear_prediction_not_definite_of_nontrivial
    {a b : ℝ} (h : a ≠ 0 ∧ b ≠ 0) :
    ¬ definiteOutcome (linearCalibratedPrediction a b) := by
  intro hdef
  unfold definiteOutcome linearCalibratedPrediction at hdef
  rcases hdef with ha | hb
  · exact h.1 ha
  · exact h.2 hb

/--
Collapse/selection requirement (finite algebraic form):
if a nontrivial input yields a definite outcome, that output cannot equal
the purely linear calibrated prediction.
-/
theorem collapse_required_for_definite_outcome
    {a b : ℝ} {post : State2}
    (hnontriv : a ≠ 0 ∧ b ≠ 0)
    (hdef : definiteOutcome post)
    (hlin : post = linearCalibratedPrediction a b) :
    False := by
  have hnot : ¬ definiteOutcome (linearCalibratedPrediction a b) :=
    linear_prediction_not_definite_of_nontrivial hnontriv
  exact hnot (by simpa [hlin] using hdef)

/--
Convex closure of the HQIV φ-corrected CKW inequality:
if two tuples satisfy corrected CKW at shell `m`, any convex mixture of tuples
also satisfies corrected CKW at the same shell. This is the finite mixed-state
style closure property in the present linear inequality layer.
-/
theorem correctedCkwMonogamyPhi_convex2
    (m : ℕ)
    (w : ℝ) (hw0 : 0 ≤ w) (hw1 : w ≤ 1)
    {τAB1 τAC1 τA_BC1 τAB2 τAC2 τA_BC2 : ℝ}
    (h1 : correctedCkwMonogamyPhi m τAB1 τAC1 τA_BC1)
    (h2 : correctedCkwMonogamyPhi m τAB2 τAC2 τA_BC2) :
    correctedCkwMonogamyPhi m
      (w * τAB1 + (1 - w) * τAB2)
      (w * τAC1 + (1 - w) * τAC2)
      (w * τA_BC1 + (1 - w) * τA_BC2) := by
  unfold correctedCkwMonogamyPhi correctedPairTanglePhi at *
  have h1w : w * (etaModePhi m * τAB1 + etaModePhi m * τAC1)
      ≤ w * (etaModePhi m * τA_BC1) := by
    exact mul_le_mul_of_nonneg_left h1 hw0
  have h2w : (1 - w) * (etaModePhi m * τAB2 + etaModePhi m * τAC2)
      ≤ (1 - w) * (etaModePhi m * τA_BC2) := by
    have h1mw : 0 ≤ 1 - w := by linarith
    exact mul_le_mul_of_nonneg_left h2 h1mw
  nlinarith [h1w, h2w]

/-- Quadratic toy energy on `State2`. -/
def stateEnergy (s : State2) : ℝ :=
  s.1 ^ 2 + s.2 ^ 2

/-- Redshifted observed energy from post energy and redshift `z`. -/
noncomputable def redshiftedEnergy (Epost z : ℝ) : ℝ :=
  Epost / (1 + z)

/--
Aux-channel balance identity: if `Epre = Epost + Δaux`, then post energy is
pre energy minus auxiliary-channel transfer.
-/
theorem energy_balance_with_aux
    (Epre Epost Δaux : ℝ)
    (hbal : Epre = Epost + Δaux) :
    Epost = Epre - Δaux := by
  nlinarith [hbal]

/-- If auxiliary transfer is nonnegative, post energy is no larger than pre energy. -/
theorem post_energy_le_pre_of_aux_nonneg
    (Epre Epost Δaux : ℝ)
    (hbal : Epre = Epost + Δaux)
    (haux : 0 ≤ Δaux) :
    Epost ≤ Epre := by
  nlinarith [hbal, haux]

/-- Exact conservation is recovered when auxiliary transfer vanishes. -/
theorem exact_conservation_when_aux_zero
    (Epre Epost : ℝ)
    (hbal : Epre = Epost + 0) :
    Epre = Epost := by
  nlinarith [hbal]

/-- Redshift-channel identity (well-defined when `z ≠ -1`). -/
theorem redshiftedEnergy_balance
    (Epost z : ℝ) (hz : z ≠ -1) :
    redshiftedEnergy Epost z * (1 + z) = Epost := by
  unfold redshiftedEnergy
  have hden : (1 + z) ≠ 0 := by
    intro hzero
    apply hz
    linarith
  calc
    (Epost / (1 + z)) * (1 + z) = Epost * ((1 + z) / (1 + z)) := by ring
    _ = Epost * 1 := by rw [div_self hden]
    _ = Epost := by ring

end Hqiv.QM
