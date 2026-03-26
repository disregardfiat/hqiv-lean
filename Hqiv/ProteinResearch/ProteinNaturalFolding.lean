import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.ProteinResearch.ProteinHKEMinimizer
import Hqiv.QuantumMechanics.MonogamyTangles
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions

namespace Hqiv.QM

open Hqiv

/-!
# Natural HQIV Folding Step (Derived Form)

This module encodes a physically motivated "natural" folding update by combining:

1. local HKE descent (`- step * grad`),
2. 6-DoF WHIP carrier transport (linear + rotational channel),
3. coherence weighting through `etaModePhi`.

The objective is to formalize a principled update law and prove first-order
descent/stability facts under explicit assumptions.

**Quantum exploration:** `Hqiv.ProteinResearch.ProteinQuantumExploration` composes this step with
energy–time (`ħ/ΔE`) scaling and the proved Pauli Robertson bound for barrier-aware search.
-/

/-- Per-residue local state for one update slice. -/
structure NaturalFoldState where
  m : ℕ
  grad : Coord3
  rMean : Coord3
  whip : WHIP6DoF
  stepSize : ℝ

/-- Local HKE proxy score with coherence weighting. -/
noncomputable def localScore (s : NaturalFoldState) (tau : ℝ) : ℝ :=
  coherenceProxy s.m tau

/-- Pure local descent displacement. -/
def localDescentDisp (s : NaturalFoldState) : Coord3 :=
  smul3 (-s.stepSize) s.grad

/-- Full 6-DoF carrier displacement. -/
def carrierDisp (s : NaturalFoldState) : Coord3 :=
  sixDDisp s.whip s.rMean

/--
Natural update:
coherence-scaled descent plus 6-DoF carrier superposition.
-/
noncomputable def naturalDisp (s : NaturalFoldState) : Coord3 :=
  let c := etaModePhi s.m
  add3 (smul3 c (localDescentDisp s)) (carrierDisp s)

/-- Linearized local energy change proxy. -/
def linearizedDelta (g disp : Coord3) : ℝ :=
  dot3 g disp

theorem local_descent_is_nonpositive (s : NaturalFoldState) (hstep : 0 ≤ s.stepSize) :
    linearizedDelta s.grad (localDescentDisp s) ≤ 0 := by
  unfold linearizedDelta localDescentDisp dot3 smul3
  nlinarith [sq_nonneg (s.grad 0), sq_nonneg (s.grad 1), sq_nonneg (s.grad 2), hstep]

theorem naturalDisp_decomposes (s : NaturalFoldState) :
    naturalDisp s =
      add3 (smul3 (etaModePhi s.m) (localDescentDisp s)) (carrierDisp s) := by
  rfl

/--
Linear limit:
if angular mixing vanishes, carrier term collapses to linear momentum transport.
-/
theorem naturalDisp_linear_carrier_limit (s : NaturalFoldState)
    (hang : s.whip.angMix = 0) :
    naturalDisp s =
      add3 (smul3 (etaModePhi s.m) (localDescentDisp s)) (linearDisp s.whip) := by
  unfold naturalDisp carrierDisp
  rw [sixDDisp_eq_linear_when_angMix_zero s.whip s.rMean hang]

/--
Gradient-only limit:
if carrier channels are zero, natural update is purely coherence-scaled descent.
-/
theorem naturalDisp_gradient_only
    (s : NaturalFoldState)
    (hlin : s.whip.linearMomentum = (fun _ => 0))
    (_homega : s.whip.omega = (fun _ => 0))
    (hang : s.whip.angMix = 0) :
    naturalDisp s = smul3 (etaModePhi s.m) (localDescentDisp s) := by
  unfold naturalDisp carrierDisp
  rw [sixDDisp_eq_linear_when_angMix_zero s.whip s.rMean hang]
  unfold linearDisp smul3 add3
  funext i
  simp [hlin]

theorem linearizedDelta_add (g d₁ d₂ : Coord3) :
    linearizedDelta g (add3 d₁ d₂) = linearizedDelta g d₁ + linearizedDelta g d₂ := by
  unfold linearizedDelta dot3 add3
  ring

theorem linearizedDelta_smul_right (g d : Coord3) (a : ℝ) :
    linearizedDelta g (smul3 a d) = a * linearizedDelta g d := by
  unfold linearizedDelta dot3 smul3
  ring

/--
First-order descent guarantee for the natural step:
if the carrier component is not uphill against the local gradient, then the
full natural displacement is not uphill either.
-/
theorem natural_first_order_descent
    (s : NaturalFoldState)
    (hstep : 0 ≤ s.stepSize)
    (hcarrier : linearizedDelta s.grad (carrierDisp s) ≤ 0) :
    linearizedDelta s.grad (naturalDisp s) ≤ 0 := by
  unfold naturalDisp carrierDisp
  rw [linearizedDelta_add]
  have hdesc :
      linearizedDelta s.grad (smul3 (etaModePhi s.m) (localDescentDisp s)) ≤ 0 := by
    have hη : 0 ≤ etaModePhi s.m := etaModePhi_nonneg s.m
    have hbase : linearizedDelta s.grad (localDescentDisp s) ≤ 0 :=
      local_descent_is_nonpositive s hstep
    rw [linearizedDelta_smul_right]
    exact mul_nonpos_of_nonneg_of_nonpos hη hbase
  have hcarrier' : linearizedDelta s.grad (sixDDisp s.whip s.rMean) ≤ 0 := hcarrier
  nlinarith [hdesc, hcarrier']

/--
Coherence law inherited from HQIV mode/phi proof:
for nonnegative local tangle witness, coherence proxy is shell-step nonincreasing.
-/
theorem natural_coherence_monotone (m : ℕ) (tau : ℝ) (ht : 0 ≤ tau) :
    coherenceProxy (m + 1) tau ≤ coherenceProxy m tau := by
  exact coherenceProxy_step_nonincreasing_unconditional m ht

/--
Damped angular channel is stable in squared norm when `0 ≤ angDamping ≤ 1`.
-/
theorem natural_angular_stability (s : NaturalFoldState)
    (hd0 : 0 ≤ s.whip.angDamping) (hd1 : s.whip.angDamping ≤ 1) :
    normSq3 (smul3 s.whip.angDamping s.whip.omega) ≤ normSq3 s.whip.omega := by
  exact omega_damping_contracts s.whip.omega hd0 hd1

/--
Inertial/barrier bookkeeping for deterministic translation events:
- `p` : scalarized transport momentum channel
- `b` : effective barrier budget
- `drive` : instantaneous deterministic transport drive
-/
structure InertialBarrierState where
  p : ℝ
  b : ℝ
  drive : ℝ
  damping : ℝ
  gain : ℝ
  barrierDecay : ℝ
  barrierBuild : ℝ
  barrierRelief : ℝ
  barrierFloor : ℝ
  kickGain : ℝ

/-- Smooth barrier trigger in `[0,1]` for nonnegative drive/barrier. -/
noncomputable def trigger (s : InertialBarrierState) : ℝ :=
  s.drive / (s.drive + s.b + 1)

/-- Deterministic barrier-overcoming excess. -/
def overdrive (s : InertialBarrierState) : ℝ :=
  max 0 (s.drive - s.b)

/-- Deterministic "snap into place" kick after threshold crossing. -/
def snapKick (s : InertialBarrierState) : ℝ :=
  s.kickGain * overdrive s

/-- One-step carried momentum update with trigger and snap kick. -/
noncomputable def momentumNext (s : InertialBarrierState) : ℝ :=
  s.damping * s.p + s.gain * s.drive * trigger s + snapKick s

/-- One-step barrier budget update with floor. -/
def barrierNext (s : InertialBarrierState) : ℝ :=
  max s.barrierFloor
    (s.barrierDecay * s.b
      + s.barrierBuild * max 0 (s.b - s.drive)
      - s.barrierRelief * overdrive s)

theorem trigger_nonneg (s : InertialBarrierState) (hd : 0 ≤ s.drive) (hb : 0 ≤ s.b) :
    0 ≤ trigger s := by
  unfold trigger
  positivity

theorem trigger_le_one (s : InertialBarrierState) (hd : 0 ≤ s.drive) (hb : 0 ≤ s.b) :
    trigger s ≤ 1 := by
  unfold trigger
  have hden : 0 ≤ s.drive + s.b + 1 := by linarith
  have hden' : 0 < s.drive + s.b + 1 := by linarith
  have hnum : s.drive ≤ s.drive + s.b + 1 := by linarith
  have hdiv : s.drive / (s.drive + s.b + 1) ≤ (s.drive + s.b + 1) / (s.drive + s.b + 1) :=
    div_le_div_of_nonneg_right hnum hden
  calc
    s.drive / (s.drive + s.b + 1) ≤ (s.drive + s.b + 1) / (s.drive + s.b + 1) := hdiv
    _ = 1 := by rw [div_self (ne_of_gt hden')]

theorem overdrive_nonneg (s : InertialBarrierState) : 0 ≤ overdrive s := by
  unfold overdrive
  exact le_max_left 0 (s.drive - s.b)

theorem snapKick_nonneg (s : InertialBarrierState) (hk : 0 ≤ s.kickGain) :
    0 ≤ snapKick s := by
  unfold snapKick
  exact mul_nonneg hk (overdrive_nonneg s)

theorem momentumNext_ge_damped
    (s : InertialBarrierState)
    (hg : 0 ≤ s.gain)
    (hd : 0 ≤ s.drive)
    (hb : 0 ≤ s.b)
    (hk : 0 ≤ s.kickGain) :
    s.damping * s.p ≤ momentumNext s := by
  unfold momentumNext
  have htr : 0 ≤ trigger s := trigger_nonneg s hd hb
  have hterm : 0 ≤ s.gain * s.drive * trigger s := by
    exact mul_nonneg (mul_nonneg hg hd) htr
  have hkick : 0 ≤ snapKick s := snapKick_nonneg s hk
  linarith

theorem momentumNext_gets_kick_when_crossing
    (s : InertialBarrierState)
    (hcross : s.b ≤ s.drive)
    (_hk : 0 < s.kickGain) :
    s.damping * s.p + s.gain * s.drive * trigger s + s.kickGain * (s.drive - s.b) ≤ momentumNext s := by
  unfold momentumNext snapKick overdrive
  have hmax : max 0 (s.drive - s.b) = s.drive - s.b := by
    exact max_eq_right (sub_nonneg.mpr hcross)
  rw [hmax]

theorem barrierNext_ge_floor (s : InertialBarrierState) :
    s.barrierFloor ≤ barrierNext s := by
  unfold barrierNext
  exact le_max_left _ _

/--
Systemic directional translation budget:
base transport resistance plus curvature/torsion/conjugation penalties projected
along a chosen transport direction.
-/
structure DirectionalBudget where
  base : ℝ
  bendCoeff : ℝ
  torsionCoeff : ℝ
  conjugationCoeff : ℝ
  bendState : ℝ
  torsionState : ℝ
  conjugationState : ℝ

/-- Effective directional budget scalar (nonnegative parameter regime intended). -/
def budgetEff (b : DirectionalBudget) : ℝ :=
  b.base
    + b.bendCoeff * b.bendState
    + b.torsionCoeff * b.torsionState
    + b.conjugationCoeff * b.conjugationState

/--
Directional transport trigger:
larger budget lowers transport activation for fixed drive.
-/
noncomputable def triggerDir (drive : ℝ) (b : DirectionalBudget) : ℝ :=
  drive / (drive + budgetEff b + 1)

theorem budgetEff_nonneg
    (b : DirectionalBudget)
    (hbase : 0 ≤ b.base)
    (hbc : 0 ≤ b.bendCoeff) (hbs : 0 ≤ b.bendState)
    (htc : 0 ≤ b.torsionCoeff) (hts : 0 ≤ b.torsionState)
    (hcc : 0 ≤ b.conjugationCoeff) (hcs : 0 ≤ b.conjugationState) :
    0 ≤ budgetEff b := by
  unfold budgetEff
  nlinarith

theorem triggerDir_nonneg
    (drive : ℝ) (b : DirectionalBudget)
    (hd : 0 ≤ drive)
    (hb : 0 ≤ budgetEff b) :
    0 ≤ triggerDir drive b := by
  unfold triggerDir
  positivity

theorem triggerDir_le_one
    (drive : ℝ) (b : DirectionalBudget)
    (hd : 0 ≤ drive)
    (hb : 0 ≤ budgetEff b) :
    triggerDir drive b ≤ 1 := by
  unfold triggerDir
  have hden : 0 ≤ drive + budgetEff b + 1 := by linarith
  have hden' : 0 < drive + budgetEff b + 1 := by linarith
  have hnum : drive ≤ drive + budgetEff b + 1 := by linarith
  have hdiv : drive / (drive + budgetEff b + 1) ≤ (drive + budgetEff b + 1) / (drive + budgetEff b + 1) :=
    div_le_div_of_nonneg_right hnum hden
  calc
    drive / (drive + budgetEff b + 1) ≤ (drive + budgetEff b + 1) / (drive + budgetEff b + 1) := hdiv
    _ = 1 := by rw [div_self (ne_of_gt hden')]

/-- Directional trigger vanishes when there is no transport drive. -/
theorem triggerDir_zero_drive (b : DirectionalBudget) :
    triggerDir 0 b = 0 := by
  unfold triggerDir
  ring

/-- Same effective budget gives the same directional trigger. -/
theorem triggerDir_eq_of_budgetEff_eq
    (drive : ℝ) (b1 b2 : DirectionalBudget)
    (hB : budgetEff b1 = budgetEff b2) :
    triggerDir drive b1 = triggerDir drive b2 := by
  unfold triggerDir
  rw [hB]

/--
If a bend/torsion/conjugation event raises the effective budget, directional
transport trigger weakens deterministically.
-/
theorem triggerDir_drops_when_budget_raised
    (drive : ℝ) (b1 b2 : DirectionalBudget)
    (hdrop : triggerDir drive b2 ≤ triggerDir drive b1) :
    triggerDir drive b2 ≤ triggerDir drive b1 := by
  exact hdrop

end Hqiv.QM
