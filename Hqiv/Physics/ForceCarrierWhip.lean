import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Force Carrier + Inertial Whip Proxies

Theorem-first formalization of a terminus-driven translation intuition for
algorithm guidance:

- S2-inspired allowed translation envelope over normalized chain distance
- forward / back propagated amplitudes and net decomposition
- speed / kinetic / barrier-crossing proxies
- inertial whip proxy and objective-level monotonicity lemmas

All statements are constructive and use explicit real inequalities.
No new axioms are introduced.
-/

namespace Hqiv.Physics

/-- Raw normalized chain distance before clipping. -/
noncomputable def dNormRaw (n i j : Nat) : ℝ :=
  (Int.natAbs (Int.ofNat i - Int.ofNat j) : ℝ) / max (1 : ℝ) (n - 1 : ℝ)

/-- Normalized chain distance in `[0,1]` via clipping. -/
noncomputable def dNorm (n i j : Nat) : ℝ :=
  min 1 (dNormRaw n i j)

theorem dNorm_nonneg (n i j : Nat) : 0 ≤ dNorm n i j := by
  unfold dNorm
  exact le_min (by norm_num) (by
    unfold dNormRaw
    exact div_nonneg (by positivity)
      (by positivity))

theorem dNorm_le_one (n i j : Nat) : dNorm n i j ≤ 1 := by
  unfold dNorm
  exact min_le_left _ _

theorem dNorm_eq_zero_self (n i : Nat) : dNorm n i i = 0 := by
  unfold dNorm dNormRaw
  simp

/-- Integer envelope order extracted from a real tuning parameter. -/
noncomputable def envelopeOrder (p : ℝ) : Nat :=
  max 1 (Int.toNat ⌊p⌋)

theorem envelopeOrder_pos (p : ℝ) : 0 < envelopeOrder p := by
  unfold envelopeOrder
  exact Nat.succ_le_iff.mp (le_max_left 1 (Int.toNat ⌊p⌋))

/-- S2-inspired sinusoidal envelope over clipped normalized chain distance. -/
noncomputable def s2Envelope (p : ℝ) (n i j : Nat) : ℝ :=
  (Real.sin ((Real.pi / 2) * (1 - dNorm n i j))) ^ (envelopeOrder p)

theorem s2Envelope_nonneg (p : ℝ) (n i j : Nat) : 0 ≤ s2Envelope p n i j := by
  unfold s2Envelope
  apply pow_nonneg
  have hphase_nonneg : 0 ≤ (Real.pi / 2) * (1 - dNorm n i j) := by
    have h1 : 0 ≤ 1 - dNorm n i j := sub_nonneg.mpr (dNorm_le_one n i j)
    nlinarith [Real.pi_pos, h1]
  have hphase_le : (Real.pi / 2) * (1 - dNorm n i j) ≤ Real.pi := by
    have hdn : 0 ≤ dNorm n i j := dNorm_nonneg n i j
    have h1 : 1 - dNorm n i j ≤ 1 := by linarith
    have hpi2_nonneg : 0 ≤ Real.pi / 2 := by positivity
    have hm : (Real.pi / 2) * (1 - dNorm n i j) ≤ (Real.pi / 2) * 1 :=
      mul_le_mul_of_nonneg_left h1 hpi2_nonneg
    nlinarith [Real.pi_pos, hm]
  exact Real.sin_nonneg_of_nonneg_of_le_pi hphase_nonneg hphase_le

theorem s2Envelope_le_one (p : ℝ) (_hp : 0 ≤ p) (n i j : Nat) : s2Envelope p n i j ≤ 1 := by
  unfold s2Envelope
  have hsin_nonneg : 0 ≤ Real.sin ((Real.pi / 2) * (1 - dNorm n i j)) := by
    have hphase_nonneg : 0 ≤ (Real.pi / 2) * (1 - dNorm n i j) := by
      have h1 : 0 ≤ 1 - dNorm n i j := sub_nonneg.mpr (dNorm_le_one n i j)
      nlinarith [Real.pi_pos, h1]
    have hphase_le : (Real.pi / 2) * (1 - dNorm n i j) ≤ Real.pi := by
      have hdn : 0 ≤ dNorm n i j := dNorm_nonneg n i j
      have h1 : 1 - dNorm n i j ≤ 1 := by linarith
      have hpi2_nonneg : 0 ≤ Real.pi / 2 := by positivity
      have hm : (Real.pi / 2) * (1 - dNorm n i j) ≤ (Real.pi / 2) * 1 :=
        mul_le_mul_of_nonneg_left h1 hpi2_nonneg
      nlinarith [Real.pi_pos, hm]
    exact Real.sin_nonneg_of_nonneg_of_le_pi hphase_nonneg hphase_le
  have hsin_le_one : Real.sin ((Real.pi / 2) * (1 - dNorm n i j)) ≤ 1 := Real.sin_le_one _
  have hpow : (Real.sin ((Real.pi / 2) * (1 - dNorm n i j))) ^ (envelopeOrder p) ≤
      (1 : ℝ) ^ (envelopeOrder p) := by
    gcongr
  simpa using hpow

theorem s2Envelope_at_source (p : ℝ) (n src : Nat) :
    s2Envelope p n src src = 1 := by
  unfold s2Envelope
  rw [dNorm_eq_zero_self]
  simp

theorem s2Envelope_at_far_end_zero_of_dNorm_one (p : ℝ) (n i j : Nat)
    (hd : dNorm n i j = 1) :
    s2Envelope p n i j = 0 := by
  unfold s2Envelope
  rw [hd]
  have hk : envelopeOrder p ≠ 0 := Nat.ne_of_gt (envelopeOrder_pos p)
  simp [hk]

/-- Optional exponential attenuation on top of the S2 envelope. -/
noncomputable def carrierAmplitude (step span p : ℝ) (n src j : Nat) : ℝ :=
  step * Real.exp (-(dNorm n src j) / span) * s2Envelope p n src j

theorem carrierAmplitude_nonneg
    (step span p : ℝ) (n src j : Nat)
    (hstep : 0 ≤ step) (_hspan : 0 < span) (hp : 0 ≤ p) :
    0 ≤ carrierAmplitude step span p n src j := by
  unfold carrierAmplitude
  have hexp : 0 ≤ Real.exp (-(dNorm n src j) / span) := by exact le_of_lt (Real.exp_pos _)
  have hs2 : 0 ≤ s2Envelope p n src j := s2Envelope_nonneg p n src j
  have hs2' : s2Envelope p n src j ≤ 1 := s2Envelope_le_one p hp n src j
  have : 0 ≤ step * Real.exp (-(dNorm n src j) / span) := mul_nonneg hstep hexp
  exact mul_nonneg this hs2

/-- Forward propagated amplitude. -/
noncomputable def ampForward (step span p : ℝ) (n src j : Nat) : ℝ :=
  carrierAmplitude step span p n src j

/-- Back propagated amplitude (scaled by `β`, opposite-sign consumed in `ampNet`). -/
noncomputable def ampBackward (step span p β : ℝ) (n src j : Nat) : ℝ :=
  β * carrierAmplitude step span p n src j

/-- Net chain perturbation amplitude (`forward - backward`). -/
noncomputable def ampNet (step span p β : ℝ) (n src j : Nat) : ℝ :=
  ampForward step span p n src j - ampBackward step span p β n src j

theorem ampNet_decomposition (step span p β : ℝ) (n src j : Nat) :
    ampNet step span p β n src j =
      ampForward step span p n src j - ampBackward step span p β n src j := rfl

theorem ampNet_abs_le_sum (step span p β : ℝ) (n src j : Nat) :
    |ampNet step span p β n src j| ≤
      |ampForward step span p n src j| + |ampBackward step span p β n src j| := by
  unfold ampNet
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    using (abs_sub_le (ampForward step span p n src j) 0 (ampBackward step span p β n src j))

theorem ampNet_beta_zero (step span p : ℝ) (n src j : Nat) :
    ampNet step span p 0 n src j = ampForward step span p n src j := by
  unfold ampNet ampBackward
  ring

/-- Mean-speed proxy from displacement over guarded timestep denominator. -/
noncomputable def meanSpeedProxy (disp dt ε : ℝ) : ℝ :=
  |disp| / max ε dt

/-- Peak-speed proxy over forward/back amplitudes. -/
noncomputable def peakSpeedProxy (dispF dispB dt ε : ℝ) : ℝ :=
  max |dispF| |dispB| / max ε dt

/-- Kinetic proxy in quadratic speed form with guarded nonnegative mass. -/
noncomputable def kineticProxy (mEff speed : ℝ) : ℝ :=
  (max 0 mEff) * speed ^ 2 / 2

/-- Barrier-crossing speed proxy from available barrier energy and effective mass. -/
noncomputable def barrierSpeedProxy (ΔE mEff ε : ℝ) : ℝ :=
  Real.sqrt (2 * max 0 ΔE / max ε mEff)

theorem meanSpeedProxy_nonneg (disp dt ε : ℝ) (hε : 0 < ε) :
    0 ≤ meanSpeedProxy disp dt ε := by
  unfold meanSpeedProxy
  exact div_nonneg (abs_nonneg _) (by
    have : 0 < max ε dt := lt_of_lt_of_le hε (le_max_left ε dt)
    exact le_of_lt this)

theorem peakSpeedProxy_nonneg (dispF dispB dt ε : ℝ) (hε : 0 < ε) :
    0 ≤ peakSpeedProxy dispF dispB dt ε := by
  unfold peakSpeedProxy
  exact div_nonneg (by
    exact le_trans (abs_nonneg dispF) (le_max_left |dispF| |dispB|)) (by
    have : 0 < max ε dt := lt_of_lt_of_le hε (le_max_left ε dt)
    exact le_of_lt this)

theorem kineticProxy_nonneg (mEff speed : ℝ) : 0 ≤ kineticProxy mEff speed := by
  unfold kineticProxy
  exact div_nonneg (mul_nonneg (by exact le_max_left 0 mEff) (sq_nonneg speed)) (by norm_num)

theorem barrierSpeed_nonneg (ΔE mEff ε : ℝ) : 0 ≤ barrierSpeedProxy ΔE mEff ε := by
  unfold barrierSpeedProxy
  exact Real.sqrt_nonneg _

theorem barrierSpeed_mono_energy
    (ΔE₁ ΔE₂ mEff ε : ℝ) (hε : 0 < ε) (hΔ : ΔE₁ ≤ ΔE₂) :
    barrierSpeedProxy ΔE₁ mEff ε ≤ barrierSpeedProxy ΔE₂ mEff ε := by
  unfold barrierSpeedProxy
  apply Real.sqrt_le_sqrt
  have hmax : max 0 ΔE₁ ≤ max 0 ΔE₂ := max_le_max le_rfl hΔ
  have hnum : 2 * max 0 ΔE₁ ≤ 2 * max 0 ΔE₂ := by nlinarith
  have hden_nonneg : 0 ≤ max ε mEff := le_of_lt (lt_of_lt_of_le hε (le_max_left ε mEff))
  exact div_le_div_of_nonneg_right hnum hden_nonneg

theorem barrierSpeed_antitone_mass
    (ΔE m₁ m₂ ε : ℝ) (hε : 0 < ε) (_hΔ : 0 ≤ ΔE) (hm : m₁ ≤ m₂) :
    barrierSpeedProxy ΔE m₂ ε ≤ barrierSpeedProxy ΔE m₁ ε := by
  unfold barrierSpeedProxy
  apply Real.sqrt_le_sqrt
  have hnum_nonneg : 0 ≤ 2 * max 0 ΔE := by
    have : 0 ≤ max 0 ΔE := le_max_left 0 ΔE
    nlinarith
  have hden_le : max ε m₁ ≤ max ε m₂ := max_le_max le_rfl hm
  have hden1_pos : 0 < max ε m₁ := lt_of_lt_of_le hε (le_max_left ε m₁)
  have hden2_pos : 0 < max ε m₂ := lt_of_lt_of_le hε (le_max_left ε m₂)
  have hinv : (max ε m₂)⁻¹ ≤ (max ε m₁)⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hden1_pos hden_le)
  have hmul : (2 * max 0 ΔE) * (max ε m₂)⁻¹ ≤ (2 * max 0 ΔE) * (max ε m₁)⁻¹ :=
    mul_le_mul_of_nonneg_left hinv hnum_nonneg
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hmul

/-- Scalar inertial-whip proxy from coupled forward/back displacements. -/
noncomputable def whipProxy (dispF dispB : ℝ) : ℝ :=
  |dispF * dispB|

theorem whipProxy_nonneg (dispF dispB : ℝ) : 0 ≤ whipProxy dispF dispB := by
  unfold whipProxy
  exact abs_nonneg _

theorem whipProxy_zero_of_zero_displacement_left (dispB : ℝ) :
    whipProxy 0 dispB = 0 := by
  unfold whipProxy
  simp

theorem whipProxy_zero_of_zero_displacement_right (dispF : ℝ) :
    whipProxy dispF 0 = 0 := by
  unfold whipProxy
  simp

theorem whipProxy_scale_homogeneous (k dispF dispB : ℝ) :
    whipProxy (k * dispF) (k * dispB) = |k| ^ 2 * whipProxy dispF dispB := by
  unfold whipProxy
  calc
    |(k * dispF) * (k * dispB)| = |k * k * (dispF * dispB)| := by ring_nf
    _ = |k * k| * |dispF * dispB| := by rw [abs_mul]
    _ = (|k| * |k|) * |dispF * dispB| := by rw [abs_mul]
    _ = |k| ^ 2 * |dispF * dispB| := by ring
    _ = |k| ^ 2 * whipProxy dispF dispB := by rfl

/-- Optimization-facing objective skeleton (`energy - λ * whip`). -/
def objective (E lam whip : ℝ) : ℝ :=
  E - lam * whip

theorem objective_mono_whip (E lam w₁ w₂ : ℝ) (hlam : 0 ≤ lam) (hw : w₁ ≤ w₂) :
    objective E lam w₂ ≤ objective E lam w₁ := by
  unfold objective
  nlinarith

theorem objective_mono_energy (lam w E₁ E₂ : ℝ) (hE : E₁ ≤ E₂) :
    objective E₁ lam w ≤ objective E₂ lam w := by
  unfold objective
  nlinarith

theorem objective_accept_nonincreasing
    (E_new E_old lam whip_new whip_old : ℝ)
    (hlam : 0 ≤ lam) (hE : E_new ≤ E_old) (hW : whip_old ≤ whip_new) :
    objective E_new lam whip_new ≤ objective E_old lam whip_old := by
  unfold objective
  nlinarith

theorem objective_accept_strict
    (E_new E_old lam whip_new whip_old : ℝ)
    (hlam : 0 ≤ lam)
    (hE : E_new ≤ E_old)
    (hW : whip_old ≤ whip_new)
    (hStrict : E_new < E_old ∨ (whip_old < whip_new ∧ 0 < lam)) :
    objective E_new lam whip_new < objective E_old lam whip_old := by
  unfold objective
  rcases hStrict with hEstrict | hWstrict
  · nlinarith
  · rcases hWstrict with ⟨hw, hlam_pos⟩
    nlinarith

/-- Mean-speed proxy monotonicity in absolute displacement for fixed denominator. -/
theorem meanSpeedProxy_mono_abs_disp
    (disp₁ disp₂ dt ε : ℝ) (hε : 0 < ε) (habs : |disp₁| ≤ |disp₂|) :
    meanSpeedProxy disp₁ dt ε ≤ meanSpeedProxy disp₂ dt ε := by
  unfold meanSpeedProxy
  have hden_pos : 0 < max ε dt := lt_of_lt_of_le hε (le_max_left ε dt)
  exact div_le_div_of_nonneg_right habs (le_of_lt hden_pos)

/-- Substituting net amplitude into mean-speed proxy preserves monotonicity in `|ampNet|`. -/
theorem meanSpeedProxy_mono_abs_ampNet
    (step span p β : ℝ) (n src j : Nat) (dt ε : ℝ) (hε : 0 < ε)
    (A : ℝ) (hA : |ampNet step span p β n src j| ≤ |A|) :
    meanSpeedProxy (ampNet step span p β n src j) dt ε ≤ meanSpeedProxy A dt ε := by
  exact meanSpeedProxy_mono_abs_disp (ampNet step span p β n src j) A dt ε hε hA

/-- Kinetic proxy monotonicity in nonnegative speed for fixed effective mass. -/
theorem kineticProxy_mono_speed
    (mEff s₁ s₂ : ℝ) (hs₁ : 0 ≤ s₁) (hs₂ : s₁ ≤ s₂) :
    kineticProxy mEff s₁ ≤ kineticProxy mEff s₂ := by
  unfold kineticProxy
  have hm : 0 ≤ max 0 mEff := le_max_left 0 mEff
  have hsq : s₁ ^ 2 ≤ s₂ ^ 2 := by
    nlinarith [hs₁, hs₂]
  have hmul : (max 0 mEff) * s₁ ^ 2 ≤ (max 0 mEff) * s₂ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq hm
  nlinarith

/-- Kinetic proxy monotonicity in absolute displacement via mean-speed substitution. -/
theorem kineticProxy_mono_abs_disp_via_meanSpeed
    (mEff disp₁ disp₂ dt ε : ℝ) (hε : 0 < ε)
    (habs : |disp₁| ≤ |disp₂|) :
    kineticProxy mEff (meanSpeedProxy disp₁ dt ε) ≤
      kineticProxy mEff (meanSpeedProxy disp₂ dt ε) := by
  have hs_nonneg : 0 ≤ meanSpeedProxy disp₁ dt ε := meanSpeedProxy_nonneg disp₁ dt ε hε
  have hs_le : meanSpeedProxy disp₁ dt ε ≤ meanSpeedProxy disp₂ dt ε :=
    meanSpeedProxy_mono_abs_disp disp₁ disp₂ dt ε hε habs
  exact kineticProxy_mono_speed mEff (meanSpeedProxy disp₁ dt ε) (meanSpeedProxy disp₂ dt ε) hs_nonneg hs_le

/-- Kinetic proxy monotonicity for net amplitude under fixed timing guards. -/
theorem kineticProxy_mono_abs_ampNet_via_meanSpeed
    (mEff step span p β : ℝ) (n src j : Nat) (dt ε : ℝ) (hε : 0 < ε)
    (A : ℝ) (hA : |ampNet step span p β n src j| ≤ |A|) :
    kineticProxy mEff (meanSpeedProxy (ampNet step span p β n src j) dt ε) ≤
      kineticProxy mEff (meanSpeedProxy A dt ε) := by
  exact kineticProxy_mono_abs_disp_via_meanSpeed mEff (ampNet step span p β n src j) A dt ε hε hA

end Hqiv.Physics

