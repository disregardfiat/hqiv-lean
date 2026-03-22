import Hqiv.Geometry.HQVMPerturbations

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.ENNReal.BigOperators

namespace Hqiv

open MeasureTheory Set
open scoped ENNReal Topology BigOperators

/-!
# Global–local dictionary (bookkeeping stub)

This module is a **pure bookkeeping layer** for a future numerical bridge (e.g. CLASS-style output)
against the observer-centric HQVM scaffolding. It **defines** Lebesgue averaging on the same open
balls `observerBall` already introduced in `Hqiv.Geometry.HQVMPerturbations`, and records **what kinds
of global–local equivalences** would eventually be proved — **without** claiming any of them.

**Extends:** `HQVMPerturbations` (`ObserverChart`, `observerBall`, `observerDistSq`); the homogeneous
background scalars `(Φ, φ, t, a, …)` used in codes are aligned by name with `Hqiv.Geometry.HQVMetric`
(`HQVM_lapse`, `G_eff`, `H_of_phi`, `gamma_HQIV`, and `phi_of_T` via the existing import chain). The
discrete elliptic constraint in `Hqiv.Geometry.HQVMDiscretePoisson` is the natural **local** object to
average once a grid restriction and boundary conditions are fixed; no such restriction is formalized
here. The companion module `Hqiv.Geometry.HQVMConsistency` proves **homogeneous slice consistency**
(vanishing `δΦ`, `δφ` ⇒ trivial discrete Poisson with `S = 0`, ball mean of zero, lapse recovery, and
`k = 0` / `h → 0` single-mode links)—still **no** dynamical or averaging-limit identification with a
global FLRW state.

**Averaging operator (precise):** Lebesgue `volume` on `ObserverChart = (Fin 3 → ℝ)` (product
measure), restricted to `observerBall center R`. The **mean** is `(volume B)⁻¹ ∫_{B} f` as a real,
using `ENNReal.toReal` on the ball volume (finite for every fixed `R`; see `volume_observerBall_lt_top`).

**Shell alternative:** the same measure-theoretic setup yields a **spherical shell** integral / mean on
`HQVM_observerShell c R_lo R_hi := observerBall c R_hi \\ observerBall c R_lo`.

**What a genuine equivalence would require (not proved):**

1. **Lapse / FLRW bookkeeping:** patch averages of the lapse field (or of `(Φ, φ, t)` feeding
   `HQVM_lapse`) agree with a single global `(Φ_bg, φ_bg, t)` after taking a limit `R → ∞` or an
   ergodic/averaging axiom on the diamond family — plus a gauge-fixed relation between numerical lapse
   and `HQVM_lapse`.
2. **Discrete Poisson vs schematic mode:** restricting a chart field to a lattice, forming the discrete
   Laplacian (`Hqiv.Geometry.HQVMDiscreteLaplacian`), and **then** ball-averaging the Poisson
   residual should connect to `HQVM_singleMode_Poisson` / `HQVM_discrete_singleMode_Poisson` only after
   a joint `h → 0`, `R → ∞`, and harmonic-mode identification — none of which is in this file.
3. **CLASS variables:** mapping `(Φ_bg, φ_bg, a_bg, δ…)` to a code’s perturbation arrays requires an
   explicit coordinate and gauge dictionary; `HQVM_CLASSHomogeneousSlice` below is only a typed slot.

**What is still not claimed (explicit):** full Bardeen / Newtonian gauge; photon polarization or
Boltzmann hierarchy; weighting operators by `HQVM_spatial_coeff` or a Laplace–Beltrami operator on a
dynamical spatial slice; any **dynamical** theorem that averaged discrete constraints imply
`HQVM_Friedmann_eq` or `HQVM_lapse` for a global background; any CLASS file-level or array-level
equivalence.
-/

section ObserverBallMeasure

variable {c : ObserverChart} {R : ℝ}

theorem continuous_observerDistSq (y : ObserverChart) :
    Continuous fun x : ObserverChart => observerDistSq x y := by
  unfold observerDistSq
  fun_prop

theorem isOpen_observerBall (c : ObserverChart) (R : ℝ) : IsOpen (observerBall c R) := by
  rw [observerBall]
  exact (continuous_observerDistSq c).isOpen_preimage (s := Iio (R ^ 2)) isOpen_Iio

theorem measurableSet_observerBall (c : ObserverChart) (R : ℝ) :
    MeasurableSet (observerBall c R) :=
  (isOpen_observerBall c R).measurableSet

theorem volume_observerBall_pos (c : ObserverChart) {R : ℝ} (hR : 0 < R) :
    0 < volume (observerBall c R) :=
  (isOpen_observerBall c R).measure_pos volume ⟨c, observerBall_center_mem hR⟩

theorem observerBall_subset_pi_Icc_abs (c : ObserverChart) (R : ℝ) :
    observerBall c R ⊆ Set.pi univ fun i : Fin 3 => Icc (c i - |R|) (c i + |R|) := by
  intro x hx
  simp only [mem_pi, mem_univ, forall_true_left, mem_Icc, mem_setOf_eq, observerBall,
    observerDistSq] at hx ⊢
  intro i
  let ssum := (x 0 - c 0) ^ 2 + (x 1 - c 1) ^ 2 + (x 2 - c 2) ^ 2
  have hcoord : (x i - c i) ^ 2 ≤ ssum := by
    fin_cases i
    · simp [ssum]
      nlinarith [sq_nonneg (x 1 - c 1), sq_nonneg (x 2 - c 2)]
    · simp [ssum]
      nlinarith [sq_nonneg (x 0 - c 0), sq_nonneg (x 2 - c 2)]
    · simp [ssum]
      nlinarith [sq_nonneg (x 0 - c 0), sq_nonneg (x 1 - c 1)]
  have hxss : ssum < R ^ 2 := by simpa [ssum] using hx
  have hi : (x i - c i) ^ 2 < R ^ 2 := by nlinarith [hxss, hcoord]
  have habs : |x i - c i| < |R| :=
    (sq_lt_sq₀ (abs_nonneg _) (abs_nonneg _)).1 (by simpa [← sq_abs] using hi)
  rcases abs_lt.mp habs with ⟨hlo, hhi⟩
  constructor <;> linarith

theorem volume_observerBall_lt_top (c : ObserverChart) (R : ℝ) :
    volume (observerBall c R) < ⊤ := by
  let B := Set.pi (univ : Set (Fin 3)) fun i : Fin 3 => Icc (c i - |R|) (c i + |R|)
  have hB : volume B < ⊤ := by
    classical
    rw [volume_pi_pi]
    refine ENNReal.prod_lt_top ?_
    intro i _hi
    rw [Real.volume_Icc]
    ring_nf
    exact ENNReal.ofReal_lt_top
  exact lt_of_le_of_lt (measure_mono (observerBall_subset_pi_Icc_abs c R)) hB

theorem volume_observerBall_toReal_pos (c : ObserverChart) {R : ℝ} (hR : 0 < R) :
    0 < ENNReal.toReal (volume (observerBall c R)) := by
  rw [ENNReal.toReal_pos_iff]
  exact ⟨volume_observerBall_pos c hR, volume_observerBall_lt_top c R⟩

end ObserverBallMeasure

section VolumeMeanOnBall

variable {c : ObserverChart} {R : ℝ} {f g : ObserverChart → ℝ}

/-- Lebesgue integral of `f` on `observerBall c R` (chart volume). -/
noncomputable def HQVM_volumeIntegralOnObserverBall (c : ObserverChart) (R : ℝ)
    (f : ObserverChart → ℝ) : ℝ :=
  ∫ x in observerBall c R, f x

/-- Volume-normalized mean of `f` on the observer ball (requires integrability on the ball). -/
noncomputable def HQVM_volumeAverageOnObserverBall (c : ObserverChart) (R : ℝ) (f : ObserverChart → ℝ)
    (_hint : IntegrableOn f (observerBall c R) volume) (_hR : 0 < R) : ℝ :=
  (ENNReal.toReal (volume (observerBall c R)))⁻¹ * ∫ x in observerBall c R, f x

theorem HQVM_integrableOn_mul_const {s : Set ObserverChart} {f : ObserverChart → ℝ}
    (hf : IntegrableOn f s volume) (a : ℝ) :
    IntegrableOn (fun x => a * f x) s volume := by
  simpa only [Pi.smul_def, smul_eq_mul] using hf.integrable.smul a

theorem HQVM_volumeIntegralOnObserverBall_add
    (hf : IntegrableOn f (observerBall c R) volume)
    (hg : IntegrableOn g (observerBall c R) volume) :
    HQVM_volumeIntegralOnObserverBall c R (fun x => f x + g x) =
      HQVM_volumeIntegralOnObserverBall c R f + HQVM_volumeIntegralOnObserverBall c R g := by
  simp only [HQVM_volumeIntegralOnObserverBall]
  rw [integral_add hf.integrable hg.integrable]

theorem HQVM_volumeIntegralOnObserverBall_smul (a : ℝ)
    (_hf : IntegrableOn f (observerBall c R) volume) :
    HQVM_volumeIntegralOnObserverBall c R (fun x => a * f x) =
      a * HQVM_volumeIntegralOnObserverBall c R f := by
  simp only [HQVM_volumeIntegralOnObserverBall]
  simpa only [smul_eq_mul] using
    (MeasureTheory.integral_const_mul (μ := volume.restrict (observerBall c R)) a f)

theorem HQVM_volumeAverageOnObserverBall_add (hR : 0 < R)
    (hf : IntegrableOn f (observerBall c R) volume)
    (hg : IntegrableOn g (observerBall c R) volume) :
    HQVM_volumeAverageOnObserverBall c R (fun x => f x + g x) (hf.add hg) hR =
      HQVM_volumeAverageOnObserverBall c R f hf hR +
        HQVM_volumeAverageOnObserverBall c R g hg hR := by
  unfold HQVM_volumeAverageOnObserverBall
  rw [integral_add hf.integrable hg.integrable, mul_add]

theorem HQVM_volumeAverageOnObserverBall_smul (a : ℝ) (hR : 0 < R)
    (hf : IntegrableOn f (observerBall c R) volume) :
    HQVM_volumeAverageOnObserverBall c R (fun x => a * f x) (HQVM_integrableOn_mul_const hf a) hR =
      a * HQVM_volumeAverageOnObserverBall c R f hf hR := by
  unfold HQVM_volumeAverageOnObserverBall
  rw [MeasureTheory.integral_const_mul (μ := volume.restrict (observerBall c R)) a f]
  ring

theorem HQVM_volumeAverageOnObserverBall_const (c : ObserverChart) (hR : 0 < R) (a : ℝ) :
    HQVM_volumeAverageOnObserverBall c R (fun _ => a)
        (integrableOn_const (μ := volume) (hs := (volume_observerBall_lt_top c R).ne)) hR = a := by
  unfold HQVM_volumeAverageOnObserverBall
  have hv := volume_observerBall_toReal_pos c hR
  simp only [setIntegral_const, measureReal_def, smul_eq_mul]
  field_simp [hv.ne']

end VolumeMeanOnBall

section ShellMean

variable {c : ObserverChart} {R_lo R_hi : ℝ} {f : ObserverChart → ℝ}

/-- Open spherical shell between squared-radius thresholds `R_lo²` and `R_hi²` in `observerDistSq`. -/
def HQVM_observerShell (c : ObserverChart) (R_lo R_hi : ℝ) : Set ObserverChart :=
  observerBall c R_hi \ observerBall c R_lo

theorem measurableSet_HQVM_observerShell (c : ObserverChart) (R_lo R_hi : ℝ) :
    MeasurableSet (HQVM_observerShell c R_lo R_hi) :=
  (measurableSet_observerBall c R_hi).diff (measurableSet_observerBall c R_lo)

theorem HQVM_observerShell_subset_ball (c : ObserverChart) (R_lo R_hi : ℝ) :
    HQVM_observerShell c R_lo R_hi ⊆ observerBall c R_hi :=
  diff_subset

theorem volume_HQVM_observerShell_lt_top (c : ObserverChart) (R_lo R_hi : ℝ) :
    volume (HQVM_observerShell c R_lo R_hi) < ⊤ :=
  lt_of_le_of_lt (measure_mono (HQVM_observerShell_subset_ball c R_lo R_hi))
    (volume_observerBall_lt_top c R_hi)

/-- Lebesgue integral on a spherical shell (same chart volume). -/
noncomputable def HQVM_volumeIntegralOnObserverShell (c : ObserverChart) (R_lo R_hi : ℝ)
    (f : ObserverChart → ℝ) : ℝ :=
  ∫ x in HQVM_observerShell c R_lo R_hi, f x

/-- Volume-normalized shell mean (requires integrability and positive shell volume). -/
noncomputable def HQVM_volumeAverageOnObserverShell (c : ObserverChart) (R_lo R_hi : ℝ)
    (f : ObserverChart → ℝ) (_hint : IntegrableOn f (HQVM_observerShell c R_lo R_hi) volume)
    (_hvol : 0 < volume (HQVM_observerShell c R_lo R_hi)) : ℝ :=
  (ENNReal.toReal (volume (HQVM_observerShell c R_lo R_hi)))⁻¹ *
    ∫ x in HQVM_observerShell c R_lo R_hi, f x

theorem volume_HQVM_observerShell_toReal_pos (c : ObserverChart) (R_lo R_hi : ℝ)
    (hvol : 0 < volume (HQVM_observerShell c R_lo R_hi)) :
    0 < ENNReal.toReal (volume (HQVM_observerShell c R_lo R_hi)) := by
  rw [ENNReal.toReal_pos_iff]
  exact ⟨hvol, volume_HQVM_observerShell_lt_top c R_lo R_hi⟩

theorem HQVM_volumeAverageOnObserverShell_const (c : ObserverChart) (R_lo R_hi : ℝ) (a : ℝ)
    (hvol : 0 < volume (HQVM_observerShell c R_lo R_hi)) :
    HQVM_volumeAverageOnObserverShell c R_lo R_hi (fun _ => a)
        (integrableOn_const (μ := volume) (hs := (volume_HQVM_observerShell_lt_top c R_lo R_hi).ne))
        hvol = a := by
  unfold HQVM_volumeAverageOnObserverShell
  have hv := volume_HQVM_observerShell_toReal_pos c R_lo R_hi hvol
  simp only [setIntegral_const, measureReal_def, smul_eq_mul]
  field_simp [hv.ne']

end ShellMean

section FinitePatchFamily

variable {ι : Type*} [Fintype ι]

/-- Arithmetic mean of ball volume-averages over a finite family of `(center, R)` patches. -/
noncomputable def HQVM_globalMean_volumeBallAverages (patch : ι → ObserverChart × ℝ)
    (f : ObserverChart → ℝ)
    (hint : ∀ i, IntegrableOn f (observerBall (patch i).1 (patch i).2) volume)
    (hR : ∀ i, 0 < (patch i).2) : ℝ :=
  (Fintype.card ι : ℝ)⁻¹ *
    ∑ i, HQVM_volumeAverageOnObserverBall (patch i).1 (patch i).2 f (hint i) (hR i)

theorem HQVM_globalMean_volumeBallAverages_eq_const [Nonempty ι] (patch : ι → ObserverChart × ℝ)
    (f : ObserverChart → ℝ)
    (hint : ∀ i, IntegrableOn f (observerBall (patch i).1 (patch i).2) volume)
    (hR : ∀ i, 0 < (patch i).2) (v : ℝ)
    (h : ∀ i, HQVM_volumeAverageOnObserverBall (patch i).1 (patch i).2 f (hint i) (hR i) = v) :
    HQVM_globalMean_volumeBallAverages patch f hint hR = v := by
  classical
  unfold HQVM_globalMean_volumeBallAverages
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  have hne : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hcard.ne'
  field_simp [hne]

end FinitePatchFamily

section CLASSSliceHook

/-- Typed slots for a homogeneous background slice (names aligned with `HQVMetric`; no CLASS array map). -/
structure HQVM_CLASSHomogeneousSlice where
  /-- ADM lapse potential `Φ` in `HQVM_lapse`. -/
  Phi_bg : ℝ
  /-- Expansion proxy `φ` in `HQVM_lapse` / `H_of_phi`. -/
  phi_bg : ℝ
  /-- Coordinate time on the slice. -/
  t_bg : ℝ
  /-- Scale-factor placeholder (FLRW / CLASS `a` analog). -/
  a_bg : ℝ

/-- Lapse on the slice using `HQVM_lapse` from `HQVMetric` (definitional hook only). -/
noncomputable def HQVM_lapse_on_CLASSSlice (s : HQVM_CLASSHomogeneousSlice) : ℝ :=
  HQVM_lapse s.Phi_bg s.phi_bg s.t_bg

end CLASSSliceHook

end Hqiv
