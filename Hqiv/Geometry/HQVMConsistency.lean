import Hqiv.Geometry.HQVMGlobalLocalDictionary
import Hqiv.Geometry.HQVMDiscretePoisson

namespace Hqiv

open MeasureTheory Filter Real
open scoped Topology

/-!
# Homogeneous consistency (dictionary ↔ background scaffolding)

This file records the **first proved bridge statements** tying the global–local averaging layer
(`Hqiv.Geometry.HQVMGlobalLocalDictionary`) to the homogeneous HQVM background and the discrete
Poisson bookkeeping (`Hqiv.Geometry.HQVMDiscretePoisson` / `Hqiv.Geometry.HQVMCLASSBridge`). Everything
is **algebraic / limit bookkeeping** on a fixed slice: no dynamical evolution, no Boltzmann sources,
no identification of averages with a unique global FLRW state beyond what is explicitly stated.

**Extends:** `HQVMGlobalLocalDictionary` (ball means, `HQVM_CLASSHomogeneousSlice`); `HQVMDiscretePoisson`
(`HQVM_discretePoisson`, `HQVM_discretePoisson_potential`, `HQVM_discrete_singleMode_Poisson`);
`HQVMCLASSBridge` (`HQVM_lapse_perturbed`, `HQVM_lapse_background`, `HQVM_singleMode_Poisson`).

**Lemma trail:** vanishing slice potentials imply vanishing `HQVM_discretePoisson_potential` and a
trivial discrete Poisson identity with `S = 0` (`HQVM_discretePoisson_vanishing_poisson_potential`).
Volume averages of the zero field are zero (`HQVM_consistency_average_zero_field`). Scalar lapse
increments `(δΦ, δφ, δt) = 0` recover the background lapse (`HQVM_consistency_lapse_scalar_zero_increment`).
At `k = 0`, discrete and schematic single-mode Poisson agree (`HQVM_consistency_discrete_eq_schematic_at_k_zero`).
The **continuous extension** of the discrete Helmholtz symbol tends to `−k²` as `h → 0`
(`HQVM_consistency_discreteHelmholtz_tendsto_neg_k_sq`); matching the legacy `+k²` schematic is a
sign relabeling (`HQVM_consistency_neg_k_sq_amplitude_eq_source_iff_schematic_negA`).

**What is still not claimed (explicit):** Bardeen / Newtonian gauge fixing; photon polarization or
Boltzmann hierarchy; curvature weighting via `HQVM_spatial_coeff`; full 3+1 dynamical evolution or a
theorem that numerical time-stepping recovers `HQVM_Friedmann_eq`; Laplace–Beltrami identification of
the axis stencil; any CLASS file-level or array-level numerical equivalence.
-/

section VanishingPerturbations

variable {t_bg : ℝ} {δΦ δφ : ObserverChart → ℝ} {h φ : ℝ} {x : ObserverChart}

theorem HQVM_discretePoisson_potential_eq_zero_of_vanishing
    (hΦ : ∀ x, δΦ x = 0) (hφ : ∀ x, δφ x = 0) :
    HQVM_discretePoisson_potential t_bg δΦ δφ = fun _ : ObserverChart => 0 := by
  funext x
  simp [HQVM_discretePoisson_potential, hΦ, hφ]

theorem HQVM_discretePoisson_vanishing_poisson_potential (hh : h ≠ 0)
    (hΦ : ∀ x, δΦ x = 0) (hφ : ∀ x, δφ x = 0) :
    HQVM_discretePoisson h φ (HQVM_discretePoisson_potential t_bg δΦ δφ) (fun _ => 0) := by
  rw [HQVM_discretePoisson_iff_forall]
  intro x₀
  simp_rw [HQVM_discretePoisson_potential_eq_zero_of_vanishing hΦ hφ]
  exact HQVM_discretePoissonAt_const_source_zero (c := 0) hh (x := x₀)

end VanishingPerturbations

section DictionaryMeans

variable {c : ObserverChart} {R : ℝ} (hR : 0 < R)

/-- Volume average of the identically vanishing field is `0` (homogeneous “no perturbation” in the
dictionary). Extends `HQVM_volumeAverageOnObserverBall_const`. -/
theorem HQVM_consistency_average_zero_field :
    HQVM_volumeAverageOnObserverBall c R (fun _ : ObserverChart => 0)
        (integrableOn_const (μ := volume) (hs := (volume_observerBall_lt_top c R).ne)) hR = 0 := by
  simpa using HQVM_volumeAverageOnObserverBall_const c hR (0 : ℝ)

/-- A constant chart field averages to that constant (already in the dictionary; packaged here as a
consistency hook). -/
theorem HQVM_consistency_dictionary_average_const (a : ℝ) :
    HQVM_volumeAverageOnObserverBall c R (fun _ : ObserverChart => a)
        (integrableOn_const (μ := volume) (hs := (volume_observerBall_lt_top c R).ne)) hR = a :=
  HQVM_volumeAverageOnObserverBall_const c hR a

end DictionaryMeans

section LapseBackground

variable {Φ_b φ_b t : ℝ}

/-- Scalar synchronous-comoving increments vanish: perturbed lapse equals background `HQVM_lapse`.
Extends `HQVM_lapse_perturbed_eq_background_of_zero_incr` in `HQVMCLASSBridge`. -/
theorem HQVM_consistency_lapse_scalar_zero_increment :
    HQVM_lapse_perturbed Φ_b φ_b t 0 0 0 = HQVM_lapse_background Φ_b φ_b t :=
  HQVM_lapse_perturbed_eq_background_of_zero_incr Φ_b φ_b t

/-- On a `HQVM_CLASSHomogeneousSlice`, `HQVM_lapse_on_CLASSSlice` is **definitionally** the background
lapse `HQVM_lapse` at `(Phi_bg, phi_bg, t_bg)`. -/
theorem HQVM_consistency_lapse_CLASSSlice (s : HQVM_CLASSHomogeneousSlice) :
    HQVM_lapse_on_CLASSSlice s = HQVM_lapse s.Phi_bg s.phi_bg s.t_bg :=
  rfl

end LapseBackground

section SingleModeHomogeneous

variable {h k φ A B : ℝ}

theorem HQVM_discreteHelmholtz_symbol_k_zero (hh : h ≠ 0) :
    HQVM_discreteHelmholtz_symbol h 0 = 0 := by
  dsimp [HQVM_discreteHelmholtz_symbol]
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  field_simp [hh2]
  simp [mul_zero, Real.cos_zero, sub_self]

/-- Constant-in-`k` mode (`k = 0`): the discrete Helmholtz symbol vanishes, so the discrete
single-mode Poisson identity forces `B = 0` whenever `G_eff φ ≠ 0`. -/
theorem HQVM_consistency_discrete_singleMode_k_zero (hh : h ≠ 0) (hG : G_eff φ ≠ 0) :
    HQVM_discrete_singleMode_Poisson h 0 φ A B ↔ B = 0 := by
  simp only [HQVM_discrete_singleMode_Poisson, HQVM_discreteHelmholtz_symbol_k_zero hh, zero_mul]
  have h4π : 4 * Real.pi * G_eff φ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hG
  constructor
  · intro heq
    exact (mul_eq_zero.mp heq.symm).resolve_left h4π
  · intro hb
    simp [hb]

/-- At `k = 0`, discrete and schematic single-mode Poisson agree as predicates on amplitudes
(`A` drops out on the discrete side once `λ_{h,0} = 0`). Extends `HQVM_singleMode_Poisson_k0_iff`. -/
theorem HQVM_consistency_discrete_eq_schematic_at_k_zero (hh : h ≠ 0) (hG : G_eff φ ≠ 0) :
    HQVM_discrete_singleMode_Poisson h 0 φ A B ↔ HQVM_singleMode_Poisson 0 φ A B := by
  rw [HQVM_consistency_discrete_singleMode_k_zero hh hG, HQVM_singleMode_Poisson_k0_iff]
  have h4π : 4 * Real.pi * G_eff φ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hG
  constructor
  · intro hb
    simp [hb]
  · intro heq
    exact (mul_eq_zero.mp heq).resolve_left h4π

/-- Continuous extension of the discrete Helmholtz symbol tends to `−k²` as `h → 0`. -/
theorem HQVM_consistency_discreteHelmholtz_tendsto_neg_k_sq (k : ℝ) :
    Tendsto (fun h : ℝ => if h = 0 then -(k ^ 2) else HQVM_discreteHelmholtz_symbol h k) (𝓝 0)
        (𝓝 (-(k ^ 2))) :=
  tendsto_HQVM_discreteHelmholtz_symbol k

/-- The limiting multiplier `−k²` matches the schematic `HQVM_singleMode_Poisson` after flipping the
sign of the **potential** amplitude only (`A ↦ −A`). Relates continuum Laplacian sign to the legacy
`+k²` convention in `HQVMCLASSBridge`. -/
theorem HQVM_consistency_neg_k_sq_amplitude_eq_source_iff_schematic_negA :
    (-(k ^ 2)) * A = 4 * Real.pi * G_eff φ * B ↔ HQVM_singleMode_Poisson k φ (-A) B := by
  rw [show (-(k ^ 2)) * A = k ^ 2 * (-A) from by ring]
  rfl

end SingleModeHomogeneous

end Hqiv
