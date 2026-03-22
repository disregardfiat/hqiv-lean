import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Logic.Function.Iterate
import Mathlib.Topology.Order.MonotoneConvergence

import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.HQVMPerturbations
import Hqiv.Physics.Action

namespace Hqiv

open Filter Set Topology

/-!
# HQVM ↔ CLASS-oriented linearized metric scaffolding (background + first-order piece)

This module is **not** a formalization of CLASS file-level equivalence, the full linearized Einstein
equations, Bardeen / Newtonian gauge transformations, photon polarization hierarchies, or Boltzmann
collision sources. It records a **synchronous-comoving** ansatz consistent with `HQVMetric`
(shift zero, `N = HQVM_lapse`, spatial coefficient `HQVM_spatial_coeff`) and packages the **exact**
finite increments into **background + linearized + remainder** form so a future numerical patch has a
clear Lean target.

**CLASS homogeneous background (proved algebra):** `section CLASSBackgroundMethodology` shows that
`HQVM_Friedmann_eq` is equivalent to the **code-style** identity
`H² = (3/(3−γ)) G_eff(H) ρ_crit` once **`ρ_crit = 8πρ/3`** at **`G = 1`** (`HQVM_CLASS_rhoCrit`), and
that for **`H ≥ 0`** this is equivalent to **`H` being a fixed point of the Picard square-root map**
(`HQVM_CLASS_picardStep`). `section PicardConvergence` proves **continuity** and **monotonicity** of
that map (given **`Monotone G_eff`**), **vacuum uniqueness** and **convergence** at **`ρ_crit = 0`**,
and the **monotone `cSup` / `tendsto_atTop_ciSup`** route to a **fixed point** when iterates are
nondecreasing and **bounded above**. `section ConformalHPrime` differentiates the modified Friedmann
identity along conformal time (`deriv` / `H′`) and solves for **`deriv H`** when the Bernstein
denominator is nonzero — the CLASS homogeneous **derivative** target.

**What is claimed:** algebraic decomposition of lapse and spatial conformal factor; subtraction of two
instances of `HQVM_Friedmann_eq`; a schematic single-`k` Poisson **definition** with solvability at
`k ≠ 0`.

**What is not claimed:** derivation of the Poisson equation from `HQVM_Friedmann_eq` or from a
3+1 Einstein constraint; matching of variables to any particular CLASS `perturbs` array layout.

**Spatial stencil (separate modules):** `Hqiv.Geometry.HQVMDiscreteLaplacian` defines an axis-aligned
second-difference operator on the same `ObserverChart` as `Hqiv.Geometry.HQVMPerturbations`;
`Hqiv.Geometry.HQVMDiscretePoisson` applies it in a pointwise Poisson constraint and relates the
`HQVM_cosModeOnAxis` eigen-coefficient to the schematic `HQVM_singleMode_Poisson` (same bilinear shape,
discrete Helmholtz symbol; sign/limit discussion in that file). No CLASS-level identification is
asserted here.

**What can be added from existing formalization (this file):** `Hqiv.Physics.Action` already defines
`S_HQVM_grav` with `S_HQVM_grav_zero_iff_Friedmann`. The difference `S_grav(φ₁) − S_grav(φ₂)` is a pure
polynomial in `(φ₁, φ₂, ρ)` and matches the same subtraction algebra as `HQVM_Friedmann_eq_difference`
(after the usual `3` vs `3.0` numeral alignment). This still does **not** produce spatial Poisson or
gauge-fixed Einstein constraints — only the homogeneous φ-channel residual already in the action.
-/

section BackgroundVsPerturbation

/-!
### Notation (bookkeeping only)

We write background values `Φ_b`, `φ_b`, `t`, `a_b` and first-order increments `δΦ`, `δφ`, `δt`,
`δa` **additively** on a single spatial slice / trajectory (no `Fin 3 → ℝ` dependence yet). This is
the same convention as `HQVM_lapse_increment_eq` / `HQVM_lapse_increment_homogeneous` in
`HQVMPerturbations`: the **only** nonlinear lapse remainder in `(δΦ, δφ, δt)` is `δφ * δt`.
-/

/-- Background lapse on the HQVM branch: same functional form as `HQVM_lapse`, arguments are
interpreted as `(Φ_b, φ_b, t)`. -/
abbrev HQVM_lapse_background (Φ_b φ_b t : ℝ) : ℝ :=
  HQVM_lapse Φ_b φ_b t

/-- Perturbed lapse after adding `(δΦ, δφ, δt)` to `(Φ_b, φ_b, t)` (synchronous-comoving ansatz). -/
def HQVM_lapse_perturbed (Φ_b φ_b t δΦ δφ δt : ℝ) : ℝ :=
  HQVM_lapse (Φ_b + δΦ) (φ_b + δφ) (t + δt)

/-- **Exact lapse increment** equals `linearizedHQVM_lapse` plus the bilinear remainder `δφ * δt`. -/
theorem HQVM_lapse_perturbed_sub_background (Φ_b φ_b t δΦ δφ δt : ℝ) :
    HQVM_lapse_perturbed Φ_b φ_b t δΦ δφ δt - HQVM_lapse_background Φ_b φ_b t =
      linearizedHQVM_lapse φ_b t δΦ δφ δt + δφ * δt :=
  HQVM_lapse_increment_eq Φ_b φ_b t δΦ δφ δt

/-!
### Homogeneous / `k = 0` slice (lapse channel)

On `Φ_b = 0`, `φ_b = H`, this is exactly `HQVM_lapse_increment_homogeneous`: the first-order piece is
`linearizedHQVM_lapse H t δΦ δφ δt`. Vanishing **linearized** lapse increment is the linearized
constraint `δΦ + H δt + t δφ = 0`.
-/

theorem HQVM_lapse_perturbed_sub_background_homogeneous (H t δΦ δφ δt : ℝ) :
    HQVM_lapse_perturbed 0 H t δΦ δφ δt - HQVM_lapse_background 0 H t =
      linearizedHQVM_lapse H t δΦ δφ δt + δφ * δt := by
  unfold HQVM_lapse_perturbed HQVM_lapse_background
  simpa [zero_add] using HQVM_lapse_increment_eq 0 H t δΦ δφ δt

/-- Linearized lapse increment vanishes iff `δΦ + φ_b δt + t δφ = 0` (pure algebra). -/
theorem linearizedHQVM_lapse_eq_zero_iff (φ_b t δΦ δφ δt : ℝ) :
    linearizedHQVM_lapse φ_b t δΦ δφ δt = 0 ↔ δΦ + φ_b * δt + t * δφ = 0 := by
  unfold linearizedHQVM_lapse
  rfl

/-- **`k = 0` / homogeneous lapse channel:** if all increments vanish, the perturbed lapse equals the
background lapse (no remainder). Connects the linearized bookkeeping to `HQVM_lapse` on the
background point. -/
theorem HQVM_lapse_perturbed_eq_background_of_zero_incr (Φ_b φ_b t : ℝ) :
    HQVM_lapse_perturbed Φ_b φ_b t 0 0 0 = HQVM_lapse_background Φ_b φ_b t := by
  simp [HQVM_lapse_perturbed, HQVM_lapse_background]

end BackgroundVsPerturbation

section SpatialLinearization

/-!
### Spatial coefficient `a²(1 - 2Φ)` at first order

The HQVM spatial diagonal coefficient is `HQVM_spatial_coeff a Φ = a²(1 - 2Φ)`. Expanding
`(a_b + δa, Φ_b + δΦ)` gives an explicit linear part and a polynomial remainder quadratic/cubic in
`(δa, δΦ)` — no curvature tensors, only the ADM coefficient already fixed in `HQVMetric`.
-/

/-- First-order change in `HQVM_spatial_coeff a Φ` in `(δa, δΦ)` at `(a, Φ)`. -/
def linearizedHQVM_spatial_coeff (a Φ δa δΦ : ℝ) : ℝ :=
  2 * a * δa * (1 - 2 * Φ) - 2 * a ^ 2 * δΦ

/-- Exact increment of the spatial coefficient as linear part plus the **exact** quadratic remainder
`(full increment) − linearizedHQVM_spatial_coeff` (identity closed by `ring`). -/
theorem HQVM_spatial_coeff_increment_eq (a Φ δa δΦ : ℝ) :
    HQVM_spatial_coeff (a + δa) (Φ + δΦ) - HQVM_spatial_coeff a Φ =
      linearizedHQVM_spatial_coeff a Φ δa δΦ +
        (HQVM_spatial_coeff (a + δa) (Φ + δΦ) - HQVM_spatial_coeff a Φ -
          linearizedHQVM_spatial_coeff a Φ δa δΦ) := by
  ring

/-- Homogeneous Newtonian background `Φ_b = 0`: linearized spatial coefficient is `2 a_b δa - 2 a_b² δΦ`. -/
theorem linearizedHQVM_spatial_coeff_homogeneous (a_b δa δΦ : ℝ) :
    linearizedHQVM_spatial_coeff a_b 0 δa δΦ = 2 * a_b * δa - 2 * a_b ^ 2 * δΦ := by
  unfold linearizedHQVM_spatial_coeff
  ring

/-- **`k = 0` spatial channel:** vanishing `(δa, δΦ)` leaves the spatial coefficient unchanged
(connects perturbation ansatz to the background `HQVM_spatial_coeff`). -/
theorem HQVM_spatial_coeff_perturbed_eq_background_of_zero_incr (a_b Φ_b : ℝ) :
    HQVM_spatial_coeff (a_b + 0) (Φ_b + 0) = HQVM_spatial_coeff a_b Φ_b := by simp

end SpatialLinearization

section FriedmannBridge

/-!
### Difference of two Friedmann equalities (homogeneous `φ` channel)

`HQVM_Friedmann_eq` is stated in `HQVMetric` for a single `φ`. Comparing two values `φ₁` and `φ₂` at
the **same** `(ρ_m, ρ_r)` subtracts the Friedmann identity to an **exact** relation between
`(φ₁² - φ₂²)` and `(G_eff φ₁ - G_eff φ₂)`. We spell numerals as `3.0` / `8.0` to match
`HQVM_Friedmann_eq_def` verbatim. Specializing `φ₁ = φ + δφ`, `φ₂ = φ` packages the finite-`δφ`
increment used in fluid linearization — still **not** a proof that a particular `δφ` arises from
`δρ` via Boltzmann.
-/

/-- Subtract two instances of the Friedmann equation at the same densities (same numerals as
`HQVM_Friedmann_eq_def`). -/
theorem HQVM_Friedmann_eq_difference (φ₁ φ₂ rho_m rho_r : ℝ)
    (h₁ : HQVM_Friedmann_eq φ₁ rho_m rho_r) (h₂ : HQVM_Friedmann_eq φ₂ rho_m rho_r) :
    (3.0 - gamma_HQIV) * (φ₁ ^ 2 - φ₂ ^ 2) =
      8.0 * Real.pi * (G_eff φ₁ - G_eff φ₂) * rho_total rho_m rho_r := by
  simp only [HQVM_Friedmann_eq_def, H_of_phi_eq, rho_total_eq] at h₁ h₂
  rw [rho_total_eq]
  rw [mul_sub]
  rw [h₁, h₂]
  simp [mul_sub, sub_mul, mul_left_comm, mul_comm]

/-- Finite `δφ` increment between `φ` and `φ + δφ` at fixed `(ρ_m, ρ_r)`. -/
theorem HQVM_Friedmann_eq_difference_phi_plus (φ δφ rho_m rho_r : ℝ)
    (hbg : HQVM_Friedmann_eq φ rho_m rho_r) (hpert : HQVM_Friedmann_eq (φ + δφ) rho_m rho_r) :
    (3.0 - gamma_HQIV) * (2 * φ * δφ + δφ ^ 2) =
      8.0 * Real.pi * (G_eff (φ + δφ) - G_eff φ) * rho_total rho_m rho_r := by
  have hmul :
      (φ + δφ) * (φ + δφ) = φ * φ + 2 * φ * δφ + δφ * δφ := by
    rw [← pow_two (φ + δφ), add_sq φ δφ]
    simp [pow_two]
  have hsq :
      (φ + δφ) ^ 2 - φ ^ 2 = 2 * φ * δφ + δφ ^ 2 := by
    simp only [pow_two]
    rw [hmul, add_assoc (φ * φ) (2 * φ * δφ) (δφ * δφ), add_sub_cancel_left]
  have h := HQVM_Friedmann_eq_difference (φ + δφ) φ rho_m rho_r hpert hbg
  simpa [← hsq, mul_sub] using h

end FriedmannBridge

section ConformalHPrime

/-!
### Conformal-time derivative `H′ = dH/dτ` (CLASS prime)

In the homogeneous HQVM limit, `φ = H` (`H_of_phi_eq`). Differentiating the modified Friedmann identity
`(3−γ) H² = 8π G_eff(H) ρ_tot` from `HQVM_Friedmann_eq_rational` / `HQVM_Friedmann_eq_power` along
conformal time `τ` gives a **linear** relation between `H′ := deriv H τ`, `ρ_tot′ := deriv ρ_tot`,
and `deriv G_eff (H τ)` (chain rule on `G_eff(H(τ))`). With `three_minus_gamma_eq`, the coefficient
`2 * (3−γ)` is **`2 * (13/5)`** on `ℝ`. This matches what a CLASS-style homogeneous **derivative**
routine must implement when `G_eff` depends on `H` and total density is carried as a smooth function
of `τ`.

**Hypothesis note:** `Filter.EventuallyEq.deriv_eq` requires the Friedmann **equality of functions**
`(3−γ) H(·)² = 8π G_eff(H(·)) ρ_tot(·)` on a **neighborhood** of `τ`. The pointwise proposition
`HQVM_Friedmann_eq (H τ) …` at one instant alone does **not** determine derivatives.
-/

/-- Total density as a function of conformal time, `ρ_tot(τ) = ρ_m(τ) + ρ_r(τ)`. -/
noncomputable abbrev HQVM_rho_total_fun (rho_m rho_r : ℝ → ℝ) : ℝ → ℝ := fun t =>
  rho_total (rho_m t) (rho_r t)

theorem HQVM_deriv_rho_total_fun (rho_m rho_r : ℝ → ℝ) (τ : ℝ) (hm : DifferentiableAt ℝ rho_m τ)
    (hr : DifferentiableAt ℝ rho_r τ) :
    deriv (HQVM_rho_total_fun rho_m rho_r) τ = deriv rho_m τ + deriv rho_r τ := by
  change deriv (fun t => rho_m t + rho_r t) τ = deriv rho_m τ + deriv rho_r τ
  exact deriv_add hm hr

/-- Numeral alignment between `HQVM_Friedmann_eq` (`3.0` / `8.0`) and the `deriv`-friendly spelling. -/
theorem HQVM_Friedmann_pointwise_eq_three_eight (H rho_m rho_r : ℝ) :
    (3.0 - gamma_HQIV) * H ^ 2 = 8.0 * Real.pi * G_eff H * rho_total rho_m rho_r ↔
      (3 - gamma_HQIV) * H ^ 2 = 8 * Real.pi * G_eff H * rho_total rho_m rho_r := by
  have h3 : (3.0 : ℝ) = (3 : ℝ) := by norm_num
  have h8 : (8.0 : ℝ) = (8 : ℝ) := by norm_num
  have hgam : (3.0 : ℝ) - gamma_HQIV = (3 : ℝ) - gamma_HQIV := by rw [h3]
  have h8pi : (8.0 : ℝ) * Real.pi = (8 : ℝ) * Real.pi := by rw [h8]
  constructor
  · intro h
    rw [hgam, h8pi] at h
    simpa [mul_assoc, mul_left_comm, mul_comm] using h
  · intro h
    simpa [← hgam, ← h8pi, mul_assoc, mul_left_comm, mul_comm] using h

theorem HQVM_Friedmann_fun_eventuallyEq_three_eight (H rho_m rho_r : ℝ → ℝ) (τ : ℝ)
    (h : ∀ᶠ t in 𝓝 τ, HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t)) :
    (fun t => (3 - gamma_HQIV) * (H t) ^ 2) =ᶠ[𝓝 τ] fun t =>
        8 * Real.pi * G_eff (H t) * rho_total (rho_m t) (rho_r t) := by
  filter_upwards [h] with t ht
  rw [← (HQVM_Friedmann_pointwise_eq_three_eight (H t) (rho_m t) (rho_r t)).1]
  simpa [HQVM_Friedmann_eq_def, H_of_phi_eq] using ht

/-- Differentiated modified Friedmann in conformal time (chain rule + product rule). -/
theorem HQVM_conformal_H_prime_eq {H rho_m rho_r : ℝ → ℝ} {τ : ℝ}
    (hF : ∀ᶠ t in 𝓝 τ, HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t))
    (hH : DifferentiableAt ℝ H τ) (hm : DifferentiableAt ℝ rho_m τ) (hr : DifferentiableAt ℝ rho_r τ)
    (hG : DifferentiableAt ℝ G_eff (H τ)) :
    2 * (3 - gamma_HQIV) * H τ * deriv H τ =
      8 * Real.pi *
        (deriv G_eff (H τ) * deriv H τ * rho_total (rho_m τ) (rho_r τ) +
          G_eff (H τ) * deriv (HQVM_rho_total_fun rho_m rho_r) τ) := by
  let lhs : ℝ → ℝ := fun t => (3 - gamma_HQIV) * (H t) ^ 2
  let rhs : ℝ → ℝ := fun t => 8 * Real.pi * G_eff (H t) * rho_total (rho_m t) (rho_r t)
  have hev : lhs =ᶠ[𝓝 τ] rhs := by
    simpa [lhs, rhs] using HQVM_Friedmann_fun_eventuallyEq_three_eight H rho_m rho_r τ hF
  have hderiv : deriv lhs τ = deriv rhs τ := hev.deriv_eq
  have h2 : deriv (fun t => (H t) ^ 2) τ = 2 * H τ * deriv H τ := by
    simpa [pow_two, Nat.cast_ofNat, mul_assoc, mul_left_comm, mul_comm] using
      (deriv_fun_pow (f := H) (n := 2) hH)
  have hHsq : DifferentiableAt ℝ (fun t => (H t) ^ 2) τ := hH.pow 2
  have hdlhs : deriv lhs τ = 2 * (3 - gamma_HQIV) * H τ * deriv H τ := by
    dsimp only [lhs]
    rw [deriv_const_mul_field (3 - gamma_HQIV), h2]
    ring
  have hGH : DifferentiableAt ℝ (fun t => G_eff (H t)) τ := by
    simpa [Function.comp_def] using (DifferentiableAt.comp (f := H) (x := τ) hG hH)
  have hρ : DifferentiableAt ℝ (HQVM_rho_total_fun rho_m rho_r) τ := by
    simpa [HQVM_rho_total_fun, rho_total_eq] using hm.add hr
  have hdrhs :
      deriv rhs τ =
        8 * Real.pi *
          (deriv G_eff (H τ) * deriv H τ * rho_total (rho_m τ) (rho_r τ) +
            G_eff (H τ) * deriv (HQVM_rho_total_fun rho_m rho_r) τ) := by
    have hp :
        deriv (fun t => G_eff (H t) * HQVM_rho_total_fun rho_m rho_r t) τ =
          deriv (fun t => G_eff (H t)) τ * HQVM_rho_total_fun rho_m rho_r τ +
            G_eff (H τ) * deriv (HQVM_rho_total_fun rho_m rho_r) τ :=
      deriv_mul hGH hρ
    have hcomp : deriv (fun t => G_eff (H t)) τ = deriv G_eff (H τ) * deriv H τ := by
      simpa [Function.comp_def] using deriv_comp τ hG hH
    have hrw :
        rhs =
          fun t =>
            (8 * Real.pi) * (G_eff (H t) * rho_total (rho_m t) (rho_r t)) := by
      funext t
      simp [rhs, mul_assoc, mul_left_comm, mul_comm]
    rw [hrw, deriv_const_mul_field (8 * Real.pi), hp, hcomp]
  simpa [hdlhs, hdrhs] using hderiv

/-- Same conclusion with `ρ_tot′` written as `deriv ρ_m + deriv ρ_r`. -/
theorem HQVM_conformal_H_prime_eq' {H rho_m rho_r : ℝ → ℝ} {τ : ℝ}
    (hF : ∀ᶠ t in 𝓝 τ, HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t))
    (hH : DifferentiableAt ℝ H τ) (hm : DifferentiableAt ℝ rho_m τ) (hr : DifferentiableAt ℝ rho_r τ)
    (hG : DifferentiableAt ℝ G_eff (H τ)) :
    2 * (3 - gamma_HQIV) * H τ * deriv H τ =
      8 * Real.pi *
        (deriv G_eff (H τ) * deriv H τ * rho_total (rho_m τ) (rho_r τ) +
          G_eff (H τ) * (deriv rho_m τ + deriv rho_r τ)) := by
  simpa [HQVM_deriv_rho_total_fun rho_m rho_r τ hm hr] using HQVM_conformal_H_prime_eq hF hH hm hr hG

/-- Pointwise Friedmann at `τ` follows from the neighborhood hypothesis in `HQVM_conformal_H_prime_eq`. -/
theorem HQVM_Friedmann_at_of_eventually {H rho_m rho_r : ℝ → ℝ} {τ : ℝ}
    (hF : ∀ᶠ t in 𝓝 τ, HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t)) :
    HQVM_Friedmann_eq (H τ) (rho_m τ) (rho_r τ) := by
  have hmem : {t : ℝ | HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t)} ∈ 𝓝 τ := eventually_iff.1 hF
  have hτ : τ ∈ {t : ℝ | HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t)} := mem_of_mem_nhds hmem
  simpa using hτ

/-- Rearranged form: bracketed coefficient times `H′`. -/
theorem HQVM_conformal_H_prime_eq_factor_H' {H rho_m rho_r : ℝ → ℝ} {τ : ℝ}
    (hF : ∀ᶠ t in 𝓝 τ, HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t))
    (hH : DifferentiableAt ℝ H τ) (hm : DifferentiableAt ℝ rho_m τ) (hr : DifferentiableAt ℝ rho_r τ)
    (hG : DifferentiableAt ℝ G_eff (H τ)) :
    (2 * (3 - gamma_HQIV) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ)) *
        deriv H τ =
      8 * Real.pi * G_eff (H τ) * deriv (HQVM_rho_total_fun rho_m rho_r) τ := by
  have h := HQVM_conformal_H_prime_eq hF hH hm hr hG
  calc
    (2 * (3 - gamma_HQIV) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ)) *
          deriv H τ
        = 2 * (3 - gamma_HQIV) * H τ * deriv H τ -
            8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ) * deriv H τ := by
          ring
    _ = 8 * Real.pi * G_eff (H τ) * deriv (HQVM_rho_total_fun rho_m rho_r) τ := by
          rw [h]
          ring

/-- Denominator in the solved `H′` formula, with `(3−γ) = 13/5` from `three_minus_gamma_eq`. -/
theorem HQVM_conformal_H_prime_denominator_eq (H : ℝ) (rho_m rho_r : ℝ)
    (_hG : DifferentiableAt ℝ G_eff H) :
    2 * (3 - gamma_HQIV) * H - 8 * Real.pi * deriv G_eff H * rho_total rho_m rho_r =
      2 * (13 / 5 : ℝ) * H - 8 * Real.pi * deriv G_eff H * rho_total rho_m rho_r := by
  simp_rw [← three_minus_gamma_eq]

/-- Explicit `H′` when the Bernstein denominator is nonzero. -/
theorem HQVM_conformal_deriv_H_eq_div {H rho_m rho_r : ℝ → ℝ} {τ : ℝ}
    (hF : ∀ᶠ t in 𝓝 τ, HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t))
    (hH : DifferentiableAt ℝ H τ) (hm : DifferentiableAt ℝ rho_m τ) (hr : DifferentiableAt ℝ rho_r τ)
    (hG : DifferentiableAt ℝ G_eff (H τ))
    (hden :
      2 * (3 - gamma_HQIV) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ) ≠
        0) :
    deriv H τ =
      (8 * Real.pi * G_eff (H τ) * deriv (HQVM_rho_total_fun rho_m rho_r) τ) /
        (2 * (3 - gamma_HQIV) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ)) := by
  have hmul := HQVM_conformal_H_prime_eq_factor_H' hF hH hm hr hG
  field_simp [hden]
  linarith [hmul]

/-- Same solved `H′` with denominator written using **`13/5`** instead of `(3−γ)`. -/
theorem HQVM_conformal_deriv_H_eq_div_rational {H rho_m rho_r : ℝ → ℝ} {τ : ℝ}
    (hF : ∀ᶠ t in 𝓝 τ, HQVM_Friedmann_eq (H t) (rho_m t) (rho_r t))
    (hH : DifferentiableAt ℝ H τ) (hm : DifferentiableAt ℝ rho_m τ) (hr : DifferentiableAt ℝ rho_r τ)
    (hG : DifferentiableAt ℝ G_eff (H τ))
    (hden :
      2 * (13 / 5 : ℝ) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ) ≠
        0) :
    deriv H τ =
      (8 * Real.pi * G_eff (H τ) * deriv (HQVM_rho_total_fun rho_m rho_r) τ) /
        (2 * (13 / 5 : ℝ) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ)) := by
  have hden' :
      2 * (3 - gamma_HQIV) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ) ≠
        0 := by
    intro hL
    apply hden
    have hEq := HQVM_conformal_H_prime_denominator_eq (H τ) (rho_m τ) (rho_r τ) hG
    have h0 :
        (2 * (13 / 5 : ℝ) * H τ - 8 * Real.pi * deriv G_eff (H τ) * rho_total (rho_m τ) (rho_r τ)) = 0 := by
      linarith [hEq, hL]
    exact h0
  have hmain := HQVM_conformal_deriv_H_eq_div hF hH hm hr hG hden'
  simpa [HQVM_conformal_H_prime_denominator_eq (H τ) (rho_m τ) (rho_r τ) hG] using hmain

end ConformalHPrime

section CLASSBackgroundMethodology

/-!
### Density convention and `H²` rescaling (matches `class_hqiv/background.c` algebra)

Flat FRW at **`G = 1` (natural units):** **`3H² = 8πρ`**. CLASS stores **`H² = ρ_crit`** with the same
normalization, so **`ρ_crit = 8πρ/3`**. HQIV replaces the **`3`** coefficient on **`H²`** by **`(3−γ)`**
and **`G`** by **`G_eff(H)`**, yielding the proved equivalence below.
-/

/-- **CLASS critical density factor** at `G = 1`: `ρ_crit = 8π ρ / 3` so that `H² = ρ_crit` ↔ `3H² = 8πρ`. -/
noncomputable def HQVM_CLASS_rhoCrit (rho : ℝ) : ℝ :=
  8 * Real.pi * rho / 3

theorem HQVM_CLASS_rhoCrit_eq (rho : ℝ) :
    HQVM_CLASS_rhoCrit rho = 8 * Real.pi * rho / 3 := rfl

/-- Standard flat GR (`G = 1`): `3H² = 8πρ` iff `H² = HQVM_CLASS_rhoCrit ρ`. -/
theorem HQVM_CLASS_GR_flat_H_sq_iff (H rho : ℝ) :
    3 * H ^ 2 = 8 * Real.pi * rho ↔ H ^ 2 = HQVM_CLASS_rhoCrit rho := by
  dsimp [HQVM_CLASS_rhoCrit]
  constructor
  · intro h
    have := congr_arg (fun x => x / (3 : ℝ)) h
    field_simp at this ⊢
    linarith
  · intro h
    rw [h]
    ring

theorem zero_le_G_eff_of_nonneg (φ : ℝ) (hφ : 0 ≤ φ) : 0 ≤ G_eff φ := by
  rw [G_eff_eq φ hφ]
  exact Real.rpow_nonneg hφ _

theorem zero_le_HQVM_CLASS_rhoCrit_of_nonneg {rho : ℝ} (hρ : 0 ≤ rho) : 0 ≤ HQVM_CLASS_rhoCrit rho := by
  unfold HQVM_CLASS_rhoCrit
  have h1 : 0 ≤ 8 * Real.pi * rho :=
    mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) Real.pi_nonneg) hρ
  exact div_nonneg h1 (by norm_num : (0 : ℝ) ≤ 3)

/-- **`3 / (3 − γ) = 15/13`** at `γ = 2/5`. -/
theorem HQVM_CLASS_three_div_three_minus_gamma : (3 : ℝ) / (3 - gamma_HQIV) = 15 / 13 := by
  rw [three_minus_gamma_eq]
  norm_num

/-- **Lean Friedmann** iff the **CLASS-style** squared Hubble identity with `ρ_crit = 8πρ_tot/3`. -/
theorem HQVM_Friedmann_eq_iff_CLASS_H_squared (φ rho_m rho_r : ℝ) :
    HQVM_Friedmann_eq φ rho_m rho_r ↔
      φ ^ 2 = (3 / (3 - gamma_HQIV)) * G_eff φ * HQVM_CLASS_rhoCrit (rho_total rho_m rho_r) := by
  have hne : (3 : ℝ) - gamma_HQIV ≠ 0 := ne_of_gt three_minus_gamma_pos
  rw [HQVM_Friedmann_eq_def]
  have hcast : (3.0 : ℝ) - gamma_HQIV = (3 : ℝ) - gamma_HQIV := by norm_num
  have h8 : (8.0 : ℝ) = (8 : ℝ) := by norm_num
  rw [hcast, h8, HQVM_CLASS_rhoCrit_eq, rho_total_eq, H_of_phi_eq]
  constructor
  · intro h
    apply mul_left_cancel₀ hne
    calc
      (3 - gamma_HQIV) * φ ^ 2 = 8 * Real.pi * G_eff φ * (rho_m + rho_r) := h
      _ = (3 - gamma_HQIV) *
            (3 / (3 - gamma_HQIV) * G_eff φ * (8 * Real.pi * (rho_m + rho_r) / 3)) := by
            field_simp [hne]
  · intro h2
    calc
      (3 - gamma_HQIV) * φ ^ 2
          = (3 - gamma_HQIV) *
              (3 / (3 - gamma_HQIV) * G_eff φ * (8 * Real.pi * (rho_m + rho_r) / 3)) := by rw [h2]
      _ = 8 * Real.pi * G_eff φ * (rho_m + rho_r) := by field_simp [hne]

/-- Same equivalence with **`15/13`** instead of **`3/(3−γ)`** (`γ = 2/5`). -/
theorem HQVM_Friedmann_eq_iff_CLASS_H_squared_rational (φ rho_m rho_r : ℝ) :
    HQVM_Friedmann_eq φ rho_m rho_r ↔
      φ ^ 2 = (15 / 13) * G_eff φ * HQVM_CLASS_rhoCrit (rho_total rho_m rho_r) := by
  rw [HQVM_Friedmann_eq_iff_CLASS_H_squared]
  simp_rw [HQVM_CLASS_three_div_three_minus_gamma]

/-- **Picard step** used in CLASS: `H ↦ √((3/(3−γ)) G_eff(H) ρ_crit)` (nonnegative branch). -/
noncomputable def HQVM_CLASS_picardStep (H_guess rhoCrit : ℝ) : ℝ :=
  Real.sqrt ((3 / (3 - gamma_HQIV)) * G_eff H_guess * rhoCrit)

theorem HQVM_CLASS_picard_inside_nonneg (H_guess rhoCrit : ℝ)
    (hH : 0 ≤ H_guess) (hρ : 0 ≤ rhoCrit) :
    0 ≤ (3 / (3 - gamma_HQIV)) * G_eff H_guess * rhoCrit := by
  have hdiv : 0 < (3 : ℝ) / (3 - gamma_HQIV) :=
    div_pos (by norm_num : (0 : ℝ) < 3) three_minus_gamma_pos
  exact mul_nonneg (mul_nonneg hdiv.le (zero_le_G_eff_of_nonneg H_guess hH)) hρ

theorem HQVM_CLASS_picardStep_sq (H_guess rhoCrit : ℝ)
    (hH : 0 ≤ H_guess) (hρ : 0 ≤ rhoCrit) :
    (HQVM_CLASS_picardStep H_guess rhoCrit) ^ 2 =
      (3 / (3 - gamma_HQIV)) * G_eff H_guess * rhoCrit := by
  unfold HQVM_CLASS_picardStep
  rw [Real.sq_sqrt (HQVM_CLASS_picard_inside_nonneg H_guess rhoCrit hH hρ)]

/-- For **`H ≥ 0`**, **`HQVM_Friedmann_eq H …`** iff **`H`** is a **fixed point** of `HQVM_CLASS_picardStep`
with **`ρ_crit = HQVM_CLASS_rhoCrit (ρ_m + ρ_r)`** — the exact algebraic content of the CLASS Picard loop. -/
theorem HQVM_CLASS_fixed_point_sqrt_iff_Friedmann (H rho_m rho_r : ℝ)
    (hH : 0 ≤ H) (hρ : 0 ≤ rho_total rho_m rho_r) :
    H = HQVM_CLASS_picardStep H (HQVM_CLASS_rhoCrit (rho_total rho_m rho_r)) ↔
      HQVM_Friedmann_eq H rho_m rho_r := by
  have hρc := zero_le_HQVM_CLASS_rhoCrit_of_nonneg hρ
  have hiff := HQVM_Friedmann_eq_iff_CLASS_H_squared H rho_m rho_r
  constructor
  · intro hfix
    refine hiff.mpr ?_
    have hsq_eq :
        H ^ 2 = (HQVM_CLASS_picardStep H (HQVM_CLASS_rhoCrit (rho_total rho_m rho_r))) ^ 2 :=
      congr_arg (fun x => x ^ 2) hfix
    rw [hsq_eq, HQVM_CLASS_picardStep_sq H _ hH hρc]
  · intro hF
    have hsq := hiff.mp hF
    calc
      H = Real.sqrt (H ^ 2) := (Real.sqrt_sq hH).symm
      _ = Real.sqrt ((3 / (3 - gamma_HQIV)) * G_eff H * HQVM_CLASS_rhoCrit (rho_total rho_m rho_r)) :=
            congr_arg Real.sqrt hsq

/-- A Friedmann solution is **unchanged** by one Picard step (algebraic fixed point). -/
theorem HQVM_CLASS_picardStep_eq_of_Friedmann (H rho_m rho_r : ℝ)
    (hH : 0 ≤ H) (hρ : 0 ≤ rho_total rho_m rho_r) (hF : HQVM_Friedmann_eq H rho_m rho_r) :
    HQVM_CLASS_picardStep H (HQVM_CLASS_rhoCrit (rho_total rho_m rho_r)) = H :=
  Eq.symm ((HQVM_CLASS_fixed_point_sqrt_iff_Friedmann H rho_m rho_r hH hρ).mpr hF)

end CLASSBackgroundMethodology

section PicardConvergence

/-!
### Picard iteration on the CLASS square-root map

The CLASS homogeneous loop updates `H` by `HQVM_CLASS_picardStep H ρ_crit`. Under **`ρ_crit = 0`**
(vacuum), the map collapses to **`0` in one step**, so the unique nonnegative fixed point is **`0`**
and every iterate stabilizes. Under **`ρ_crit ≥ 0`** and **`Monotone G_eff`**, the Picard map is
**monotone**; with a **nondecreasing seed** `H₀ ≤ F(H₀)` and a **finite upper bound** on the orbit,
`Nat.iterate` is **monotone and bounded**, hence **converges** to **`⨆ₙ Fⁿ(H₀)`**; **continuity** of
`F` then identifies this limit as a **fixed point** of `F`. This is the monotone-bounded route
(`tendsto_atTop_ciSup`); it certifies that the C Picard loop reaches **a** limiting background once
the iterate sequence is monotone and bounded (e.g. vacuum, or numerically enforced caps).

**Note:** For **`ρ_crit > 0`**, **`H = 0`** is always a nonnegative fixed point (`G_eff 0 = 0`), so a
**globally unique** nonnegative fixed point does **not** hold without further side conditions; we
prove **global uniqueness only in vacuum** (`ρ_crit = 0`).
-/

/-- Picard iterates `H₀, F(H₀), F(F(H₀)), …` with `F(H) = HQVM_CLASS_picardStep H ρ_crit`. -/
noncomputable def HQVM_CLASS_picardIter (rhoCrit H0 : ℝ) (n : ℕ) : ℝ :=
  (fun H => HQVM_CLASS_picardStep H rhoCrit)^[n] H0

theorem continuous_G_eff : Continuous G_eff := by
  have hα : (0 : ℝ) ≤ alpha := by rw [alpha_eq_3_5]; norm_num
  have hG :
      G_eff = fun φ : ℝ => φ ^ alpha := by
    funext φ
    simp [G_eff, G0_eq, H0_eq, H_of_phi]
  rw [hG]
  exact Real.continuous_rpow_const hα

/-- The CLASS Picard map `H ↦ √((3/(3−γ)) G_eff(H) ρ_crit)` is continuous in `H` for fixed `ρ_crit`. -/
theorem HQVM_CLASS_picard_continuous (rhoCrit : ℝ) :
    Continuous (HQVM_CLASS_picardStep · rhoCrit) := by
  unfold HQVM_CLASS_picardStep
  refine Real.continuous_sqrt.comp ?_
  exact (continuous_const.mul continuous_G_eff).mul continuous_const

theorem HQVM_CLASS_picard_inside_mono (rhoCrit : ℝ) (hρ : 0 ≤ rhoCrit) (hG_mono : Monotone G_eff) :
    Monotone fun H =>
      (3 / (3 - gamma_HQIV)) * G_eff H * rhoCrit := by
  intro x y hxy
  have hc : 0 ≤ (3 : ℝ) / (3 - gamma_HQIV) :=
    le_of_lt (div_pos (by norm_num : (0 : ℝ) < 3) three_minus_gamma_pos)
  have h1 : G_eff x * rhoCrit ≤ G_eff y * rhoCrit :=
    mul_le_mul_of_nonneg_right (hG_mono hxy) hρ
  have h2 :
      (3 / (3 - gamma_HQIV)) * (G_eff x * rhoCrit) ≤
        (3 / (3 - gamma_HQIV)) * (G_eff y * rhoCrit) :=
    mul_le_mul_of_nonneg_left h1 hc
  simpa [mul_assoc, mul_left_comm, mul_comm] using h2

theorem HQVM_CLASS_picard_monotone (rhoCrit : ℝ) (hρ : 0 ≤ rhoCrit) (hG_mono : Monotone G_eff) :
    Monotone (HQVM_CLASS_picardStep · rhoCrit) :=
  Real.sqrt_monotone.comp (HQVM_CLASS_picard_inside_mono rhoCrit hρ hG_mono)

theorem HQVM_CLASS_picardStep_eq_zero_of_rhoCrit_zero (H rhoCrit : ℝ) (hρ : rhoCrit = 0) :
    HQVM_CLASS_picardStep H rhoCrit = 0 := by
  unfold HQVM_CLASS_picardStep
  simp [hρ]

/-- **Vacuum (`ρ_crit = 0`):** every Picard step is `0`, so `0` is the unique nonnegative fixed point. -/
theorem HQVM_CLASS_picard_unique_nonneg_fixed_point_vacuum (rhoCrit : ℝ) (hρ : rhoCrit = 0) :
    ∃! H : ℝ, 0 ≤ H ∧ H = HQVM_CLASS_picardStep H rhoCrit := by
  refine ⟨0, ?_, ?_⟩
  · constructor
    · exact le_rfl
    · simp [HQVM_CLASS_picardStep_eq_zero_of_rhoCrit_zero _ _ hρ]
  · rintro H ⟨hH, hfix⟩
    rw [hfix, HQVM_CLASS_picardStep_eq_zero_of_rhoCrit_zero _ _ hρ]

/-- **Vacuum (`ρ_crit = 0`):** the unique nonnegative fixed point is `H* = 0`
(global uniqueness fails for `ρ_crit > 0` because `H = 0` is always a fixed point). -/
theorem HQVM_CLASS_picard_has_unique_fixed_point (rhoCrit : ℝ) (hρ : rhoCrit = 0) :
    ∃! H : ℝ, H ≥ 0 ∧ H = HQVM_CLASS_picardStep H rhoCrit := by
  simpa [ge_iff_le] using HQVM_CLASS_picard_unique_nonneg_fixed_point_vacuum rhoCrit hρ

theorem HQVM_CLASS_picardIter_eq_zero_after_one (rhoCrit H0 : ℝ) (hρ : rhoCrit = 0) :
    ∀ {n : ℕ}, 0 < n → HQVM_CLASS_picardIter rhoCrit H0 n = 0
  | 0, hn => absurd hn (Nat.lt_irrefl _)
  | 1, _ => by
      rw [HQVM_CLASS_picardIter, Function.iterate_succ_apply', Function.iterate_zero]
      exact HQVM_CLASS_picardStep_eq_zero_of_rhoCrit_zero H0 rhoCrit hρ
  | n + 2, _ => by
      have heq :
          HQVM_CLASS_picardStep ((fun H => HQVM_CLASS_picardStep H rhoCrit)^[n] H0) rhoCrit =
            HQVM_CLASS_picardIter rhoCrit H0 (n + 1) := by
        simp [HQVM_CLASS_picardIter, Function.iterate_succ_apply']
      simp only [HQVM_CLASS_picardIter, Function.iterate_succ_apply']
      rw [heq, HQVM_CLASS_picardIter_eq_zero_after_one rhoCrit H0 hρ (Nat.succ_pos n)]
      exact HQVM_CLASS_picardStep_eq_zero_of_rhoCrit_zero _ _ hρ

/-- **Vacuum:** Picard iterates converge to **`H* = 0`** (the unique nonnegative fixed point).
This certifies that the C Picard loop reaches the unique physical **vacuum** background from any
initial `H₀ ≥ 0`. For `ρ_crit > 0`, use `HQVM_CLASS_picardIter_tendsto_ciSup_fixed` under a
monotone, bounded iterate orbit. -/
theorem HQVM_CLASS_picard_converges_to_fixed_point (rhoCrit H0 : ℝ) (_hH0 : 0 ≤ H0) (hρ : rhoCrit = 0) :
    Tendsto (fun n => HQVM_CLASS_picardIter rhoCrit H0 n) atTop (𝓝 0) := by
  have hev :
      ∀ᶠ (n : ℕ) in atTop, HQVM_CLASS_picardIter rhoCrit H0 n = 0 := by
    rw [eventually_atTop]
    refine ⟨1, ?_⟩
    intro n hn
    exact HQVM_CLASS_picardIter_eq_zero_after_one rhoCrit H0 hρ (Nat.lt_of_succ_le hn)
  exact tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)

theorem HQVM_CLASS_picardIter_succ (rhoCrit H0 : ℝ) (n : ℕ) :
    HQVM_CLASS_picardIter rhoCrit H0 (n + 1) =
      HQVM_CLASS_picardStep (HQVM_CLASS_picardIter rhoCrit H0 n) rhoCrit := by
  simp [HQVM_CLASS_picardIter, Function.iterate_succ_apply']

theorem HQVM_CLASS_picardIter_monotone (rhoCrit H0 : ℝ) (hρ : 0 ≤ rhoCrit) (hG_mono : Monotone G_eff)
    (hseed : H0 ≤ HQVM_CLASS_picardStep H0 rhoCrit) :
    Monotone (HQVM_CLASS_picardIter rhoCrit H0) := by
  refine monotone_nat_of_le_succ ?_
  intro k
  induction k with
  | zero =>
    simpa [HQVM_CLASS_picardIter, Function.iterate_zero, Function.iterate_succ_apply'] using hseed
  | succ k ih =>
    simpa [HQVM_CLASS_picardIter, Function.iterate_succ_apply', Function.iterate_succ_apply'] using
      (HQVM_CLASS_picard_monotone rhoCrit hρ hG_mono) ih

theorem tendsto_nat_succ_atTop : Tendsto (Nat.succ : ℕ → ℕ) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro b
  refine ⟨b, fun a ha => le_trans ha (Nat.le_succ a)⟩

theorem HQVM_CLASS_picard_ciSup_fixed_point (rhoCrit H0 : ℝ) (_hρ : 0 ≤ rhoCrit)
    (hmono : Monotone (HQVM_CLASS_picardIter rhoCrit H0))
    (hbdd : BddAbove (range (HQVM_CLASS_picardIter rhoCrit H0))) :
    (⨆ n : ℕ, HQVM_CLASS_picardIter rhoCrit H0 n) =
      HQVM_CLASS_picardStep (⨆ n : ℕ, HQVM_CLASS_picardIter rhoCrit H0 n) rhoCrit := by
  set u : ℕ → ℝ := HQVM_CLASS_picardIter rhoCrit H0
  set L : ℝ := ⨆ n, u n
  have hlim : Tendsto u atTop (𝓝 L) := tendsto_atTop_ciSup hmono hbdd
  have hlim' : Tendsto (fun n => u (n + 1)) atTop (𝓝 L) :=
    hlim.comp tendsto_nat_succ_atTop
  have hFcont := HQVM_CLASS_picard_continuous rhoCrit
  have hlimF : Tendsto (fun n => HQVM_CLASS_picardStep (u n) rhoCrit) atTop (𝓝 (HQVM_CLASS_picardStep L rhoCrit)) :=
    (hFcont.tendsto L).comp hlim
  have hsame : (fun n => u (n + 1)) = fun n => HQVM_CLASS_picardStep (u n) rhoCrit := by
    funext n
    simp [u, HQVM_CLASS_picardIter_succ]
  rw [hsame] at hlim'
  exact tendsto_nhds_unique hlim' hlimF

/-- Monotone, bounded-above Picard iterates converge to their supremum, which is a fixed point. -/
theorem HQVM_CLASS_picardIter_tendsto_ciSup_fixed (rhoCrit H0 : ℝ) (hρ : 0 ≤ rhoCrit)
    (hG_mono : Monotone G_eff) (hseed : H0 ≤ HQVM_CLASS_picardStep H0 rhoCrit)
    (hbdd : BddAbove (range (HQVM_CLASS_picardIter rhoCrit H0))) :
    Tendsto (fun n => HQVM_CLASS_picardIter rhoCrit H0 n) atTop
        (𝓝 (⨆ n : ℕ, HQVM_CLASS_picardIter rhoCrit H0 n)) ∧
      (⨆ n : ℕ, HQVM_CLASS_picardIter rhoCrit H0 n) =
        HQVM_CLASS_picardStep (⨆ n : ℕ, HQVM_CLASS_picardIter rhoCrit H0 n) rhoCrit := by
  have hmono := HQVM_CLASS_picardIter_monotone rhoCrit H0 hρ hG_mono hseed
  refine ⟨?_, ?_⟩
  · exact tendsto_atTop_ciSup hmono hbdd
  · exact HQVM_CLASS_picard_ciSup_fixed_point rhoCrit H0 hρ hmono hbdd

end PicardConvergence

section GravitationalActionBridge

/-!
### Link to `S_HQVM_grav` (`Action`)

`S_HQVM_grav φ ρ_m ρ_r = (3−γ)φ² − 8π G_eff(φ)(ρ_m+ρ_r)` is the **homogeneous** gravitational
constraint density whose vanishing is equivalent to `HQVM_Friedmann_eq` (`S_HQVM_grav_zero_iff_Friedmann`).
Subtracting two such residuals at the same densities is **exact algebra** — no new axiom.
-/

/-- Difference of gravitational residuals at two `φ` values, same `(ρ_m, ρ_r)`. -/
theorem S_HQVM_grav_sub_eq (φ₁ φ₂ rho_m rho_r : ℝ) :
    S_HQVM_grav φ₁ rho_m rho_r - S_HQVM_grav φ₂ rho_m rho_r =
      (3 - gamma_HQIV) * (φ₁ ^ 2 - φ₂ ^ 2) -
        8 * Real.pi * (G_eff φ₁ - G_eff φ₂) * rho_total rho_m rho_r := by
  unfold S_HQVM_grav rho_total
  ring

/-- Vanishing residual difference ⟺ the same identity as `HQVM_Friedmann_eq_difference` but with
`(3 : ℝ)` / `(8 : ℝ)` from `S_HQVM_grav` (not `3.0` / `8.0` from `HQVM_Friedmann_eq_def`). -/
theorem S_HQVM_grav_sub_eq_zero_iff (φ₁ φ₂ rho_m rho_r : ℝ) :
    S_HQVM_grav φ₁ rho_m rho_r - S_HQVM_grav φ₂ rho_m rho_r = 0 ↔
      (3 - gamma_HQIV) * (φ₁ ^ 2 - φ₂ ^ 2) =
        8 * Real.pi * (G_eff φ₁ - G_eff φ₂) * rho_total rho_m rho_r := by
  rw [S_HQVM_grav_sub_eq φ₁ φ₂ rho_m rho_r, sub_eq_zero]

/-- Two Friedmann-satisfying backgrounds have equal gravitational residual (both zero). -/
theorem S_HQVM_grav_sub_zero_of_Friedmann_pair (φ₁ φ₂ rho_m rho_r : ℝ)
    (h₁ : HQVM_Friedmann_eq φ₁ rho_m rho_r) (h₂ : HQVM_Friedmann_eq φ₂ rho_m rho_r) :
    S_HQVM_grav φ₁ rho_m rho_r - S_HQVM_grav φ₂ rho_m rho_r = 0 := by
  have s₁ : S_HQVM_grav φ₁ rho_m rho_r = 0 :=
    (S_HQVM_grav_zero_iff_Friedmann φ₁ rho_m rho_r).mpr h₁
  have s₂ : S_HQVM_grav φ₂ rho_m rho_r = 0 :=
    (S_HQVM_grav_zero_iff_Friedmann φ₂ rho_m rho_r).mpr h₂
  linarith

/-- `HQVM_Friedmann_eq_difference` is the `3.0`/`8.0` spelling of the same subtraction identity as
`S_HQVM_grav_sub_eq_zero_iff` (numeral defeq on `ℝ`). -/
theorem HQVM_Friedmann_eq_difference_eq_S_grav_sub_zero_iff (φ₁ φ₂ rho_m rho_r : ℝ) :
    ((3.0 - gamma_HQIV) * (φ₁ ^ 2 - φ₂ ^ 2) =
        8.0 * Real.pi * (G_eff φ₁ - G_eff φ₂) * rho_total rho_m rho_r) ↔
      S_HQVM_grav φ₁ rho_m rho_r - S_HQVM_grav φ₂ rho_m rho_r = 0 := by
  rw [S_HQVM_grav_sub_eq_zero_iff]
  constructor <;> intro h <;> convert h using 1 <;> norm_num

end GravitationalActionBridge

section SingleModePoisson

/-!
### Optional: single Fourier-mode scalar constraint (definition only)

Newtonian Poisson in Fourier space is often written `k² δΦ ∝ G δρ`. We record a **schematic** scalar
constraint using `G_eff φ` from `HQVMetric` — **not** derived from the Hamiltonian constraint here.
At `k = 0` the left side vanishes, so consistency forces `G_eff φ * δρ = 0` unless one relaxes the
definition (standard long-wavelength degeneracy).
-/

/-- Schematic single-mode Poisson: `k² δΦ = 4π G_eff(φ) δρ`. -/
def HQVM_singleMode_Poisson (k φ δΦ δρ : ℝ) : Prop :=
  k ^ 2 * δΦ = 4 * Real.pi * G_eff φ * δρ

theorem HQVM_singleMode_Poisson_iff_of_ne_zero (k φ δΦ δρ : ℝ) (hk : k ≠ 0) :
    HQVM_singleMode_Poisson k φ δΦ δρ ↔
      δΦ = 4 * Real.pi * G_eff φ * δρ / k ^ 2 := by
  have hk2 : k ^ 2 ≠ 0 := pow_ne_zero 2 hk
  unfold HQVM_singleMode_Poisson
  constructor
  · intro h
    field_simp [hk2]
    linarith
  · intro h
    field_simp [hk2] at h
    linarith

/-- Long-wavelength (`k = 0`) degeneracy: the Poisson predicate is `0 = 4π G_eff(φ) δρ`. -/
theorem HQVM_singleMode_Poisson_k0_iff (φ δΦ δρ : ℝ) :
    HQVM_singleMode_Poisson 0 φ δΦ δρ ↔ 4 * Real.pi * G_eff φ * δρ = 0 := by
  simp [HQVM_singleMode_Poisson]

end SingleModePoisson

end Hqiv
