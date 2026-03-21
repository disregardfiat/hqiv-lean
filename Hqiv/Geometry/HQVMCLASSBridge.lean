import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.HQVMPerturbations
import Hqiv.Physics.Action

namespace Hqiv

/-!
# HQVM ↔ CLASS-oriented linearized metric scaffolding (background + first-order piece)

This module is **not** a formalization of CLASS file-level equivalence, the full linearized Einstein
equations, Bardeen / Newtonian gauge transformations, photon polarization hierarchies, or Boltzmann
collision sources. It records a **synchronous-comoving** ansatz consistent with `HQVMetric`
(shift zero, `N = HQVM_lapse`, spatial coefficient `HQVM_spatial_coeff`) and packages the **exact**
finite increments into **background + linearized + remainder** form so a future numerical patch has a
clear Lean target.

**What is claimed:** algebraic decomposition of lapse and spatial conformal factor; subtraction of two
instances of `HQVM_Friedmann_eq`; a schematic single-`k` Poisson **definition** with solvability at
`k ≠ 0`.

**What is not claimed:** derivation of the Poisson equation from `HQVM_Friedmann_eq` or from a
3+1 Einstein constraint; matching of variables to any particular CLASS `perturbs` array layout.

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
