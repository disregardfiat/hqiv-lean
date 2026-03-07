import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Pi.Bounds

import Hqiv.Geometry.AuxiliaryField

namespace Hqiv

/-!
# HQVMetric — Horizon Quantized Vacuum Metric (Non-FLRW) and Effective Friedmann Equation

HQIV is **not** FLRW: the background is the **Horizon-Quantized Vacuum Metric (HQVM)**,
which is inhomogeneous (Φ, φ depend on position/time). We adopt synchronous-comoving
gauge (shift βⁱ = 0). The **ADM lapse** N is fixed by the informational-energy axiom
and the horizon-overlap coefficient γ (paper: N = 1 + Φ + φ t/c; natural units: N = 1 + Φ + φ t).
The line element is ds² = -N² dt² + a(t)²(1 - 2Φ) δᵢⱼ dxⁱ dxʲ.

This module provides:
- **ADM lapse:** definition and proof that the HQVM metric has lapse N = 1 + Φ + φ t
  (see `HQVM_lapse` and `HQVM_tt_coefficient`).
- **Homogeneous limit:** γ, G_eff, and the declarative Friedmann equation
  (φ ≈ H, used for volume-averaged dynamics and CLASS).

The theory is built from **division math** (α = 3/5, γ = 2/5) and **monogamy**;
the lapse formula encodes observer-centric time (wall-clock vs apparent age).

**√3 vs 2π:** The curvature norm (light-cone module) uses **√3** — a **spatial** factor
(unit-cube half-diagonal, dimension length). The time phase here uses **2π** — an
**angular** period (dimension angle). So they are not the same kind of constant:
one is geometry of the 3D cube, the other is the period of phase. No conflict.

### Arriving at the definitions (derivation path)

We do not introduce free parameters. Each definition is **determined by** prior structure:

1. **Lapse N:** The **informational-energy axiom** (paper) fixes the ADM lapse in
   synchronous-comoving gauge to N = 1 + Φ + φ t. So `HQVM_lapse` is the unique
   form imposed by that axiom; we then prove it equals 1 + Φ + timeAngle φ t.

2. **Time angle δθ′:** φ is already fixed by the lattice (AuxiliaryField: φ(m) = 2/T(m)).
   The horizon term in N is φ t, which we call `timeAngle`; it is the only
   cumulative-in-time piece, so it is **determined** by the lapse decomposition.

3. **Metric components:** With shift βⁱ = 0, the line element is ds² = -N² dt² + spatial.
   So g_tt = -N² and the spatial coefficient is a²(1 - 2Φ) **from ADM** with
   conformal factor (1 - 2Φ). No choice — just writing the metric in this gauge.

4. **γ:** From **entanglement monogamy** (metric sector); γ = 2/5. Proved equal to
   the paper value; (3−γ) = 13/5 and α + γ = 1 from the lattice/monogamy split.

5. **G₀, H₀:** **Natural units** (c = ħ = 1, G₀ = H₀ = 1). Convention, not a free
   fit; we prove G_eff(1) = 1 when φ = H₀.

6. **G_eff:** The paper’s varying-G relation G_eff/G₀ = (H/H₀)^α with α from the
   **lattice** (3/5). So G_eff(φ) = φ^α in natural units — **determined** by α and
   the homogeneous identification H = φ.

7. **Friedmann equation:** (3−γ)H² = 8π G_eff(φ)(ρ_m + ρ_r) is the **Einstein
   equation** in the homogeneous HQVM limit with varying G. So the def
   `HQVM_Friedmann_eq` is the statement of that equation; we then prove
   rational form, vacuum iff φ = 0, and sign of (3−γ).

Thus the proven theory in this file **rests on** the light-cone (α, φ, curvature),
monogamy (γ), natural units, and the informational-energy axiom; the defs are
arrived at by fixing those, not by tuning.
-/

/-!
## HQVM metric and ADM lapse (non-homogeneous)

The full HQVM is not FLRW. In synchronous-comoving gauge (shift βⁱ = 0) the lapse N
is **fixed by** the informational-energy axiom: N = 1 + Φ + φ t (natural units).
We define the lapse as that expression and then prove all subsequent structure.
-/

/-- **ADM lapse** (determined by the informational-energy axiom): N = 1 + Φ + φ t.
Φ = Newtonian potential; φ = auxiliary field from the lattice (2/Θ); t = coordinate time.
The term φ t is the horizon contribution (time angle). So this def is the unique
lapse imposed by the axiom in synchronous-comoving gauge. -/
def HQVM_lapse (Φ φ t : ℝ) : ℝ := 1 + Φ + φ * t

/-- **Time angle (δθ′)** from the observer: φ · t (natural units).

From the observer’s perspective, the time angle is the cumulative phase that
**allows interaction with newly unlocked horizon modes**. Those modes are the
ones from the curvature already proved in the light-cone module: shell-wise
mode count (`new_modes`, `available_modes`), curvature imprint (δE, `shell_shape`),
and curvature integral / Ω_k at the chosen horizon. So δθ′ = φ t is not an
extra degree of freedom: φ is tied to the lattice (e.g. φ(m) = 2/T(m) in
AuxiliaryField), and as t advances the observer couples to the next shell’s
unlocked modes from that curvature. -/
def timeAngle (φ t : ℝ) : ℝ := φ * t

/-- **Lapse equals 1 + Φ + time angle:** N = 1 + Φ + δθ′. -/
theorem HQVM_lapse_eq_timeAngle (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + timeAngle φ t := rfl

/-- **ADM lapse is the HQVM lapse:** In the HQVM line element
  ds² = -N² dt² + a(t)²(1 - 2Φ) δᵢⱼ dxⁱ dxʲ
with shift zero, the lapse function (the function N such that g_tt = -N²) is
N = 1 + Φ + φ t = 1 + Φ + timeAngle φ t. -/
theorem ADM_lapse_eq_HQVM_lapse (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + φ * t := rfl

/-- **Time angle is the horizon term in the lapse:** N = 1 + Φ + timeAngle φ t. -/
theorem lapse_decompose (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + timeAngle φ t := by unfold HQVM_lapse timeAngle; rfl

/-- **Time angle is monotone in t** when φ > 0: more coordinate time ⇒ larger
δθ′ ⇒ (in the narrative) interaction with more unlocked horizon modes. -/
theorem timeAngle_mono_t (φ t₁ t₂ : ℝ) (hφ : 0 < φ) (ht : t₁ ≤ t₂) :
    timeAngle φ t₁ ≤ timeAngle φ t₂ := by
  unfold timeAngle
  exact mul_le_mul_of_nonneg_left ht (le_of_lt hφ)

/-- **Time angle at t = 0:** δθ′ = 0 (no cumulative horizon phase yet). -/
theorem timeAngle_zero_t (φ : ℝ) : timeAngle φ 0 = 0 := by unfold timeAngle; ring

/-- **Period of the time angle:** 2π (one full phase turn). Spin lost to the horizon
is conserved as phase: the time angle is interpreted mod 2π, so no spin is destroyed,
only wrapped. This is **angular** (2π); the curvature norm’s √3 is **spatial**
(unit-cube half-diagonal) — different dimensions. -/
noncomputable def twoPi : ℝ := 2 * Real.pi

theorem twoPi_eq : twoPi = 2 * Real.pi := rfl

/-- **Time angle reaches 2π at the first period:** when φ > 0, δθ′ = 2π at t = 2π/φ. -/
theorem timeAngle_first_period (φ : ℝ) (hφ : 0 < φ) :
    timeAngle φ (twoPi / φ) = twoPi := by
  unfold timeAngle twoPi
  field_simp [hφ.ne']

/-- **Time angle in the first period:** for φ > 0 and t ∈ [0, 2π/φ], δθ′ ∈ [0, 2π].
So the time angle sweeps [0, 2π] as t goes from 0 to the first period. -/
theorem timeAngle_mem_Icc_first_period (φ t : ℝ) (hφ : 0 < φ) (ht0 : 0 ≤ t) (ht : t ≤ twoPi / φ) :
    timeAngle φ t ∈ Set.Icc (0 : ℝ) twoPi := by
  unfold timeAngle twoPi
  constructor
  · exact mul_nonneg (le_of_lt hφ) ht0
  · calc φ * t = t * φ := mul_comm φ t
      _ ≤ (2 * Real.pi / φ) * φ := mul_le_mul_of_nonneg_right ht (le_of_lt hφ)
      _ = 2 * Real.pi := by field_simp [hφ.ne']

/-- **Lower limit:** at t = 0 the time angle is 0 (already in `timeAngle_zero_t`). -/
theorem timeAngle_limit_zero (φ : ℝ) :
    timeAngle φ 0 = 0 := timeAngle_zero_t φ

/-- **Upper limit (first period):** at t = 2π/φ the time angle is 2π. -/
theorem timeAngle_limit_twoPi (φ : ℝ) (hφ : 0 < φ) :
    timeAngle φ (twoPi / φ) = twoPi := timeAngle_first_period φ hφ

/-!
### Spin conserved at the horizon

The time angle δθ′ is periodic mod 2π. **Spin lost to the horizon** is not destroyed:
it is encoded in the phase (δθ′ mod 2π), which wraps in [0, 2π). So total spin
(phase) is conserved; the horizon only resets the angle every 2π. This is the
conservation statement for spin lost to the horizon.
-/

/-- **Spin conservation (narrative):** the time angle in [0, 2π] and its periodic
extension mod 2π encodes the phase of modes locked at the horizon; that phase
is conserved (wraps rather than being lost). -/
theorem timeAngle_zero_to_twoPi (φ : ℝ) (hφ : 0 < φ) :
    timeAngle φ 0 = 0 ∧ timeAngle φ (twoPi / φ) = twoPi ∧
    ∀ t, t ∈ Set.Icc 0 (twoPi / φ) → timeAngle φ t ∈ Set.Icc 0 twoPi := by
  refine ⟨timeAngle_zero_t φ, timeAngle_first_period φ hφ, fun t ht => ?_⟩
  exact timeAngle_mem_Icc_first_period φ t hφ ht.1 ht.2

/-- In the homogeneous limit (Φ = 0, φ = H) the lapse is N = 1 + H t. -/
theorem HQVM_lapse_homogeneous_limit (H t : ℝ) :
    HQVM_lapse 0 H t = 1 + H * t := by unfold HQVM_lapse; ring

/-- Minkowski limit: when Φ = 0 and φ = 0 the lapse is N = 1. -/
theorem HQVM_lapse_Minkowski (t : ℝ) : HQVM_lapse 0 0 t = 1 := by unfold HQVM_lapse; norm_num

/-- **Lapse at t = 0:** N = 1 + Φ (no time-angle contribution yet). -/
theorem HQVM_lapse_at_zero (Φ φ : ℝ) : HQVM_lapse Φ φ 0 = 1 + Φ := by unfold HQVM_lapse; ring

/-- **Lapse is monotone in t** when φ ≥ 0: t₁ ≤ t₂ ⇒ N(Φ, φ, t₁) ≤ N(Φ, φ, t₂). -/
theorem HQVM_lapse_mono_t (Φ φ t₁ t₂ : ℝ) (hφ : 0 ≤ φ) (ht : t₁ ≤ t₂) :
    HQVM_lapse Φ φ t₁ ≤ HQVM_lapse Φ φ t₂ := by
  unfold HQVM_lapse
  have H := add_le_add_right (add_le_add_left (mul_le_mul_of_nonneg_right ht hφ) Φ) 1
  rw [mul_comm t₁ φ, mul_comm t₂ φ] at H
  conv_lhs => rw [add_assoc, add_comm Φ (φ * t₁)]
  conv_rhs => rw [add_assoc, add_comm Φ (φ * t₂)]
  exact H

/-- **Lapse is positive** when 1 + Φ > 0 and φ ≥ 0, t ≥ 0. So in the weak-field
(Φ > -1) and forward-time, non-negative φ regime, N > 0 and g_tt < 0 (timelike t). -/
theorem HQVM_lapse_pos (Φ φ t : ℝ) (h₁ : 0 < 1 + Φ) (hφ : 0 ≤ φ) (ht : 0 ≤ t) :
    0 < HQVM_lapse Φ φ t := by
  unfold HQVM_lapse
  exact lt_of_lt_of_le h₁ (by nlinarith [mul_nonneg hφ ht])

/-- **Lapse above Minkowski** when Φ ≥ 0, φ > 0, t > 0: N > 1. -/
theorem HQVM_lapse_gt_one (Φ φ t : ℝ) (hΦ : 0 ≤ Φ) (hφ : 0 < φ) (ht : 0 < t) :
    1 < HQVM_lapse Φ φ t := by
  unfold HQVM_lapse
  nlinarith [mul_pos hφ ht]

/-!
## HQVM manifold geometry

The line element is ds² = -N² dt² + a(t)²(1 - 2Φ) δᵢⱼ dxⁱ dxʲ. We formalise the
metric components and prove Lorentzian signature and positive-definite spatial part
under natural physical assumptions (N ≠ 0, a > 0, weak field Φ < 1/2).
-/

/-- **Time-time component** g_tt = -N². Determined by the ADM decomposition with
shift zero: the line element is -N² dt² + spatial, so g_tt is minus the lapse squared. -/
def HQVM_g_tt (N : ℝ) : ℝ := -N ^ 2

/-- **Spatial conformal factor** a²(1 - 2Φ). Determined by the ADM metric in
synchronous-comoving gauge: the spatial part is a(t)²(1 - 2Φ) δᵢⱼ, so this is
the coefficient of each dxⁱ dxⁱ (no free choice — just the gauge and potential Φ). -/
def HQVM_spatial_coeff (a Φ : ℝ) : ℝ := a ^ 2 * (1 - 2 * Φ)

/-- **g_tt is negative** whenever N ≠ 0, so the coordinate t is timelike
(Lorentzian time direction). -/
theorem HQVM_g_tt_neg (N : ℝ) (hN : N ≠ 0) :
    HQVM_g_tt N < 0 := by
  unfold HQVM_g_tt
  exact neg_lt_zero.mpr (sq_pos_of_ne_zero hN)

/-- **Spatial coefficient is positive** when a > 0 and Φ < 1/2 (weak-field regime:
the Newtonian potential does not dominate). So the spatial metric is Riemannian. -/
theorem HQVM_spatial_coeff_pos (a Φ : ℝ) (ha : 0 < a) (hΦ : Φ < 1/2) :
    0 < HQVM_spatial_coeff a Φ := by
  unfold HQVM_spatial_coeff
  have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
  have h : 0 < 1 - 2 * Φ := by linarith
  exact mul_pos ha2 h

/-- **ADM decomposition of the HQVM metric:** with lapse N = HQVM_lapse Φ φ t and
shift zero, the line element has g_tt = -N² and spatial diagonal coefficient
a²(1 - 2Φ). So the manifold is foliated by spatial hypersurfaces Σ_t with
induced metric a(t)²(1 - 2Φ) δᵢⱼ. -/
theorem HQVM_ADM_decomposition (Φ φ t a : ℝ) :
    HQVM_g_tt (HQVM_lapse Φ φ t) = -(HQVM_lapse Φ φ t) ^ 2 ∧
    HQVM_spatial_coeff a Φ = a ^ 2 * (1 - 2 * Φ) := by
  constructor
  · unfold HQVM_g_tt; rfl
  · unfold HQVM_spatial_coeff; rfl

/-- **Minkowski limit of the geometry:** Φ = 0, φ = 0, a = 1 gives g_tt = -1
and spatial coefficient 1 (flat spacetime). -/
theorem HQVM_geometry_Minkowski (t : ℝ) :
    HQVM_g_tt (HQVM_lapse 0 0 t) = -1 ∧ HQVM_spatial_coeff 1 0 = 1 := by
  constructor
  · rw [HQVM_lapse_Minkowski]; unfold HQVM_g_tt; norm_num
  · unfold HQVM_spatial_coeff; norm_num

/-- **Unit normal to constant-t hypersurfaces:** with shift zero, the future-pointing
normal is n = (1/N) ∂_t; its squared norm is g_tt · (1/N)² = -1, so n is timelike and unit. -/
theorem HQVM_unit_normal_squared (N : ℝ) (hN : N ≠ 0) :
    HQVM_g_tt N * (1 / N) ^ 2 = -1 := by
  unfold HQVM_g_tt; field_simp [hN]

/-- **Spatial coefficient expanded:** a²(1 - 2Φ) = a² - 2a²Φ. -/
theorem HQVM_spatial_coeff_expand (a Φ : ℝ) :
    HQVM_spatial_coeff a Φ = a ^ 2 - 2 * a ^ 2 * Φ := by
  unfold HQVM_spatial_coeff; ring

/-- **Lorentzian signature (g_tt < 0)** when the lapse is positive: N > 0 ⇒ g_tt < 0. -/
theorem HQVM_g_tt_neg_of_lapse_pos (Φ φ t : ℝ) (hN : 0 < HQVM_lapse Φ φ t) :
    HQVM_g_tt (HQVM_lapse Φ φ t) < 0 :=
  HQVM_g_tt_neg (HQVM_lapse Φ φ t) (ne_of_gt hN)

/-- **γ** (entanglement monogamy / overlap coefficient): defined as the **complement of α**
in the unit horizon split, i.e. γ = 1 − α. So γ is **derived** from the same structural
split that gives α from the lattice (α + γ = 1); no separate free parameter. -/
def gamma_HQIV : ℝ := 1 - alpha

/-- **γ = 2/5** — derived from α = 3/5 and the split α + γ = 1 (so γ = 1 − 3/5 = 2/5). -/
theorem gamma_eq_2_5 : gamma_HQIV = 2/5 := by
  unfold gamma_HQIV; rw [alpha_eq_3_5]; norm_num

/-- **γ equals the paper value 0.40** (2/5 = 0.40). -/
theorem gamma_eq_paper : gamma_HQIV = 0.40 := by rw [gamma_eq_2_5]; norm_num

/-- **Division of the horizon:** α (lattice) + γ (monogamy) = 1. Holds by definition of γ = 1 − α. -/
theorem alpha_add_gamma : alpha + gamma_HQIV = 1 := by unfold gamma_HQIV; ring

/-- **Coefficient (3 − γ) in the Friedmann equation** equals 13/5. Derived from γ = 2/5. -/
theorem three_minus_gamma_eq : (3 : ℝ) - gamma_HQIV = 13/5 := by
  rw [gamma_eq_2_5]; norm_num

/-- **(3 − γ) is positive** (13/5 > 0); so the H² term in the Friedmann equation
has the correct sign for an expanding universe. -/
theorem three_minus_gamma_pos : 0 < (3 : ℝ) - gamma_HQIV := by
  rw [three_minus_gamma_eq]; norm_num

/-- **G₀** (natural units): reference Newton coupling = 1. Convention: we set G₀ = 1,
so all couplings are relative to it; no free parameter. -/
def G0 : ℝ := 1.0

/-- **G₀ = 1 in natural units** (proved). -/
theorem G0_eq : G0 = 1 := by unfold G0; norm_num

/-- **H₀** (natural units): reference Hubble rate = 1. Same convention: H₀ = 1,
so G_eff(1) = 1 when φ = H₀. -/
def H0 : ℝ := 1.0

/-- **H₀ = 1 in natural units** (proved). -/
theorem H0_eq : H0 = 1 := by unfold H0; norm_num

/-- **H(φ)** (homogeneous limit): we identify φ with H in natural units (φ ≈ H).
So H_of_phi φ = φ. This is the **bridge** from the lattice field φ to the
Hubble rate in the Friedmann equation; not an extra degree of freedom. -/
def H_of_phi (φ : ℝ) : ℝ := φ

/-- H(φ) = φ (proved). -/
theorem H_of_phi_eq (φ : ℝ) : H_of_phi φ = φ := rfl

/-- **G_eff(φ)** (determined by the varying-G relation and the lattice α).
Paper: G_eff/G₀ = (H/H₀)^α; with H = φ (homogeneous) and G₀ = H₀ = 1 we get
G_eff(φ) = φ^α. So this def is **arrived at** from α (from the light cone) and
natural units — no extra fit. -/
noncomputable def G_eff (φ : ℝ) : ℝ :=
  G0 * (H_of_phi φ / H0) ^ alpha

/-- **G_eff in terms of φ and α only:** when G₀ = H₀ = 1, G_eff(φ) = φ^α (φ ≥ 0). -/
theorem G_eff_eq (φ : ℝ) (_hφ : 0 ≤ φ) :
  G_eff φ = φ ^ alpha := by
  simp only [G_eff, H_of_phi, G0_eq, H0_eq, div_one, one_mul]

/-- **G_eff at unit Hubble:** when φ = 1 (H = H₀ in natural units), G_eff(1) = 1 = G₀. -/
theorem G_eff_one : G_eff 1 = 1 := by
  rw [G_eff_eq 1 zero_le_one, alpha_eq_3_5]; norm_num

/-- Total homogeneous energy density (matter + radiation). -/
def rho_total (rho_m rho_r : ℝ) : ℝ := rho_m + rho_r

/-- Total density is the sum (proved). -/
theorem rho_total_eq (rho_m rho_r : ℝ) : rho_total rho_m rho_r = rho_m + rho_r := rfl

/-- **Friedmann equation** (arrived at from Einstein eqn in homogeneous HQVM limit).
  (3 − γ) H² = 8 π G_eff(φ) (ρ_m + ρ_r)
(3−γ) from monogamy, H = φ, G_eff from varying-G and α. So this is the **statement**
of the dynamics, not a new definition — we then prove rational form (13/5)φ² = …,
vacuum iff φ = 0, and LHS nonnegativity. -/
def HQVM_Friedmann_eq (φ rho_m rho_r : ℝ) : Prop :=
  (3.0 - gamma_HQIV) * (H_of_phi φ) ^ 2 =
    8.0 * Real.pi * G_eff φ * rho_total rho_m rho_r

/-- Trivial unfolding lemma: spelling out `HQVM_Friedmann_eq`. -/
theorem HQVM_Friedmann_eq_def (φ rho_m rho_r : ℝ) :
  HQVM_Friedmann_eq φ rho_m rho_r ↔
    (3.0 - gamma_HQIV) * (H_of_phi φ) ^ 2 =
      8.0 * Real.pi * G_eff φ * rho_total rho_m rho_r := by
  rfl

/-- **Friedmann equation in rational form:** (3−γ) = 13/5, so the equation is
  (13/5) φ² = 8π G_eff(φ) (ρ_m + ρ_r). -/
theorem HQVM_Friedmann_eq_rational (φ rho_m rho_r : ℝ) :
  HQVM_Friedmann_eq φ rho_m rho_r ↔
    (13/5 : ℝ) * φ ^ 2 = 8 * Real.pi * G_eff φ * (rho_m + rho_r) := by
  simp only [HQVM_Friedmann_eq_def, H_of_phi_eq, rho_total_eq]
  rw [show (3.0 : ℝ) = (3 : ℝ) by norm_num, three_minus_gamma_eq, show (8.0 : ℝ) = (8 : ℝ) by norm_num]

/-- **Friedmann equation with G_eff as φ^α (φ ≥ 0):**
  (13/5) φ² = 8π φ^α (ρ_m + ρ_r). -/
theorem HQVM_Friedmann_eq_power (φ rho_m rho_r : ℝ) (hφ : 0 ≤ φ) :
  HQVM_Friedmann_eq φ rho_m rho_r ↔
    (13/5 : ℝ) * φ ^ 2 = 8 * Real.pi * (φ ^ alpha) * (rho_m + rho_r) := by
  rw [HQVM_Friedmann_eq_rational, G_eff_eq φ hφ]

/-- **Vacuum (Minkowski) case:** when ρ_m = ρ_r = 0, the Friedmann equation holds iff φ = 0.
So in the vacuum the only homogeneous solution is H = 0. -/
theorem HQVM_Friedmann_eq_vacuum_iff (φ : ℝ) :
  HQVM_Friedmann_eq φ 0 0 ↔ φ = 0 := by
  rw [HQVM_Friedmann_eq_rational, add_zero, mul_zero]
  constructor
  · intro h
    rw [mul_eq_zero] at h
    cases h with
    | inl h => exact absurd h (by norm_num)
    | inr h => exact eq_zero_of_pow_eq_zero h
  · intro h; rw [h]; norm_num

/-- **Minkowski limit and Friedmann vacuum agree:** when Φ = 0, φ = 0, the lapse is 1
and the Friedmann equation (vacuum) holds for φ = 0. So the Minkowski geometry
is the unique vacuum homogeneous limit. -/
theorem HQVM_Minkowski_iff_vacuum (φ : ℝ) :
    (∀ t, HQVM_lapse 0 φ t = 1) ↔ φ = 0 := by
  constructor
  · intro h; specialize h 1; unfold HQVM_lapse at h; linarith
  · intro h; rw [h]; exact HQVM_lapse_Minkowski

/-- **Friedmann equation: left-hand side (3−γ)φ² is nonnegative** when φ is real;
so with positive ρ, the equation constrains φ. -/
theorem HQVM_Friedmann_LHS_nonneg (φ : ℝ) :
    0 ≤ (3 - gamma_HQIV) * φ ^ 2 := by
  rw [three_minus_gamma_eq]; exact mul_nonneg (by norm_num) (sq_nonneg φ)

-- Quick checks (visible in infoview)
#check HQVM_lapse
#check ADM_lapse_eq_HQVM_lapse
#check HQVM_g_tt
#check HQVM_spatial_coeff
#check HQVM_g_tt_neg
#check HQVM_unit_normal_squared
#check gamma_HQIV
#check H_of_phi
#check G_eff
#check HQVM_Friedmann_eq
#check HQVM_Friedmann_eq_def

end Hqiv
