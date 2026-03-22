import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.Topology.Order

import Hqiv.Geometry.HQVMDiscreteLaplacian
import Hqiv.Geometry.HQVMCLASSBridge

namespace Hqiv

open Filter Real
open scoped Topology

/-!
# Discrete Poisson / Hamiltonian-constraint bookkeeping (axis stencil)

This file is the **next link** after `Hqiv.Geometry.HQVMDiscreteLaplacian`: we package the
7-point axis-aligned discrete Laplacian as a **pointwise Poisson-type constraint** between a scalar
potential on `ObserverChart` and a density source, using the same `G_eff φ` factor as the schematic
Fourier statement `HQVM_singleMode_Poisson` in `Hqiv.Geometry.HQVMCLASSBridge`.

**No time derivatives** appear: everything is evaluated on a fixed spatial chart (a single slice).
There is **no full 3D wavevector** `k⃗` — only the separable toy `HQVM_cosModeOnAxis` from the
Laplacian module. **No** weighting by `HQVM_spatial_coeff` (curved-slice Laplace–Beltrami) is
asserted.

**Extends:** `HQVMDiscreteLaplacian` (operator, `HQVM_cosModeOnAxis` eigen-calculation);
`HQVMCLASSBridge` (schematic `HQVM_singleMode_Poisson`). Ball averaging of chart fields (no claimed
equivalence yet) is in `Hqiv.Geometry.HQVMGlobalLocalDictionary`.

**Lemma trail:** range-scalar linearity of the stencil (`HQVM_discreteLaplacian_smul`) mirrors
`HQVM_rawSecondDiffAlong_add` / `HQVM_discreteLaplacian_comp_smul` (domain scaling). The Poisson
predicate `HQVM_discretePoissonAt` is the discrete analogue of the **algebraic shape**
`k² δΦ = 4π G_eff δρ`, with the Fourier multiplier replaced by the discrete Helmholtz symbol
`2(cos(kh)−1)/h²` on cosine modes. `HQVM_discreteHelmholtz_symbol_eq_neg_k_sq_sinc_sq` rewrites that
symbol as `−k² sinc²(kh/2)` and yields the `h → 0` limit `→ −k²` via continuity of `Real.sinc`
(`Hqiv.Geometry.HQVMDiscretePoisson` / Mathlib `Real.continuous_sinc`), aligning the **sign** with the
standard continuum identity `Δ cos(k·x) = −k² cos(k·x)` while the legacy scalar definition
`HQVM_singleMode_Poisson` keeps a **plus** `k²` on the left (documented mismatch; see
`HQVM_discretePoisson_singleMode_vs_schematic_sign`).

**What is still not claimed (explicit):** a full Bardeen / Newtonian gauge story; photon polarization
or Boltzmann hierarchy sources; multiplying the discrete Laplacian by `HQVM_spatial_coeff` or
otherwise encoding a curved-slice Laplace–Beltrami operator; a theorem identifying this 7-point
stencil with a continuum limit on a dynamical HQVM spatial metric; any file-level or array-level
match to CLASS `perturbs` output.
-/

section StencilLinearity

variable {h : ℝ} {f g : ObserverChart → ℝ} {x : ObserverChart}

theorem HQVM_rawSecondDiffAlong_smul (c : ℝ) (i : Fin 3) :
    HQVM_rawSecondDiffAlong h (fun y => c * f y) x i =
      c * HQVM_rawSecondDiffAlong h f x i := by
  dsimp [HQVM_rawSecondDiffAlong]
  ring

theorem HQVM_rawSecondDiff_sum_smul (c : ℝ) :
    HQVM_rawSecondDiff_sum h (fun y => c * f y) x =
      c * HQVM_rawSecondDiff_sum h f x := by
  simp [HQVM_rawSecondDiff_sum, Finset.mul_sum, HQVM_rawSecondDiffAlong_smul]

theorem HQVM_discreteLaplacian_smul (c : ℝ) (hh : h ≠ 0) :
    HQVM_discreteLaplacian h (fun y => c * f y) x =
      c * HQVM_discreteLaplacian h f x := by
  unfold HQVM_discreteLaplacian
  rw [HQVM_rawSecondDiff_sum_smul]
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  field_simp [hh2]

theorem HQVM_discreteLaplacian_add (f g : ObserverChart → ℝ) (hh : h ≠ 0) :
    HQVM_discreteLaplacian h (fun y => f y + g y) x =
      HQVM_discreteLaplacian h f x + HQVM_discreteLaplacian h g x := by
  simp only [HQVM_discreteLaplacian, HQVM_rawSecondDiff_sum_add]
  have hh2 : h ^ 2 ≠ 0 := pow_ne_zero 2 hh
  field_simp [hh2]

end StencilLinearity

section PotentialAndPredicate

/-- Slice potential entering the Poisson stencil: Newtonian fluctuation `δΦ` plus the `t δφ` term
from `linearizedHQVM_lapse` (`Hqiv.Geometry.HQVMPerturbations`), **without** the `φ δt` gauge piece
and without any time derivative — `t` is a fixed background time coordinate on the slice. -/
def HQVM_discretePoisson_potential (t_bg : ℝ) (δΦ δφ : ObserverChart → ℝ) : ObserverChart → ℝ :=
  fun x => δΦ x + t_bg * δφ x

theorem HQVM_discretePoisson_potential_add (t_bg : ℝ) (δΦ₁ δΦ₂ δφ₁ δφ₂ : ObserverChart → ℝ) :
    HQVM_discretePoisson_potential t_bg (fun x => δΦ₁ x + δΦ₂ x) (fun x => δφ₁ x + δφ₂ x) =
      (fun x =>
        HQVM_discretePoisson_potential t_bg δΦ₁ δφ₁ x + HQVM_discretePoisson_potential t_bg δΦ₂ δφ₂ x) := by
  funext x
  dsimp [HQVM_discretePoisson_potential]
  ring

/-- Pointwise discrete Poisson constraint: `Δ_h Ψ = 4π G_eff(φ) S`. No spatial_coeff weighting. -/
def HQVM_discretePoissonAt (h : ℝ) (φ : ℝ) (Ψ S : ObserverChart → ℝ) (x : ObserverChart) : Prop :=
  HQVM_discreteLaplacian h Ψ x = 4 * Real.pi * G_eff φ * S x

/-- Chart-wide discrete Poisson: the same constraint at every `x : ObserverChart`. -/
def HQVM_discretePoisson (h : ℝ) (φ : ℝ) (Ψ S : ObserverChart → ℝ) : Prop :=
  ∀ x, HQVM_discretePoissonAt h φ Ψ S x

theorem HQVM_discretePoissonAt_add (h : ℝ) (φ : ℝ) (Ψ₁ Ψ₂ S₁ S₂ : ObserverChart → ℝ) (x : ObserverChart)
    (hh : h ≠ 0)
    (h₁ : HQVM_discretePoissonAt h φ Ψ₁ S₁ x) (h₂ : HQVM_discretePoissonAt h φ Ψ₂ S₂ x) :
    HQVM_discretePoissonAt h φ (fun y => Ψ₁ y + Ψ₂ y) (fun y => S₁ y + S₂ y) x := by
  dsimp [HQVM_discretePoissonAt] at h₁ h₂ ⊢
  rw [HQVM_discreteLaplacian_add Ψ₁ Ψ₂ hh, h₁, h₂]
  ring

theorem HQVM_discretePoissonAt_smul (h : ℝ) (φ : ℝ) (c : ℝ) (Ψ S : ObserverChart → ℝ) (x : ObserverChart)
    (hh : h ≠ 0) (hP : HQVM_discretePoissonAt h φ Ψ S x) :
    HQVM_discretePoissonAt h φ (fun y => c * Ψ y) (fun y => c * S y) x := by
  dsimp [HQVM_discretePoissonAt] at hP ⊢
  rw [HQVM_discreteLaplacian_smul c hh, hP]
  ring

theorem HQVM_discretePoisson_iff_forall (h φ Ψ S) :
    HQVM_discretePoisson h φ Ψ S ↔ ∀ x, HQVM_discretePoissonAt h φ Ψ S x :=
  Iff.rfl

end PotentialAndPredicate

section HelmholtzSymbol

/-- Discrete Helmholtz symbol on an axis-aligned cosine (eigenvalue of `Δ_h` on `cos(k x_{i₀})`). -/
noncomputable def HQVM_discreteHelmholtz_symbol (h k : ℝ) : ℝ :=
  2 * (cos (k * h) - 1) / h ^ 2

theorem HQVM_discreteHelmholtz_symbol_eq_of_h_eq_zero (k : ℝ) : HQVM_discreteHelmholtz_symbol 0 k = 0 := by
  simp [HQVM_discreteHelmholtz_symbol]

/-- Algebraic bridge to `HQVM_singleMode_Poisson`: same **bilinear** shape, Fourier multiplier
replaced by `HQVM_discreteHelmholtz_symbol`. -/
def HQVM_discrete_singleMode_Poisson (h k φ A B : ℝ) : Prop :=
  HQVM_discreteHelmholtz_symbol h k * A = 4 * Real.pi * G_eff φ * B

theorem HQVM_discrete_singleMode_Poisson_of_h_eq_zero (k φ A B : ℝ) :
    HQVM_discrete_singleMode_Poisson 0 k φ A B ↔ 4 * Real.pi * G_eff φ * B = 0 := by
  simp [HQVM_discrete_singleMode_Poisson, HQVM_discreteHelmholtz_symbol_eq_of_h_eq_zero]

/-- The legacy schematic `k² δΦ` side differs by a **sign** from the continuum Laplacian eigenvalue
`−k²` on `cos(kx)`; the discrete symbol tends to `−k²` as `h → 0` (`tendsto_HQVM_discreteHelmholtz_symbol`). -/
theorem HQVM_discretePoisson_singleMode_vs_schematic_sign (k φ A B : ℝ) :
    HQVM_singleMode_Poisson k φ A B ↔ HQVM_singleMode_Poisson k φ (-A) (-B) := by
  simp only [HQVM_singleMode_Poisson]
  constructor <;> intro h <;> linarith

end HelmholtzSymbol

section SincExtensionAndLimit

/-- Continuous extension of the discrete Helmholtz symbol: `2(cos(kh)−1)/h² = −k² sinc²(kh/2)` for
`h ≠ 0`, and the right-hand side is continuous at `h = 0`. -/
theorem HQVM_discreteHelmholtz_symbol_eq_neg_k_sq_sinc_sq (k h : ℝ) :
    (if h = 0 then -(k ^ 2) else HQVM_discreteHelmholtz_symbol h k) =
      -(k ^ 2 * Real.sinc (k * h / 2) ^ 2) := by
  split_ifs with hh
  · subst hh
    simp [Real.sinc_zero]
  · dsimp [HQVM_discreteHelmholtz_symbol]
    by_cases hk : k = 0
    · subst hk
      simp
    have hk2 : k * h / 2 ≠ 0 := by
      intro hz
      have : k * h = 0 := by linarith [hz]
      cases mul_eq_zero.mp this with
      | inl hkl => exact hk hkl
      | inr hhr => exact hh hhr
    have hsinc : Real.sinc (k * h / 2) = sin (k * h / 2) / (k * h / 2) :=
      Real.sinc_of_ne_zero hk2
    have hcos :
        cos (k * h) - 1 = -2 * sin (k * h / 2) ^ 2 := by
      have hk' : k * h = 2 * (k * h / 2) := by ring
      rw [hk', cos_two_mul]
      have hsq := sin_sq_add_cos_sq (k * h / 2)
      have hcos2 : cos (k * h / 2) ^ 2 = 1 - sin (k * h / 2) ^ 2 := by linarith [hsq]
      rw [hcos2]
      ring_nf
    rw [hcos, hsinc]
    field_simp [hh, hk]

theorem HQVM_discreteHelmholtz_sinc_extension (k h : ℝ) :
    -(k ^ 2 * Real.sinc (k * h / 2) ^ 2) =
      (if h = 0 then -(k ^ 2) else HQVM_discreteHelmholtz_symbol h k) := by
  simpa [eq_comm] using (HQVM_discreteHelmholtz_symbol_eq_neg_k_sq_sinc_sq k h).symm

theorem continuous_HQVM_discreteHelmholtz_sinc (k : ℝ) :
    Continuous fun h : ℝ => -(k ^ 2 * Real.sinc (k * h / 2) ^ 2) := by
  fun_prop

theorem continuous_HQVM_discreteHelmholtz_symbol_extension (k : ℝ) :
    Continuous fun h : ℝ =>
      (if h = 0 then -(k ^ 2) else HQVM_discreteHelmholtz_symbol h k) := by
  simpa [HQVM_discreteHelmholtz_sinc_extension] using continuous_HQVM_discreteHelmholtz_sinc k

theorem tendsto_HQVM_discreteHelmholtz_symbol (k : ℝ) :
    Tendsto (fun h : ℝ => if h = 0 then -(k ^ 2) else HQVM_discreteHelmholtz_symbol h k) (𝓝 0)
        (𝓝 (-(k ^ 2))) := by
  have hval :
      (fun h : ℝ => if h = 0 then -(k ^ 2) else HQVM_discreteHelmholtz_symbol h k) =
        fun h : ℝ => -(k ^ 2 * Real.sinc (k * h / 2) ^ 2) := by
    funext h
    exact (HQVM_discreteHelmholtz_sinc_extension k h).symm
  rw [hval]
  convert (continuous_HQVM_discreteHelmholtz_sinc k).tendsto (0 : ℝ) using 1
  simp [Real.sinc_zero]

end SincExtensionAndLimit

section CosModePoisson

variable {i₀ : Fin 3} {k h φ A B : ℝ} {x : ObserverChart}

/-- Discrete Laplacian on an amplitude-scaled axis cosine; extends
`HQVM_discreteLaplacian_cosModeOnAxis` in `HQVMDiscreteLaplacian`. -/
theorem HQVM_discreteLaplacian_cosModeOnAxis_smul (hh : h ≠ 0) :
    HQVM_discreteLaplacian h (fun y => A * HQVM_cosModeOnAxis i₀ k y) x =
      HQVM_discreteHelmholtz_symbol h k * (A * HQVM_cosModeOnAxis i₀ k x) := by
  calc
    HQVM_discreteLaplacian h (fun y => A * HQVM_cosModeOnAxis i₀ k y) x
        = A * HQVM_discreteLaplacian h (HQVM_cosModeOnAxis i₀ k) x :=
      HQVM_discreteLaplacian_smul A hh
    _ = A * (2 * cos (k * x i₀) * (cos (k * h) - 1) / h ^ 2) := by
      rw [HQVM_discreteLaplacian_cosModeOnAxis i₀ k h x hh]
    _ = HQVM_discreteHelmholtz_symbol h k * (A * HQVM_cosModeOnAxis i₀ k x) := by
      dsimp [HQVM_discreteHelmholtz_symbol, HQVM_cosModeOnAxis]
      ring

theorem HQVM_discretePoissonAt_cosMode_iff_of_cos_ne_zero (hh : h ≠ 0)
    (hx : cos (k * x i₀) ≠ 0) :
    HQVM_discretePoissonAt h φ (fun y => A * HQVM_cosModeOnAxis i₀ k y)
        (fun y => B * HQVM_cosModeOnAxis i₀ k y) x ↔
      HQVM_discrete_singleMode_Poisson h k φ A B := by
  dsimp [HQVM_discretePoissonAt, HQVM_discrete_singleMode_Poisson]
  rw [HQVM_discreteLaplacian_cosModeOnAxis_smul hh]
  constructor
  · intro hP
    exact
      mul_right_cancel₀ hx
        (calc
          HQVM_discreteHelmholtz_symbol h k * A * cos (k * x i₀)
              = HQVM_discreteHelmholtz_symbol h k * (A * cos (k * x i₀)) := by ring
          _ = 4 * Real.pi * G_eff φ * (B * cos (k * x i₀)) := hP
          _ = 4 * Real.pi * G_eff φ * B * cos (k * x i₀) := by ring)
  · intro hP
    calc
      HQVM_discreteHelmholtz_symbol h k * (A * HQVM_cosModeOnAxis i₀ k x)
          = HQVM_discreteHelmholtz_symbol h k * A * HQVM_cosModeOnAxis i₀ k x := by ring
      _ = 4 * Real.pi * G_eff φ * B * HQVM_cosModeOnAxis i₀ k x := by rw [hP]
      _ = 4 * Real.pi * G_eff φ * (B * HQVM_cosModeOnAxis i₀ k x) := by ring

theorem HQVM_discretePoissonAt_cosMode_of_singleMode (hh : h ≠ 0)
    (hmode : HQVM_discrete_singleMode_Poisson h k φ A B) :
    HQVM_discretePoissonAt h φ (fun y => A * HQVM_cosModeOnAxis i₀ k y)
      (fun y => B * HQVM_cosModeOnAxis i₀ k y) x := by
  dsimp [HQVM_discretePoissonAt]
  rw [HQVM_discreteLaplacian_cosModeOnAxis_smul hh]
  calc
    HQVM_discreteHelmholtz_symbol h k * (A * HQVM_cosModeOnAxis i₀ k x)
        = HQVM_discreteHelmholtz_symbol h k * A * HQVM_cosModeOnAxis i₀ k x := by ring
    _ = 4 * Real.pi * G_eff φ * B * HQVM_cosModeOnAxis i₀ k x := by rw [hmode]
    _ = 4 * Real.pi * G_eff φ * (B * HQVM_cosModeOnAxis i₀ k x) := by ring

theorem HQVM_discretePoisson_cosMode_of_singleMode (i₀ : Fin 3) (k h φ A B : ℝ) (hh : h ≠ 0)
    (hmode : HQVM_discrete_singleMode_Poisson h k φ A B) :
    HQVM_discretePoisson h φ (fun y => A * HQVM_cosModeOnAxis i₀ k y)
      (fun y => B * HQVM_cosModeOnAxis i₀ k y) := by
  intro x
  exact HQVM_discretePoissonAt_cosMode_of_singleMode hh hmode

end CosModePoisson

section HomogeneousSpatial

variable {h : ℝ} {φ : ℝ} {Ψ S : ObserverChart → ℝ} {x : ObserverChart} {c : ℝ}

theorem HQVM_rawSecondDiffAlong_const (i : Fin 3) :
    HQVM_rawSecondDiffAlong h (fun _ : ObserverChart => c) x i = 0 := by
  dsimp [HQVM_rawSecondDiffAlong]
  ring

theorem HQVM_discreteLaplacian_const (_hh : h ≠ 0) :
    HQVM_discreteLaplacian h (fun _ : ObserverChart => c) x = 0 := by
  simp [HQVM_discreteLaplacian, HQVM_rawSecondDiff_sum, HQVM_rawSecondDiffAlong_const]

theorem HQVM_discretePoissonAt_const_source_zero (hh : h ≠ 0) :
    HQVM_discretePoissonAt h φ (fun _ => c) (fun _ => 0) x := by
  simp [HQVM_discretePoissonAt, HQVM_discreteLaplacian_const hh]

theorem HQVM_discretePoissonAt_const_iff (hh : h ≠ 0)
    (hG : G_eff φ ≠ 0) :
    HQVM_discretePoissonAt h φ (fun _ => c) S x ↔ S x = 0 := by
  dsimp [HQVM_discretePoissonAt]
  rw [HQVM_discreteLaplacian_const hh]
  have h4π : 4 * Real.pi * G_eff φ ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (ne_of_gt Real.pi_pos)) hG
  constructor
  · intro hp
    exact (mul_eq_zero.mp (Eq.symm hp)).resolve_left h4π
  · intro hs
    simp [hs]

end HomogeneousSpatial

end Hqiv
