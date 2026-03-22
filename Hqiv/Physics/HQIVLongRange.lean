import Mathlib.Data.Real.Basic

import Hqiv.Physics.HQIVMolecules
import Hqiv.Physics.SpinStatistics

/-!
# HQIV long-range attraction: H-bond / contact proxy from dihedral alignment

Extends `valleyPotentialEM` with an **explicit attractive contact term** built only from
vacuum-mode data (`phi_of_shell`, `availableModesNat`), horizon radii `R_m`, and dihedral
alignment factors `cos θ`, `cos φ`. The radial factor is a Lorentzian in `dist / R_hbond` —
the same `R_m` scale as `sphericalFresnelEnvelope` / `fresnelCaustic` (no empirical 1/r⁶ tail).

No new axioms: lemmas are definitional rewrites plus inequalities from existing positivity
results (`phi_of_shell_pos`, `latticeSimplexCount_pos`, `water_dielectric_rescaling_eq_EM`, …).
-/

namespace Hqiv.Physics

open Real

/-!
## 1. Vacuum-tied scale and H-bond proxy
-/

/-- Stiffness proxy: auxiliary-field shell scale per available vacuum mode (no fitted constant). -/
noncomputable def K_hbond (m : ℕ) : ℝ :=
  Hqiv.phi_of_shell m / (availableModesNat m : ℝ)

/-- Contact radius: same discrete shell radius as Fresnel / nuclear horizons. -/
noncomputable def R_hbond (m : ℕ) : ℝ :=
  R_m m

theorem R_hbond_eq_R_m (m : ℕ) : R_hbond m = R_m m :=
  rfl

theorem K_hbond_eq_omega_over_modes (m : ℕ) : K_hbond m = omegaCasimir m / (availableModesNat m : ℝ) := by
  unfold K_hbond omegaCasimir
  rfl

/-- Attractive (negative) contact / H-bond proxy from dihedral alignment and caustic overlap. -/
noncomputable def hBondProxy (m : ℕ) (θ φ dist : ℝ) : ℝ :=
  -K_hbond m * (cos θ * cos φ) / (1 + (dist / R_hbond m) ^ 2)

/-!
### Positivity of mode density scale
-/

theorem availableModesNat_pos (m : ℕ) : 0 < availableModesNat m := by
  unfold availableModesNat
  exact Nat.mul_pos (by norm_num : 0 < 4) (Hqiv.latticeSimplexCount_pos m)

theorem K_hbond_pos (m : ℕ) : 0 < K_hbond m := by
  unfold K_hbond
  have hφ : 0 < Hqiv.phi_of_shell m := Hqiv.phi_of_shell_pos m
  have hν : 0 < (availableModesNat m : ℝ) := Nat.cast_pos.mpr (availableModesNat_pos m)
  exact div_pos hφ hν

theorem R_hbond_pos (m : ℕ) : 0 < R_hbond m := by
  unfold R_hbond R_m
  linarith [Nat.cast_nonneg m]

theorem overlap_denominator_pos (m : ℕ) (dist : ℝ) : 0 < 1 + (dist / R_hbond m) ^ 2 := by
  have hsq : 0 ≤ (dist / R_hbond m) ^ 2 := sq_nonneg _
  linarith [hsq]

/-!
## 2. Caustic / Fresnel identification (same radius as `R_m`)
-/

theorem R_hbond_eq_sphericalFresnelEnvelope_radius (m : ℕ) (H : SphericalHarmonics m) (h : MetaHorizon m) :
    R_hbond m = (sphericalFresnelEnvelope H h).radius := by
  unfold R_hbond
  exact (sphericalFresnelEnvelope_radius H h).symm

/-- The proxy uses exactly the Fresnel envelope radius in the radial overlap factor. -/
theorem hBondProxy_from_caustic_overlap (m : ℕ) (θ φ dist : ℝ) (H : SphericalHarmonics m) (h : MetaHorizon m) :
    hBondProxy m θ φ dist =
      -K_hbond m * (cos θ * cos φ) / (1 + (dist / (sphericalFresnelEnvelope H h).radius) ^ 2) := by
  unfold hBondProxy
  rw [R_hbond_eq_sphericalFresnelEnvelope_radius m H h]

/-!
## 3. Augmented valley potential (EM + long-range contact)
-/

/-- Valley + EM pair potential plus explicit long-range contact proxy. -/
noncomputable def valleyPotentialLongRange (m : ℕ) (n₁ n₂ : CasimirSurface m) (Z_eff r : ℝ) (θ φ dist : ℝ) : ℝ :=
  valleyPotentialEM m n₁ n₂ Z_eff r + hBondProxy m θ φ dist

theorem valleyPotentialLongRange_def (m : ℕ) (n₁ n₂ : CasimirSurface m) (Z_eff r : ℝ) (θ φ dist : ℝ) :
    valleyPotentialLongRange m n₁ n₂ Z_eff r θ φ dist =
      valleyPotentialEM m n₁ n₂ Z_eff r + hBondProxy m θ φ dist :=
  rfl

theorem valleyPotentialLongRange_lt_EM_of_attractive_hBond {m : ℕ} {n₁ n₂ : CasimirSurface m} {Z_eff r θ φ dist : ℝ}
    (hh : hBondProxy m θ φ dist < 0) :
    valleyPotentialLongRange m n₁ n₂ Z_eff r θ φ dist < valleyPotentialEM m n₁ n₂ Z_eff r := by
  unfold valleyPotentialLongRange
  linarith [hh]

/-!
### Solvent / pH bookkeeping (EM term only; proxy unchanged)
-/

theorem water_dielectric_rescaling_long_range (ε_r : ℝ) (hε : ε_r ≠ 0) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (Z_eff r : ℝ) (θ φ dist : ℝ) :
    waterDielectricValley ε_r m n₁ n₂ Z_eff r + hBondProxy m θ φ dist =
      valleyPotentialLongRange m n₁ n₂ Z_eff (ε_r * r) θ φ dist := by
  unfold valleyPotentialLongRange waterDielectricValley
  rw [water_dielectric_rescaling_eq_EM ε_r hε]

theorem pH_charge_flip_effect_long_range (δZ Z_eff r : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m) (θ φ dist : ℝ) :
    valleyPotentialLongRange m n₁ n₂ (Z_eff + δZ) r θ φ dist =
      valleyPotentialLongRange m n₁ n₂ Z_eff r θ φ dist + Hqiv.alpha_EM_at_MZ * δZ / r := by
  unfold valleyPotentialLongRange
  rw [pH_charge_flip_effect δZ Z_eff r m n₁ n₂]

/-!
## 4. Long-range attraction (net negative proxy when cosines and scale are positive)
-/

/-- When both alignment cosines are positive and `K_hbond > 0`, the proxy is strictly attractive. -/
theorem long_range_attraction_emergent (m : ℕ) (θ φ dist : ℝ) (hθ : 0 < cos θ) (hφ : 0 < cos φ) :
    hBondProxy m θ φ dist < 0 := by
  unfold hBondProxy
  have hK : 0 < K_hbond m := K_hbond_pos m
  have hnum : 0 < cos θ * cos φ := mul_pos hθ hφ
  have hden : 0 < 1 + (dist / R_hbond m) ^ 2 := overlap_denominator_pos m dist
  have hpos : 0 < K_hbond m * (cos θ * cos φ) / (1 + (dist / R_hbond m) ^ 2) :=
    div_pos (mul_pos hK hnum) hden
  linarith [hpos]

/-!
### Optional hydrophobic distance window (symbolic positivity of the overlap factor)
-/

theorem hydrophobic_overlap_factor_pos (m : ℕ) (dist : ℝ) : 0 < 1 + (dist / R_hbond m) ^ 2 :=
  overlap_denominator_pos m dist

/-!
## 5. Native fold: dihedral additive constant (H-bond proxy does not change the θ-fold argmin)
-/

theorem augmented_minimum_energy_fold_is_native {m : ℕ} (κ θFold Z_eff r μ c : ℝ) (hb : ℝ) (t : TorqueTree m)
    (hκ : κ ≠ 0) :
    foldEnergyWithDihedral κ θFold Z_eff r μ c t + hb =
        foldEnergy Z_eff r μ c t + hb ↔ cos θFold = 1 := by
  unfold foldEnergyWithDihedral
  constructor
  · intro h
    have hdiff := congr_arg (fun z => z - foldEnergy Z_eff r μ c t - hb) h
    simp [add_assoc, add_sub_cancel_right] at hdiff
    have h1 : 1 - cos θFold = 0 := by
      cases (mul_eq_zero.mp hdiff) with
      | inl hκ0 => exact absurd hκ0 hκ
      | inr h1 => exact h1
    have : cos θFold = 1 := by linarith [h1]
    exact this
  · intro hcos
    have h1 : 1 - cos θFold = 0 := by rw [hcos]; simp
    simp [h1, add_assoc]

/-!
## 6. Multibody attachment bookkeeping (H-bond vs covalent tag)
-/

inductive MultibodyAttachment : Type
  | hBond {Z₁ e₁ Z₂ e₂ : ℕ} : AtomicSurface Z₁ e₁ → AtomicSurface Z₂ e₂ → ℝ → ℝ → MultibodyAttachment
  | covalent {Z₁ e₁ Z₂ e₂ : ℕ} : AtomicSurface Z₁ e₁ → AtomicSurface Z₂ e₂ → MultibodyAttachment

/-- Dihedral penalty vanishes (pole cancellation). -/
def PoleCancellation (κ θ : ℝ) : Prop :=
  κ * (1 - cos θ) = 0

/-- Saturated valley overlap identity between equal-shell caustics (`HQIVNuclei`). -/
def ValleySaturation (m : ℕ) (n₁ n₂ : CasimirSurface m) : Prop :=
  valleyPotential n₁ n₂ = -(R_m m * R_m m)

theorem valley_saturation_always (m : ℕ) (n₁ n₂ : CasimirSurface m) : ValleySaturation m n₁ n₂ :=
  valleyPotential_neg_overlap n₁ n₂

theorem resonance_half_life_pos {ΔE : ℝ} (hΔ : 0 < ΔE) : 0 < resonance_half_life ΔE := by
  unfold resonance_half_life
  exact mul_pos (Real.log_pos (by norm_num : (1 : ℝ) < 2)) (resonance_lifetime_pos hΔ)

/-- Covalent / coordination tags inherit valley saturation and finite overlap half-life at any `ΔE > 0`. -/
theorem multibody_ligand_covalent_constraints (ΔE : ℝ) (hΔ : 0 < ΔE) (κ θ : ℝ) (m : ℕ) (n₁ n₂ : CasimirSurface m)
    (hθ : θ = 0) :
    PoleCancellation κ θ ∧ ValleySaturation m n₁ n₂ ∧
      (∃ τ : ℝ, τ = resonance_half_life ΔE ∧ 0 < τ) := by
  refine ⟨?_, valley_saturation_always m n₁ n₂, ?_⟩
  · unfold PoleCancellation
    rw [hθ, Real.cos_zero]
    simp
  · refine ⟨resonance_half_life ΔE, rfl, resonance_half_life_pos hΔ⟩

/-!
## 7. CASP-style symbolic bridge (energy strictly improves when the proxy is attractive)
-/

theorem casp_long_range_energy_improvement {m : ℕ} {n₁ n₂ : CasimirSurface m} {Z_eff r θ φ dist : ℝ}
    (hh : hBondProxy m θ φ dist < 0) :
    valleyPotentialLongRange m n₁ n₂ Z_eff r θ φ dist < valleyPotentialEM m n₁ n₂ Z_eff r :=
  valleyPotentialLongRange_lt_EM_of_attractive_hBond hh

/-- Spectral anchor: deuteron binding scale is positive (same witness as `HQIVMolecules` / `HQIVNuclei`). -/
theorem casp_spectral_anchor_pos : 0 < spectraDeuteronBinding_MeV := by
  unfold spectraDeuteronBinding_MeV
  norm_num

end Hqiv.Physics
