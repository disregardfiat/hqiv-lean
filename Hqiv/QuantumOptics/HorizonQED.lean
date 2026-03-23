import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Horizon-lattice quantum optics (QED scaffolding)

This file formalises the **discrete shell layer** of single-mode and two-level quantum
optics that is tied to the HQIV null lattice (`OctonionicLightCone`) and the
temperature ladder (`AuxiliaryField`). It does **not** import a full Fock space;
instead we prove:

1. **Shell combinatorics** for spatial mode labels (`latticeSimplexCount`).
2. **Frequency tags** from the ladder: \(\tilde\omega_m := T(m)/T_{\mathrm{Pl}}\).
3. **Scalar QED normalisation** (single-mode electric-field amplitude coefficient).
4. **Pauli / pseudospin algebra** for the two-level atom sector (Jaynes–Cummings matter).
5. **Positivity** of vacuum zero-point energy contributions and coupling tags.

Lean sources of truth: `OctonionicLightCone.lean`, `AuxiliaryField.lean`.
-/

open scoped BigOperators

namespace Hqiv.QuantumOptics

open Hqiv

/-- Spatial mode multiplicity on shell `m` (stars-and-bars numerator). -/
def shellSpatialModeCount (m : ℕ) : ℕ :=
  latticeSimplexCount m

theorem shellSpatialModeCount_eq (m : ℕ) :
    shellSpatialModeCount m = (m + 2) * (m + 1) := by
  simp [shellSpatialModeCount, latticeSimplexCount_eq]

theorem shellSpatialModeCount_pos (m : ℕ) : 0 < shellSpatialModeCount m := by
  simpa [shellSpatialModeCount] using latticeSimplexCount_pos m

/-- Dimensionless angular-frequency tag \(\tilde\omega_m := T(m) / T_{\mathrm{Pl}}\). -/
noncomputable def dimensionlessOmegaShell (m : ℕ) : ℝ :=
  T m / T_Pl

theorem dimensionlessOmegaShell_eq (m : ℕ) :
    dimensionlessOmegaShell m = 1 / (m + 1 : ℝ) := by
  unfold dimensionlessOmegaShell
  rw [T_eq m, T_Pl_eq]
  field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)]

theorem dimensionlessOmegaShell_pos (m : ℕ) : 0 < dimensionlessOmegaShell m := by
  rw [dimensionlessOmegaShell_eq m]
  positivity

/-- SI angular frequency \(\omega_m = k_B T(m) / \hbar\) (bridge from ladder temperature). -/
noncomputable def omegaShellSI (m : ℕ) (kB hbar : ℝ) : ℝ :=
  kB * T m / hbar

/-- Single-mode zero-point energy \(\tfrac12 \hbar \omega\) with \(\omega = k_B T/\hbar\). -/
noncomputable def zeroPointEnergyShellSI (m : ℕ) (kB hbar : ℝ) : ℝ :=
  (1 / 2 : ℝ) * hbar * omegaShellSI m kB hbar

theorem zeroPointEnergyShellSI_eq (m : ℕ) (kB hbar : ℝ) (hhbar : hbar ≠ 0) :
    zeroPointEnergyShellSI m kB hbar = (1 / 2 : ℝ) * kB * T m := by
  unfold zeroPointEnergyShellSI omegaShellSI
  field_simp [hhbar]

theorem zeroPointEnergyShellSI_pos (m : ℕ) (kB hbar : ℝ)
    (hkB : 0 < kB) (hhbar : 0 < hbar) : 0 < zeroPointEnergyShellSI m kB hbar := by
  rw [zeroPointEnergyShellSI_eq m kB hbar (ne_of_gt hhbar)]
  have hT : 0 < T m := T_pos m
  have : 0 < (1 / 2 : ℝ) * kB * T m := by
    have h2 : 0 < (1 / 2 : ℝ) := by norm_num
    exact mul_pos (mul_pos h2 hkB) hT
  simpa [mul_assoc] using this

/-- Truncated vacuum zero-point sum \(\sum_{m=0}^{M-1} N_m \cdot \tfrac12 k_B T(m)\)
with \(N_m = \) `shellSpatialModeCount m`. -/
noncomputable def truncatedVacuumZeroPointSI (M : ℕ) (kB : ℝ) : ℝ :=
  ∑ m ∈ Finset.range M, (shellSpatialModeCount m : ℝ) * ((1 / 2 : ℝ) * kB * T m)

theorem truncatedVacuumZeroPointSI_nonneg (M : ℕ) (kB : ℝ) (hkB : 0 ≤ kB) :
    0 ≤ truncatedVacuumZeroPointSI M kB := by
  unfold truncatedVacuumZeroPointSI
  refine Finset.sum_nonneg ?_
  intro m _
  have hTm : 0 ≤ T m := le_of_lt (T_pos m)
  have hNm : 0 ≤ (shellSpatialModeCount m : ℝ) := Nat.cast_nonneg _
  refine mul_nonneg hNm ?_
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  exact mul_nonneg (mul_nonneg hhalf hkB) hTm

/-!
## Single-mode electric-field quantisation coefficient (scalar QED layer)

\[
  \mathcal{E}_m := \sqrt{\frac{\hbar \omega_m}{2 \varepsilon_0 V}} .
\]
-/

noncomputable def fieldQuantizationPrefactorSI (m : ℕ) (kB hbar epsilon0 V : ℝ) : ℝ :=
  Real.sqrt (hbar * omegaShellSI m kB hbar / (2 * epsilon0 * V))

theorem fieldQuantizationPrefactorSI_nonneg (m : ℕ) (kB hbar epsilon0 V : ℝ)
    (hkB : 0 < kB) (hhbar : 0 < hbar) (heps : 0 < epsilon0) (hV : 0 < V) :
    0 ≤ fieldQuantizationPrefactorSI m kB hbar epsilon0 V := by
  unfold fieldQuantizationPrefactorSI
  have hω : 0 < omegaShellSI m kB hbar := by
    unfold omegaShellSI
    have hT : 0 < T m := T_pos m
    positivity
  have hnum : 0 < hbar * omegaShellSI m kB hbar := mul_pos hhbar hω
  have hden : 0 < 2 * epsilon0 * V := by positivity
  exact Real.sqrt_nonneg _

theorem fieldQuantizationPrefactorSI_pos (m : ℕ) (kB hbar epsilon0 V : ℝ)
    (hkB : 0 < kB) (hhbar : 0 < hbar) (heps : 0 < epsilon0) (hV : 0 < V) :
    0 < fieldQuantizationPrefactorSI m kB hbar epsilon0 V := by
  unfold fieldQuantizationPrefactorSI
  have hω : 0 < omegaShellSI m kB hbar := by
    unfold omegaShellSI
    exact div_pos (mul_pos hkB (T_pos m)) hhbar
  have hnum : 0 < hbar * omegaShellSI m kB hbar := mul_pos hhbar hω
  have hden : 0 < 2 * epsilon0 * V := by positivity
  have hfrac : 0 < hbar * omegaShellSI m kB hbar / (2 * epsilon0 * V) := by
    exact div_pos hnum hden
  exact Real.sqrt_pos.mpr hfrac

/-!
## Two-level (Pauli) algebra for Jaynes–Cummings matter

\[
  \sigma^+ = \begin{pmatrix} 0 & 1 \\ 0 & 0 \end{pmatrix},\quad
  \sigma^- = \begin{pmatrix} 0 & 0 \\ 1 & 0 \end{pmatrix},\quad
  \sigma_z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}.
\]
-/

open Matrix Complex

/-- \(\sigma^+\) (excitation). -/
def sigmaPlus : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(0 : ℂ), (1 : ℂ)], ![(0 : ℂ), (0 : ℂ)]]

/-- \(\sigma^-\) (de-excitation). -/
def sigmaMinus : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(0 : ℂ), (0 : ℂ)], ![(1 : ℂ), (0 : ℂ)]]

/-- \(\sigma_z\). -/
def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(1 : ℂ), (0 : ℂ)], ![(0 : ℂ), (-1 : ℂ)]]

theorem commutator_sigma_plus_sigmaMinus : sigmaPlus * sigmaMinus - sigmaMinus * sigmaPlus = sigmaZ := by
  ext i j
  simp_rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaMinus, sigmaZ, Finset.sum_range_succ, Finset.sum_range_zero] <;>
    norm_num

theorem commutator_sigmaZ_sigmaPlus : sigmaZ * sigmaPlus - sigmaPlus * sigmaZ = (2 : ℂ) • sigmaPlus := by
  ext i j
  simp_rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
  fin_cases i <;> fin_cases j <;>
    simp [sigmaPlus, sigmaZ, Finset.sum_range_succ, Finset.sum_range_zero, smul_eq_mul] <;>
    norm_num

theorem commutator_sigmaZ_sigmaMinus : sigmaZ * sigmaMinus - sigmaMinus * sigmaZ = (-2 : ℂ) • sigmaMinus := by
  ext i j
  simp_rw [Matrix.sub_apply, Matrix.mul_apply, Finset.sum_fin_eq_sum_range]
  fin_cases i <;> fin_cases j <;>
    simp [sigmaMinus, sigmaZ, Finset.sum_range_succ, Finset.sum_range_zero, smul_eq_mul] <;>
    norm_num

/-!
## Jaynes–Cummings coupling tag (scalar, from ladder scalars)

We record the **positive** scalar \(g_{\mathrm{tag}}(m) := \sqrt{T(m)\,\varphi(m)}\) with
\(\varphi(m)=2/T(m)\) so \(g_{\mathrm{tag}}(m)=\sqrt{2}\) in natural units. This is the
unique parameter-free square-root tag linking the temperature ladder and auxiliary field.
-/

noncomputable def jcCouplingTag (m : ℕ) : ℝ :=
  Real.sqrt (T m * phi_of_shell m)

theorem jcCouplingTag_eq_sqrt_two (m : ℕ) : jcCouplingTag m = Real.sqrt 2 := by
  unfold jcCouplingTag
  have h : T m * phi_of_shell m = 2 := by
    -- φ = 2/T ⇒ T * φ = 2
    have hphi : phi_of_shell m = 2 / T m := by
      unfold phi_of_shell phiTemperatureCoeff
      field_simp [ne_of_gt (T_pos m)]
    rw [hphi]
    field_simp [ne_of_gt (T_pos m)]
  rw [h]

theorem jcCouplingTag_pos (m : ℕ) : 0 < jcCouplingTag m := by
  rw [jcCouplingTag_eq_sqrt_two m]
  exact Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)

/-- On-resonance Rabi angular frequency \(\Omega = 2g\) for a scalar coupling \(g\). -/
noncomputable def rabiAngularFrequency (g : ℝ) : ℝ :=
  2 * g

theorem rabiAngularFrequency_pos (g : ℝ) (hg : 0 < g) : 0 < rabiAngularFrequency g := by
  unfold rabiAngularFrequency
  linarith

/-!
## Lindblad dissipator (scalar rate)

Jump operators live in the full operator algebra; here we only fix a **non-negative**
scalar rate \(\gamma\) as in the Lindblad generator.
-/

noncomputable def lindbladScalarRate (gamma : ℝ) : ℝ :=
  gamma

theorem lindbladScalarRate_nonneg (gamma : ℝ) (hγ : 0 ≤ gamma) : 0 ≤ lindbladScalarRate gamma :=
  hγ

end Hqiv.QuantumOptics
