import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.Abel

import Hqiv.Geometry.AuxiliaryField

/-!
# Rapidity, Minkowski 1+1 structure, and a toy calibration link to φ

**Layer 1 — metric and pairing:** `minkowskiMetric11 = diag(-1,1)` and the bilinear pairing
`minkowskiInner11`. Boosts preserve **the full inner product** (polarization from the quadratic
invariant), hence preserve **nullness**.

**Layer 2 — rapidity group:** `Λ(η)Λ(ξ) = Λ(η+ξ)`, `Λ(0) = I`, `Λ(η)Λ(-η) = I`.

**Layer 3 — HQIV φ:** only the algebraic identity `phi_of_T T · T = phiTemperatureCoeff` (no boost law).

**Not claimed:** discrete null-lattice equivalence across charts without extra φ-embedding data.
See `Hqiv.Geometry.HQVMMinkowskiSubstrate` for how the **HQVM Minkowski limit** (`N = 1`) sits next to
this flat 1+1 Lorentz substrate (without identifying `timeAngle` with rapidity).
-/

namespace Hqiv.Geometry

open Hqiv Matrix Real
open scoped Matrix

/-- Minkowski metric `diag(-1, 1)` in 1+1 (`c = 1`). -/
noncomputable def minkowskiMetric11 : Matrix (Fin 2) (Fin 2) ℝ :=
  !![(-1 : ℝ), 0; 0, 1]

/-- Minkowski inner product `⟨u,v⟩ = -u₀v₀ + u₁v₁` as `u ⬝ᵥ (g *ᵥ v)`. -/
noncomputable def minkowskiInner11 (u v : Fin 2 → ℝ) : ℝ :=
  dotProduct u (minkowskiMetric11 *ᵥ v)

theorem minkowskiInner11_eq (u v : Fin 2 → ℝ) :
    minkowskiInner11 u v = -(u 0) * (v 0) + (u 1) * (v 1) := by
  simp [minkowskiInner11, dotProduct, minkowskiMetric11, mulVec, Fin.sum_univ_two]

/-- Associated quadratic form `Q(v) = ⟨v,v⟩`. -/
noncomputable def minkowskiSq11 (v : Fin 2 → ℝ) : ℝ :=
  -(v 0) ^ 2 + (v 1) ^ 2

theorem minkowskiSq11_eq_inner (v : Fin 2 → ℝ) : minkowskiSq11 v = minkowskiInner11 v v := by
  simp [minkowskiSq11, minkowskiInner11_eq, sq]

/-- Polarization identity in 1+1 (characteristic ≠ 2). -/
theorem minkowski_polarization (u v : Fin 2 → ℝ) :
    2 * minkowskiInner11 u v = minkowskiSq11 (u + v) - minkowskiSq11 u - minkowskiSq11 v := by
  simp [minkowskiInner11_eq, minkowskiSq11, Pi.add_apply]
  ring

/-- Orthochronous boost on `(t, x)` with rapidity `η`. -/
noncomputable def boostApply11 (η : ℝ) (v : Fin 2 → ℝ) : Fin 2 → ℝ
  | 0 => cosh η * v 0 + sinh η * v 1
  | 1 => sinh η * v 0 + cosh η * v 1

/-- Boost matrix `Λ(η)` (`Λ` is symmetric). -/
noncomputable def boostMatrix11 (η : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![cosh η, sinh η; sinh η, cosh η]

theorem boostMatrix11_mulVec (η : ℝ) (v : Fin 2 → ℝ) : boostMatrix11 η *ᵥ v = boostApply11 η v := by
  funext i
  fin_cases i <;> simp [boostMatrix11, boostApply11, mulVec, dotProduct, Fin.sum_univ_two]

theorem boostMatrix11_transpose (η : ℝ) : (boostMatrix11 η)ᵀ = boostMatrix11 η := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostMatrix11, Matrix.transpose_apply]

/-- **Adjoint / isometry identity:** `Λ g Λ = g` (since `Λᵀ = Λ`). -/
theorem boostMatrix11_mul_minkowski_mul_boost (η : ℝ) :
    boostMatrix11 η * minkowskiMetric11 * boostMatrix11 η = minkowskiMetric11 := by
  have h := cosh_sq_sub_sinh_sq η
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [boostMatrix11, minkowskiMetric11, Matrix.mul_apply, Fin.sum_univ_two]; ring_nf
  all_goals
    rw [← sub_eq_zero]
    nlinarith [h, sq_nonneg (cosh η), sq_nonneg (sinh η)]

/-- Boosts preserve the quadratic Minkowski invariant. -/
theorem minkowskiSq11_boost_invariant (η : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq11 (boostApply11 η v) = minkowskiSq11 v := by
  dsimp [minkowskiSq11, boostApply11]
  have h := cosh_sq_sub_sinh_sq η
  set t : ℝ := v 0
  set x : ℝ := v 1
  calc
    -(cosh η * t + sinh η * x) ^ 2 + (sinh η * t + cosh η * x) ^ 2
        = (cosh η ^ 2 - sinh η ^ 2) * (x ^ 2 - t ^ 2) := by ring
    _ = 1 * (x ^ 2 - t ^ 2) := by rw [h]
    _ = -(t ^ 2) + x ^ 2 := by ring

theorem minkowskiSq11_boost_invariant_mulVec (η : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq11 (boostMatrix11 η *ᵥ v) = minkowskiSq11 v := by
  rw [boostMatrix11_mulVec η v]
  exact minkowskiSq11_boost_invariant η v

/-- **Full bilinear Lorentz invariance** (from polarization + quadratic invariance). -/
theorem minkowskiInner11_boost_invariant (η : ℝ) (u v : Fin 2 → ℝ) :
    minkowskiInner11 (boostMatrix11 η *ᵥ u) (boostMatrix11 η *ᵥ v) = minkowskiInner11 u v := by
  have hQ (w : Fin 2 → ℝ) : minkowskiSq11 (boostMatrix11 η *ᵥ w) = minkowskiSq11 w :=
    minkowskiSq11_boost_invariant_mulVec η w
  have step :
      (2 : ℝ) * minkowskiInner11 (boostMatrix11 η *ᵥ u) (boostMatrix11 η *ᵥ v) =
        (2 : ℝ) * minkowskiInner11 u v := by
    rw [minkowski_polarization, minkowski_polarization u v]
    simp_rw [← mulVec_add, hQ]
  exact mul_left_cancel₀ two_ne_zero step

/-- Forward null direction `(1,1)` stays null under boost. -/
theorem null_forward_boost (η : ℝ) : minkowskiSq11 (boostApply11 η ![1, 1]) = 0 := by
  rw [minkowskiSq11_boost_invariant]
  simp [minkowskiSq11, Matrix.cons_val_zero, Matrix.cons_val_one]

/-- **Rapidity addition:** `Λ(η) Λ(ξ) = Λ(η + ξ)`. -/
theorem boostMatrix11_mul_boostMatrix11 (η ξ : ℝ) :
    boostMatrix11 η * boostMatrix11 ξ = boostMatrix11 (η + ξ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostMatrix11, Matrix.mul_apply, Fin.sum_univ_two, cosh_add, sinh_add] <;> abel

theorem boostMatrix11_zero : boostMatrix11 (0 : ℝ) = (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostMatrix11, cosh_zero, sinh_zero]

theorem boostMatrix11_mul_boostMatrix11_neg (η : ℝ) :
    boostMatrix11 η * boostMatrix11 (-η) = 1 := by
  rw [boostMatrix11_mul_boostMatrix11, add_neg_cancel, boostMatrix11_zero]

theorem minkowskiSq11_smul (a : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq11 (a • v) = a ^ 2 * minkowskiSq11 v := by
  simp [minkowskiSq11, Pi.smul_apply, smul_eq_mul]
  ring

theorem minkowskiSq11_boost_invariant_smul (η a : ℝ) (v : Fin 2 → ℝ) :
    minkowskiSq11 (boostApply11 η (a • v)) = a ^ 2 * minkowskiSq11 v := by
  rw [minkowskiSq11_boost_invariant, minkowskiSq11_smul]

/-!
## Link to HQIV φ (algebra only)
-/

theorem phi_of_T_mul_temperature (Tpos : ℝ) (h : Tpos ≠ 0) :
    phi_of_T Tpos * Tpos = phiTemperatureCoeff := by
  unfold phi_of_T phiTemperatureCoeff
  field_simp [h]

end Hqiv.Geometry
