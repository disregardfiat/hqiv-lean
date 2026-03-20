import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin

import Hqiv.Generators
import Hqiv.GeneratorsFromAxioms
import Hqiv.GeneratorsLieClosureData
import Hqiv.So8CoordMatrix

open Matrix BigOperators

namespace Hqiv

/-!
# Lie bracket closure — [so8Generator i, so8Generator j] in span of the 28

We prove that each Lie bracket lies in the ℝ-span of the 28 generators, so the
generators form a Lie subalgebra (so(8)). Coefficients from
`scripts/print_lie_bracket_closure.py` (see `Hqiv.GeneratorsLieClosureData`).
-/

/-- **Lie bracket antisymmetry:** [A, B] = -[B, A]. -/
theorem lieBracket_antisymm (A B : Matrix (Fin 8) (Fin 8) ℝ) :
    lieBracket A B = -lieBracket B A := by
  unfold lieBracket
  ext i j
  simp only [neg_apply, mul_apply, sub_apply, neg_sub]
  ring

/-- **Every Lie bracket [so8Generator i, so8Generator j]** lies in the ℝ-span of the 28 generators.
Coefficients are `lieBracketCoeff i j` (defined in GeneratorsLieClosureData). -/
theorem lieBracket_in_span (i j : Fin 28) :
    lieBracket (so8Generator i) (so8Generator j) =
      ∑ k : Fin 28, lieBracketCoeff i j k • so8Generator k := by
  ext a b
  simp only [lieBracket, mul_apply, sub_apply, Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_fin_eq_sum_range]
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    norm_num [Finset.sum_range_succ, so8Generator, lieBracketCoeff,
      generator_0, generator_1, generator_2, generator_3, generator_4, generator_5,
      generator_6, generator_7, generator_8, generator_9, generator_10, generator_11,
      generator_12, generator_13, generator_14, generator_15, generator_16, generator_17,
      generator_18, generator_19, generator_20, generator_21, generator_22, generator_23,
      generator_24, generator_25, generator_26, generator_27]

/-!
## Linear independence

The 28 generators are linearly independent (hence a basis for so(8)). We prove this
by showing that the 28×28 matrix of upper-triangle coordinates (`so8CoordMatrix`) has
nonzero determinant (script: `scripts/print_linear_independence.py` gives det = -1).
-/

/-- **det(so8CoordMatrix)² = 1** (columns orthonormal ⇒ Mᵀ M = 1 ⇒ det(Mᵀ M) = 1). -/
theorem so8CoordMatrix_det_sq_eq_one : so8CoordMatrix.det ^ 2 = 1 := by
  calc so8CoordMatrix.det ^ 2 = so8CoordMatrix.det * so8CoordMatrix.det := sq _
    _ = (so8CoordMatrixᵀ).det * so8CoordMatrix.det := by rw [det_transpose]
    _ = det (so8CoordMatrixᵀ * so8CoordMatrix) := by rw [det_mul]
    _ = det (1 : Matrix (Fin 28) (Fin 28) ℝ) := by rw [So8CoordMatrix.so8CoordMatrix_transpose_mul_self]
    _ = 1 := det_one

/-- **Coordinate matrix has nonzero determinant.** Follows from so8CoordMatrix_transpose_mul_self (det² = 1). -/
theorem so8CoordMatrix_det_ne_zero : so8CoordMatrix.det ≠ 0 := by
  intro h
  rw [h, sq, zero_mul] at so8CoordMatrix_det_sq_eq_one
  norm_num at so8CoordMatrix_det_sq_eq_one

/-- so8CoordMatrix p k equals (so8Generator k) at the p-th upper-triangle index (definitional). -/
theorem so8CoordMatrix_eq_coord (p k : Fin 28) :
    so8CoordMatrix p k = (so8Generator k) (upperTriangleIdx p).1 (upperTriangleIdx p).2 := rfl

/-- The coordinate vector of a linear combination ∑ c_k • so8Generator k is so8CoordMatrix.mulVec c. -/
theorem coordVec_linearCombination (c : Fin 28 → ℝ) (p : Fin 28) :
    coordVec (∑ k : Fin 28, c k • so8Generator k) p = (so8CoordMatrix.mulVec c) p := by
  simp only [coordVec, Finset.sum_apply, Pi.smul_apply, mulVec_apply, so8CoordMatrix_eq_coord]
  rfl

/-- so8CoordMatrix is invertible (Mᵀ * M = 1 ⇒ M has a left inverse ⇒ det invertible). -/
instance so8CoordMatrix_invertible : Invertible so8CoordMatrix := by
  have : Invertible so8CoordMatrix.det :=
    Matrix.detInvertibleOfLeftInverse so8CoordMatrix so8CoordMatrixᵀ So8CoordMatrix.so8CoordMatrix_transpose_mul_self
  exact Matrix.invertibleOfDetInvertible so8CoordMatrix

/-- If so8CoordMatrix.mulVec c = 0 then c = 0 (matrix is invertible, so kernel trivial). -/
theorem so8CoordMatrix_mulVec_eq_zero_imp_eq_zero (c : Fin 28 → ℝ)
    (h : so8CoordMatrix.mulVec c = 0) : c = 0 := by
  have key : (⅟so8CoordMatrix).mulVec (so8CoordMatrix.mulVec c) = c := by
    rw [← Matrix.mulVec_mulVec c (⅟so8CoordMatrix) so8CoordMatrix, Matrix.invOf_mul_self, Matrix.one_mulVec]
  rw [h, Matrix.zero_mulVec] at key
  exact key.symm

/-- **The 28 so8 generators are linearly independent over ℝ.** The coordinate map sends
∑ c_k • so8Generator k to so8CoordMatrix.mulVec c; det ≠ 0 implies the matrix is invertible,
so the map is injective, hence the generators are independent. -/
theorem so8_generators_linear_independent :
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by
  rw [Fintype.linearIndependent_iffₛ]
  intro f g h
  ext i
  have hdiff : ∑ k : Fin 28, (f k - g k) • so8Generator k = 0 := by
    rw [← sub_eq_zero, Finset.sum_sub_distrib]; simp_rw [sub_smul]
    exact sub_eq_zero.mpr h
  have hcoord : so8CoordMatrix.mulVec (fun k => f k - g k) = 0 := by
    ext p
    rw [← coordVec_linearCombination (fun k => f k - g k) p, hdiff]
    simp only [coordVec, zero_apply]
  have hzero := so8CoordMatrix_mulVec_eq_zero_imp_eq_zero (fun k => f k - g k) hcoord
  exact sub_eq_zero.mp (congr_fun hzero i)

/-- **Generators from first assumptions:** The 28 so(8) generators are antisymmetric,
closed under Lie bracket (with coefficients `lieBracketCoeff`), and linearly independent.
So they form a basis for a 28-dimensional Lie subalgebra (so(8)). -/
theorem generators_from_octonion_closure :
    (∀ k : Fin 28, so8Generator k + (so8Generator k)ᵀ = 0) ∧
    (∀ i j : Fin 28, ∃ f : Fin 28 → ℝ,
      lieBracket (so8Generator i) (so8Generator j) = ∑ k, f k • so8Generator k) ∧
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by
  refine ⟨so8Generator_antisymm, ?_, so8_generators_linear_independent⟩
  intro i j
  exact ⟨lieBracketCoeff i j, lieBracket_in_span i j⟩

end Hqiv
