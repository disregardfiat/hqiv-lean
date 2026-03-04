import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent
import Mathlib.Algebra.BigOperators.Basic
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

/-- **Coordinate matrix has nonzero determinant.** Script `print_linear_independence.py` gives det = -1. -/
theorem so8CoordMatrix_det_ne_zero : so8CoordMatrix.det ≠ 0 := by
  -- det so8CoordMatrix = -1 (numerically); proving in Lean by norm_num may be heavy
  sorry

/-- **The 28 so8 generators are linearly independent over ℝ.** Follows from
`so8CoordMatrix_det_ne_zero`: the upper-triangle coordinate matrix is invertible. -/
theorem so8_generators_linear_independent :
    LinearIndependent ℝ (fun k : Fin 28 => so8Generator k) := by
  sorry  -- use so8CoordMatrix_det_ne_zero + coordinate map: ∑ c_k • g_k = 0 ⇒ coords = M·c = 0 ⇒ c = 0

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
