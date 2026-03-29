import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Notation
import Hqiv.OctonionLeftMultiplication

open BigOperators

/-!
# Octonion basics — Fano-plane algebra on ℝ⁸

Standard octonion basis e₀..e₇ with Fano-plane multiplication. We represent the algebra
as ℝ⁸ (Fin 8 → ℝ) with multiplication given by the left-multiplication matrices L(e_i)
from `Hqiv.OctonionLeftMultiplication`. Mathlib 4 does not yet have an `Octonion ℝ` type
in the main library; we use the matrix representation throughout.

**Reference:** HQIV preprint v2, Zenodo 10.5281/zenodo.18899939, Section 4.2.
-/

open Matrix

namespace Hqiv.Algebra

/-- **Octonion algebra as 8-dimensional real space** (basis e₀ = 1, e₁..e₇ imaginary).
We identify ℝ⁸ ≃ Fin 8 → ℝ; component i is the coefficient of e_i. -/
def OctonionVec := Fin 8 → ℝ

instance : AddCommGroup OctonionVec := Pi.addCommGroup
instance : Module ℝ OctonionVec := Pi.module _ _ _

@[ext]
theorem OctonionVec.ext (x y : OctonionVec) (h : ∀ i, x i = y i) : x = y := by
  funext i; exact h i

/-- **Standard basis vector e_i** (1 at position i, 0 elsewhere). -/
def octonionBasis (i : Fin 8) : OctonionVec :=
  fun j => if j = i then 1 else 0

/-- **e₀ = 1** (real unit). -/
def e0 : OctonionVec := octonionBasis 0

/-- **e₁..e₇** (imaginary units, Fano plane). -/
def e1 : OctonionVec := octonionBasis 1
def e2 : OctonionVec := octonionBasis 2
def e3 : OctonionVec := octonionBasis 3
def e4 : OctonionVec := octonionBasis 4
def e5 : OctonionVec := octonionBasis 5
def e6 : OctonionVec := octonionBasis 6
def e7 : OctonionVec := octonionBasis 7

/-- Left multiplication by e_i as a matrix (L(e_i) from OctonionLeftMultiplication). -/
def leftMulMatrix : Fin 8 → Matrix (Fin 8) (Fin 8) ℝ
  | 0 => 1  -- identity
  | 1 => Hqiv.octonionLeftMul_1
  | 2 => Hqiv.octonionLeftMul_2
  | 3 => Hqiv.octonionLeftMul_3
  | 4 => Hqiv.octonionLeftMul_4
  | 5 => Hqiv.octonionLeftMul_5
  | 6 => Hqiv.octonionLeftMul_6
  | 7 => Hqiv.octonionLeftMul_7

/-- **Octonion multiplication (left action)** on ℝ⁸: x * y = L(x) · y as vectors.
So (leftMul x) y = (leftMulMatrix applied to x) · y. -/
def leftMulVec (x : OctonionVec) (y : OctonionVec) : OctonionVec :=
  fun i => ∑ j, (∑ k, (leftMulMatrix k) i j * x k) * y j

-- Simplify: leftMul by basis vector e_i is just the i-th column of leftMulMatrix i... 
-- Actually L(e_i) acts by (L(e_i) * y)_k = ∑_j (L(e_i))_kj y_j. So for x = e_i, 
-- leftMul e_i = leftMulMatrix i as linear map. We keep the definition above for a generic x.

/-- **Standard Euclidean inner product on ℝ⁸** (octonions viewed as vectors): ⟨x, y⟩ = ∑ᵢ xᵢ yᵢ. -/
def octonionInner (x y : OctonionVec) : ℝ := ∑ i : Fin 8, x i * y i

/-- **Left multiplication by the i-th basis vector** (i = 0..7): applies leftMulMatrix i. -/
def leftMulByBasis (i : Fin 8) (y : OctonionVec) : OctonionVec :=
  fun k => ∑ j : Fin 8, (leftMulMatrix i) k j * y j

/-- For the real unit e₀, left multiplication is the identity. -/
theorem leftMulByBasis_e0 (y : OctonionVec) : leftMulByBasis 0 y = y := by
  unfold leftMulByBasis leftMulMatrix
  ext k
  simp only [Matrix.one_apply]
  rw [Finset.sum_eq_single k]
  · simp
  · intro x _ hne; simp only [hne.symm, ite_false, zero_mul]
  · intro h; exact absurd (Finset.mem_univ k) h

/-- Multiplying by a **basis** vector matches `leftMulByBasis` (Fano multiplication table). -/
theorem leftMulVec_octonionBasis (i : Fin 8) (y : OctonionVec) :
    leftMulVec (octonionBasis i) y = leftMulByBasis i y := by
  funext l
  simp only [leftMulVec, leftMulByBasis]
  refine Finset.sum_congr rfl ?_
  intro j _
  congr 1
  rw [Finset.sum_eq_single i]
  · simp [octonionBasis]
  · intro k _ hk
    have h0 : (octonionBasis i) k = (0 : ℝ) := by
      simp [octonionBasis, if_neg hk]
    rw [h0, mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Octonion associator \((xy)z - x(yz)\), measuring non-associativity (vorticity surrogate). -/
def octonionAssociator (x y z : OctonionVec) : OctonionVec :=
  leftMulVec (leftMulVec x y) z - leftMulVec x (leftMulVec y z)

/-- Squared Euclidean norm \(\sum_i a_i^2\) of the associator. -/
noncomputable def octonionAssociatorNormSq (x y z : OctonionVec) : ℝ :=
  ∑ i : Fin 8, (octonionAssociator x y z i) ^ 2

/-- Map associator energy to \([0,1]\) for scattering-style witnesses (`a/(a+1)`). -/
noncomputable def scatteringAmpFromAssociator (x y z : OctonionVec) : ℝ :=
  octonionAssociatorNormSq x y z / (octonionAssociatorNormSq x y z + 1)

end Hqiv.Algebra
