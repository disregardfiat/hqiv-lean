/-
Digital gates as bijections of `DiscreteState L` preserving the informational inner product from
`DiscreteQuantumState`, together with the ℝ octonion 8-plane (left multiplications from
`Hqiv.OctonionLeftMultiplication`) and a finite `Fin 4` controlled–swap model (CNOT analogue).
No continuum Hilbert space: only finite sums, rational weights on the angular ladder, and ℝ only
where the existing generator matrices are typed.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Hqiv.OctonionLeftMultiplication
import Hqiv.QuantumComputing.DiscreteQuantumState
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions

namespace Hqiv.QuantumComputing

open scoped BigOperators
open Finset
open Hqiv.Algebra

variable {L : ℕ}
variable [DecidableEq (HarmonicIndex L)]

/-- Euclidean octonion inner product: sign flip on both arguments is invariant. -/
private theorem octonionInner_neg_neg (x y : OctonionVec) :
    octonionInner (-x) (-y) = octonionInner x y := by
  -- Unfold to the componentwise sum and finish by termwise negation cancellation.
  simp [octonionInner] at *
  -- Now the goal is a sum over `Fin 8`; use termwise equality.
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact neg_mul_neg (x i) (y i)

/-- Bijections of digital amplitudes preserving `discreteIp`. -/
structure HQIVGate (L : ℕ) where
  toEquiv : DiscreteState L ≃ DiscreteState L
  preserves_ip (f g : DiscreteState L) :
    discreteIp (toEquiv f) (toEquiv g) = discreteIp f g

omit [DecidableEq (HarmonicIndex L)] in
theorem HQIVGate.preserves_normSq (G : HQIVGate L) (f : DiscreteState L) :
    discreteNormSq (G.toEquiv f) = discreteNormSq f := by
  simpa [discreteNormSq] using G.preserves_ip f f

def HQIVGate.symm (G : HQIVGate L) : HQIVGate L where
  toEquiv := G.toEquiv.symm
  preserves_ip f g := by
    simpa [Equiv.apply_symm_apply] using
      (G.preserves_ip (G.toEquiv.symm f) (G.toEquiv.symm g)).symm

def HQIVGate.trans (G₁ G₂ : HQIVGate L) : HQIVGate L where
  toEquiv := G₁.toEquiv.trans G₂.toEquiv
  preserves_ip f g := by
    simp [Equiv.trans_apply, G₂.preserves_ip, G₁.preserves_ip]

def HQIVGate.id : HQIVGate L where
  toEquiv := Equiv.refl _
  preserves_ip _ _ := rfl

/-- π phase on one angular mode. -/
def phaseGate (ij : HarmonicIndex L) : HQIVGate L where
  toEquiv := {
    toFun := fun f k => if k = ij then -f k else f k
    invFun := fun f k => if k = ij then -f k else f k
    left_inv := fun f => funext fun k => by by_cases hk : k = ij <;> simp [hk]
    right_inv := fun f => funext fun k => by by_cases hk : k = ij <;> simp [hk]
  }
  preserves_ip f g := by
    classical
    -- Expand the informational inner product; only index `ij` is sign-flipped.
    simp [discreteIp, Equiv.coe_fn_mk]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k = ij
    · subst h
      simp [octonionInner_neg_neg]
    · simp [h]

private theorem phiRat_eq_of_swap {ij₁ ij₂ : HarmonicIndex L} (hℓ : ij₁.fst = ij₂.fst)
    (k : HarmonicIndex L) :
    phiRat k.fst.val = phiRat ((Equiv.swap ij₁ ij₂) k).fst.val := by
  by_cases hk1 : k = ij₁
  · subst hk1
    simpa [Equiv.swap_apply_left, phiRat] using congr_arg (fun ℓ : Fin (L + 1) => phiRat ℓ.val) hℓ
  · by_cases hk2 : k = ij₂
    · subst hk2
      simpa [Equiv.swap_apply_right, phiRat] using
        congr_arg (fun ℓ : Fin (L + 1) => phiRat ℓ.val) hℓ.symm
    · have hk3 : Equiv.swap ij₁ ij₂ k = k := Equiv.swap_apply_of_ne_of_ne hk1 hk2
      simp [hk3]

/-- Swap two modes with the same `ℓ` (identical `phiRat` weight). -/
def swapGates (ij₁ ij₂ : HarmonicIndex L) (hℓ : ij₁.fst = ij₂.fst) : HQIVGate L where
  toEquiv := (Equiv.swap ij₁ ij₂).arrowCongr (Equiv.refl (OctonionVec))
  preserves_ip f g := by
    let σ := Equiv.swap ij₁ ij₂
    -- With the unweighted `discreteIp`, any index permutation preserves the inner product.
    -- `arrowCongr` induces precomposition by `σ` on the basis-indexed amplitude function.
    simp [discreteIp, Equiv.arrowCongr, Equiv.coe_refl, σ, octonionInner]
    simpa using Equiv.sum_comp σ (fun k => octonionInner (f k) (g k))

/-- Hadamard-style identity on a uniform `Fin 2` pair (no `√2`; doubling is explicit). -/
theorem hadamardShell_two_mul (v : Fin 2 → ℚ) :
    (v 0 + v 1) ^ 2 + (v 0 - v 1) ^ 2 = 2 * (v 0 ^ 2 + v 1 ^ 2) := by
  ring

/-! ### Octonion left multiplications on `Fin 8 → ℝ` (Euclidean sum of squares) -/

def octonionMulVec (M : Matrix (Fin 8) (Fin 8) ℝ) (v : Fin 8 → ℝ) : Fin 8 → ℝ :=
  fun i => ∑ j : Fin 8, M i j * v j

def euclideanNormSqEight (v : Fin 8 → ℝ) : ℝ :=
  ∑ i : Fin 8, v i * v i

theorem octonionLeftMul_N_preserves_euclidean (N : Fin 7) (v : Fin 8 → ℝ) :
    euclideanNormSqEight (octonionMulVec (octonionLeftMul_N N) v) = euclideanNormSqEight v := by
  set_option maxHeartbeats 0 in
  match N with
  | ⟨0, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_1,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨1, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_2,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨2, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_3,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨3, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_4,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨4, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_5,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨5, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_6,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring
  | ⟨6, _⟩ =>
      simp [octonionLeftMul_N, octonionMulVec, euclideanNormSqEight, octonionLeftMul_7,
        Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]; ring

/-- The scalar unit `e₀ = 1` acts as identity on the octonion 8-vector. -/
def octonionScalarUnit : Matrix (Fin 8) (Fin 8) ℝ := 1

theorem octonionScalarUnit_preserves_euclidean (v : Fin 8 → ℝ) :
    euclideanNormSqEight (octonionMulVec octonionScalarUnit v) = euclideanNormSqEight v := by
  have hmul : octonionMulVec octonionScalarUnit v = v := by
    funext i
    simp only [octonionMulVec, octonionScalarUnit, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp [mul_one]
    · intro j _ hne; simp only [hne.symm, ite_false, zero_mul]
    · intro h; exact absurd (Finset.mem_univ i) h
  simp [hmul]

/-! ### `Fin 4` controlled–swap (CNOT analogue) on `ℚ⁴`, unweighted `ℓ²` -/

def unweightedNormSqFour (v : Fin 4 → ℚ) : ℚ :=
  ∑ i : Fin 4, v i * v i

/-- Swap the `|10⟩` and `|11⟩` basis labels (`2` and `3` in little-endian two-bit order). -/
def cnotPerm : Fin 4 ≃ Fin 4 :=
  Equiv.swap 2 3

def applyPermFour (σ : Fin 4 ≃ Fin 4) (v : Fin 4 → ℚ) : Fin 4 → ℚ :=
  fun i => v (σ i)

theorem unweighted_norm_perm_four (σ : Fin 4 ≃ Fin 4) (v : Fin 4 → ℚ) :
    unweightedNormSqFour (applyPermFour σ v) = unweightedNormSqFour v := by
  simp [unweightedNormSqFour, applyPermFour]
  exact Equiv.sum_comp σ fun i => v i * v i

theorem cnot_preserves_unweighted_four (v : Fin 4 → ℚ) :
    unweightedNormSqFour (applyPermFour cnotPerm v) = unweightedNormSqFour v :=
  unweighted_norm_perm_four cnotPerm v

/-- CKW/monogamy budget compatibility: scaling nonnegative tangles by `etaModePhi` preserves CKW. -/
theorem digital_ckw_step (m : ℕ) {τAB τAC τA_BC : ℝ} (h : Hqiv.QM.ckwMonogamy τAB τAC τA_BC) :
    Hqiv.QM.correctedCkwMonogamyPhi m τAB τAC τA_BC :=
  Hqiv.QM.corrected_monogamy_of_ckw_phi m h

#print HQIVGate
#print swapGates
#print octonionLeftMul_N_preserves_euclidean
#print cnot_preserves_unweighted_four
#print digital_ckw_step

#check HQIVGate.preserves_normSq
#check hadamardShell_two_mul
#check octonionLeftMul_N_preserves_euclidean
#check cnot_preserves_unweighted_four
#check digital_ckw_step

end Hqiv.QuantumComputing
