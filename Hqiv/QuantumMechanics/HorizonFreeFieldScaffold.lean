import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Basic

/-!
# Free-field scaffold on a finite spatial lattice (commuting smeared operators)

This is a **minimal** formal hook toward continuum QFT: a fixed-time Cauchy slice is modelled by
`Fin n` sites, Hilbert space `ℂⁿ` with the standard `L²` inner product (`EuclideanSpace`), and a
**diagonal** smeared “field” `Φ(f)` given by `Matrix.toEuclideanLin (Matrix.diagonal (f i))ᵢ`.

* The algebra is **abelian** (`Φ(f)` and `Φ(g)` always commute). This is honest scaffolding: it
  isolates **smeared linear operators** and **composition** before adding canonical pairs or
  dynamics.
* **Disjoint sampling supports** (`∀ i, f i = 0 ∨ g i = 0`) imply `Φ(f) ∘ Φ(g) = 0`, since the
  diagonal weights multiply site-wise.

`microcausality_in_domain_free_lattice` packages unconditional commutativity for use as the
`microcausality_in_domain` slot in `HorizonContinuumAxiomsMinimal` (not full Minkowski microcausality).

`opCommutator` and `smearedField_opCommutator_eq_zero` give the operator commutator on `LatticeHilbert n`;
`opCommutator_sum_finset_first` / `opCommutator_sum_univ_first` (linearity in the **first** factor) and
`opCommutator_sum_finset_second` / `opCommutator_sum_univ_second` (linearity in the **second** factor);
`MinkowskiFieldOperatorScaffold` maps events through an `EventChart` to `smearedField` on `LatticeHilbert 4`.
`CCRFiniteDimObstruction` proves **no** exact `[A,B]=I` on fixed `Mat_n` (trace); HQIV still works patchwise
in the light cone with growing cutoffs. `LocalAlgebraNetScaffold` packages a constant diagonal **local net**.

See also `Hqiv.Geometry.AuxiliaryFieldSmeared`, `ContinuumManyBodyQFTScaffold`, and `PauliCommutatorExample`.
-/

namespace Hqiv.QM

open scoped InnerProductSpace
open EuclideanSpace PiLp Matrix

/-- One complex amplitude per lattice site, `L²` inner product. -/
abbrev LatticeHilbert (n : ℕ) := EuclideanSpace ℂ (Fin n)

noncomputable section

/-- Diagonal matrix with entries `(w i : ℂ)` (site weights). -/
noncomputable def smearedMat {n : ℕ} (w : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun i => (w i : ℂ))

/-- Smeared field operator `Φ(w)` on `LatticeHilbert n`. -/
noncomputable def smearedField {n : ℕ} (w : Fin n → ℝ) : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n :=
  Matrix.toEuclideanLin (smearedMat w)

theorem toEuclideanLin_comp_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (Matrix.toEuclideanLin A).comp (Matrix.toEuclideanLin B) = Matrix.toEuclideanLin (A * B) :=
  (Matrix.toLpLin_mul_same (R := ℂ) (p := 2) (A := A) (B := B)).symm

theorem smearedMat_ext {n : ℕ} {w v : Fin n → ℝ} (h : ∀ i, w i = v i) : smearedMat w = smearedMat v := by
  dsimp [smearedMat]
  congr 1
  ext i
  simp [h i]

@[simp]
theorem smearedField_apply {n : ℕ} (w : Fin n → ℝ) (ψ : LatticeHilbert n) (i : Fin n) :
    smearedField w ψ i = (w i : ℂ) * ψ i := by
  simp [smearedField, Matrix.toEuclideanLin, Matrix.toLpLin_apply, PiLp.toLp_apply, smearedMat,
    mulVec_diagonal]

theorem smearedField_ext {n : ℕ} {w v : Fin n → ℝ} (h : ∀ i, w i = v i) :
    smearedField w = smearedField v := by
  dsimp [smearedField]
  rw [smearedMat_ext h]

theorem smearedField_comp {n : ℕ} (f g : Fin n → ℝ) :
    smearedField f ∘ₗ smearedField g = smearedField (fun i => f i * g i) := by
  dsimp [smearedField, smearedMat]
  rw [toEuclideanLin_comp_mul]
  congr 1
  rw [Matrix.diagonal_mul_diagonal]
  ext i
  simp

theorem smearedField_comm {n : ℕ} (f g : Fin n → ℝ) :
    smearedField f ∘ₗ smearedField g = smearedField g ∘ₗ smearedField f := by
  rw [smearedField_comp, smearedField_comp]
  refine smearedField_ext ?_
  intro i
  exact mul_comm _ _

/-- Operator commutator `[A,B] = AB - BA` on `LatticeHilbert n` (abstract `ℂⁿ` scaffold). -/
noncomputable def opCommutator {n : ℕ} (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    LatticeHilbert n →ₗ[ℂ] LatticeHilbert n :=
  A ∘ₗ B - B ∘ₗ A

@[simp]
theorem opCommutator_apply {n : ℕ} (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) (ψ : LatticeHilbert n) :
    opCommutator A B ψ = A (B ψ) - B (A ψ) :=
  rfl

theorem opCommutator_zero_left {n : ℕ} (B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (0 : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) B = 0 := by
  unfold opCommutator
  simp

theorem opCommutator_smul_left {n : ℕ} (r : ℂ) (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (r • A) B = r • opCommutator A B := by
  unfold opCommutator
  rw [LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]

theorem opCommutator_add_left {n : ℕ} (A₁ A₂ B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (A₁ + A₂) B = opCommutator A₁ B + opCommutator A₂ B := by
  unfold opCommutator
  rw [LinearMap.add_comp, LinearMap.comp_add, sub_add_sub_comm]

theorem opCommutator_sum_finset_first {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (A : ι → (LatticeHilbert n →ₗ[ℂ] LatticeHilbert n)) (B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (Finset.sum s fun i => c i • A i) B = Finset.sum s fun i => c i • opCommutator (A i) B := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [opCommutator_zero_left]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opCommutator_add_left, ih, opCommutator_smul_left]

theorem opCommutator_sum_univ_first {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (A : ι → (LatticeHilbert n →ₗ[ℂ] LatticeHilbert n)) (B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator (Finset.sum Finset.univ fun i => c i • A i) B =
      Finset.sum Finset.univ fun i => c i • opCommutator (A i) B :=
  opCommutator_sum_finset_first Finset.univ c A B

theorem opCommutator_zero_right {n : ℕ} (A : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator A (0 : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) = 0 := by
  unfold opCommutator
  simp

theorem opCommutator_smul_right {n : ℕ} (r : ℂ) (A B : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator A (r • B) = r • opCommutator A B := by
  unfold opCommutator
  rw [LinearMap.comp_smul, LinearMap.smul_comp, smul_sub]

theorem opCommutator_add_right {n : ℕ} (A B₁ B₂ : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) :
    opCommutator A (B₁ + B₂) = opCommutator A B₁ + opCommutator A B₂ := by
  unfold opCommutator
  rw [LinearMap.comp_add, LinearMap.add_comp, sub_add_sub_comm]

theorem opCommutator_sum_finset_second {n : ℕ} {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ)
    (A : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) (B : ι → (LatticeHilbert n →ₗ[ℂ] LatticeHilbert n)) :
    opCommutator A (Finset.sum s fun i => c i • B i) = Finset.sum s fun i => c i • opCommutator A (B i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [opCommutator_zero_right]
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, opCommutator_add_right, ih, opCommutator_smul_right]

theorem opCommutator_sum_univ_second {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (A : LatticeHilbert n →ₗ[ℂ] LatticeHilbert n) (B : ι → (LatticeHilbert n →ₗ[ℂ] LatticeHilbert n)) :
    opCommutator A (Finset.sum Finset.univ fun i => c i • B i) =
      Finset.sum Finset.univ fun i => c i • opCommutator A (B i) :=
  opCommutator_sum_finset_second Finset.univ c A B

/-- Diagonal smeared fields are **abelian**: commutators vanish identically. -/
theorem smearedField_opCommutator_eq_zero {n : ℕ} (f g : Fin n → ℝ) :
    opCommutator (smearedField f) (smearedField g) = 0 := by
  unfold opCommutator
  rw [smearedField_comm, sub_self]

/-- Pointwise disjoint supports: at each site at least one weight vanishes. -/
def DisjointSamplingSupport {n : ℕ} (f g : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, f i = 0 ∨ g i = 0

theorem mul_eq_zero_of_disjointSampling {n : ℕ} {f g : Fin n → ℝ}
    (h : DisjointSamplingSupport f g) (i : Fin n) : f i * g i = 0 := by
  rcases h i with hf | hg
  · simp [hf]
  · simp [hg]

theorem smearedField_zero {n : ℕ} : smearedField (fun _ : Fin n => (0 : ℝ)) = 0 := by
  refine LinearMap.ext fun ψ => PiLp.ext fun i => ?_
  simp [smearedField_apply]

theorem smearedField_comp_eq_zero_of_disjoint {n : ℕ} {f g : Fin n → ℝ}
    (h : DisjointSamplingSupport f g) : smearedField f ∘ₗ smearedField g = 0 := by
  rw [smearedField_comp]
  have hfg : (fun i : Fin n => f i * g i) = fun _ : Fin n => (0 : ℝ) :=
    funext fun i => mul_eq_zero_of_disjointSampling h i
  rw [hfg]
  exact smearedField_zero

/-- Unconditional commutativity of all smeared lattice fields (abelian scaffold). -/
def microcausality_in_domain_free_lattice : Prop :=
  ∀ (n : ℕ) (f g : Fin n → ℝ), smearedField f ∘ₗ smearedField g = smearedField g ∘ₗ smearedField f

theorem microcausality_in_domain_free_lattice_holds : microcausality_in_domain_free_lattice :=
  fun _ _ _ => smearedField_comm _ _

end

end Hqiv.QM
