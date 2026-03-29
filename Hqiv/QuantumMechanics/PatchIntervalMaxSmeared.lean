import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.BigOperators
import Hqiv.QuantumMechanics.PatchQFTBridge
import Hqiv.QuantumMechanics.IntervalMaxOperatorCommutator

/-!
# Smeared interval–max Pauli operators on the patch net (`Fin 4 × Fin 4`)

`IntervalMaxOperatorCommutator` realizes `commutatorKernelIntervalMax chart x y` inside
`opCommutator` on `LatticeHilbert 2` (Pauli carrier).  Here we **smear** over the discrete patch
indices: a bilinear test function `φ : Fin 4 → Fin 4 → ℝ` gives

`  smearedOpIntervalMax chart φ = ∑_{p : Fin 4 × Fin 4} φ p.1 p.2 • toEuclideanLin (pauliX_intervalMax chart p.1.val p.2.val).`

**Microcausality → vanishing smearing:** if every nonzero weight sits on an **η-spacelike** label pair,
then `commutatorKernelIntervalMax` is `0` on that support (`microcausality_intervalMax_minkowski`), hence
each summand vanishes and the smeared operator is `0`.  The same hypothesis controls the **integrated**
commutator against `toEuclideanLin pauliY` (`opCommutator_smearedOpIntervalMax_pauliY_eq_zero_of_spacelike_support`).

**Patch geometry:** `WeightSupportInRegionPair R S φ` with disjoint **spatial** regions `R, S` implies
spacelike separation for corners (`spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions`), hence
`smearedOpIntervalMax patchEventChartFour φ = 0` — the finite-patch local net now carries a **nontrivial**
commutator only where the interval kernel is nonzero (timelike / causal interior), while **Einstein causal**
disjoint spatial supports still give **vanishing** smeared operators at this Pauli-carrier level.

This is the smeared-operator layer expected by `HorizonContinuumAxiomsMinimal` / continuum-closure packaging
(`HorizonLimitedRenormLocality`): scalar kernel → matrix commutator → **smeared** linear combination with
region supports (`PatchQFTBridge.WeightSupportInRegion`, `WeightSupportInRegionPair`).
-/

namespace Hqiv.QM

open scoped InnerProductSpace
open Matrix Finset

noncomputable section

/-- Bilinear weights supported on `R × S` (nonzero only when `i ∈ R` and `j ∈ S`). -/
def WeightSupportInRegionPair (R S : SpacetimeRegion) (φ : Fin 4 → Fin 4 → ℝ) : Prop :=
  ∀ i j, φ i j ≠ 0 → i ∈ R ∧ j ∈ S

theorem WeightSupportInRegionPair.mono {R R' S S' : SpacetimeRegion} {φ : Fin 4 → Fin 4 → ℝ}
    (hR : R ⊆ R') (hS : S ⊆ S') (h : WeightSupportInRegionPair R S φ) :
    WeightSupportInRegionPair R' S' φ := by
  intro i j hij
  rcases h i j hij with ⟨hi, hj⟩
  exact ⟨hR hi, hS hj⟩

/-- Smeared `σ_x` with interval–max coefficients over patch corners (labels carried as `p.1.val`, `p.2.val` : `ℕ`). -/
noncomputable def smearedOpIntervalMax (chart : EventChart) (φ : Fin 4 → Fin 4 → ℝ) :
    LatticeHilbert 2 →ₗ[ℂ] LatticeHilbert 2 :=
  Finset.sum Finset.univ fun p : Fin 4 × Fin 4 =>
    (φ p.1 p.2 : ℂ) • Matrix.toEuclideanLin (pauliX_intervalMax chart p.1.val p.2.val)

theorem smearedOpIntervalMax_eq_zero_of_kernel_vanishes (chart : EventChart) (φ : Fin 4 → Fin 4 → ℝ)
    (h : ∀ i j, φ i j ≠ 0 → commutatorKernelIntervalMax chart i.val j.val = 0) :
    smearedOpIntervalMax chart φ = 0 := by
  unfold smearedOpIntervalMax
  refine Finset.sum_eq_zero ?_
  intro p _
  by_cases hφ : φ p.1 p.2 = 0
  · simp [hφ]
  · have hκ := h p.1 p.2 hφ
    have hmat : pauliX_intervalMax chart p.1.val p.2.val = 0 := by
      dsimp [pauliX_intervalMax]
      rw [hκ]
      simp
    rw [hmat, LinearEquiv.map_zero, smul_zero]

theorem smearedOpIntervalMax_eq_zero_of_spacelike_support (chart : EventChart) (φ : Fin 4 → Fin 4 → ℝ)
    (h : ∀ i j, φ i j ≠ 0 → spacelikeRelationMinkowski chart i.val j.val) :
    smearedOpIntervalMax chart φ = 0 :=
  smearedOpIntervalMax_eq_zero_of_kernel_vanishes chart φ fun i j hi =>
    microcausality_intervalMax_minkowski chart i.val j.val (h i j hi)

theorem smearedOpIntervalMax_patchEventChartFour_eq_zero_of_disjoint_spatial_regions
    (φ : Fin 4 → Fin 4 → ℝ) {R S : SpacetimeRegion}
    (hR : R ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0)
    (hS : S ⊆ Finset.erase (Finset.univ : Finset (Fin 4)) 0)
    (hdisj : Disjoint R S) (hφ : WeightSupportInRegionPair R S φ) :
    smearedOpIntervalMax patchEventChartFour φ = 0 := by
  refine smearedOpIntervalMax_eq_zero_of_spacelike_support patchEventChartFour φ ?_
  intro i j hij
  have hiR : i ∈ R := (hφ i j hij).1
  have hjS : j ∈ S := (hφ i j hij).2
  exact spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions i.is_lt j.is_lt hR hS hdisj hiR hjS

theorem opCommutator_smearedOpIntervalMax_toEuclideanLin_pauliY (chart : EventChart) (φ : Fin 4 → Fin 4 → ℝ) :
    opCommutator (smearedOpIntervalMax chart φ) (Matrix.toEuclideanLin pauliY_comm) =
      Finset.sum Finset.univ fun p : Fin 4 × Fin 4 =>
        (φ p.1 p.2 : ℂ) •
          opCommutator (Matrix.toEuclideanLin (pauliX_intervalMax chart p.1.val p.2.val))
            (Matrix.toEuclideanLin pauliY_comm) := by
  unfold smearedOpIntervalMax
  exact opCommutator_sum_univ_first (ι := Fin 4 × Fin 4) (fun p => φ p.1 p.2)
    (fun p => Matrix.toEuclideanLin (pauliX_intervalMax chart p.1.val p.2.val))
      (Matrix.toEuclideanLin pauliY_comm)

/-- **Full bilinear** patch commutator: two independent test functions `φ`, `ψ` on `Fin 4 × Fin 4` (c-number
coefficients `(φ p)(ψ q)` on each elementary `opCommutator` of interval–scaled `σ_x` factors). -/
theorem opCommutator_smearedOpIntervalMax_pair (chart : EventChart) (φ ψ : Fin 4 → Fin 4 → ℝ) :
    opCommutator (smearedOpIntervalMax chart φ) (smearedOpIntervalMax chart ψ) =
      Finset.sum Finset.univ fun p : Fin 4 × Fin 4 =>
        Finset.sum Finset.univ fun q : Fin 4 × Fin 4 =>
          (φ p.1 p.2 * ψ q.1 q.2 : ℂ) •
            opCommutator (Matrix.toEuclideanLin (pauliX_intervalMax chart p.1.val p.2.val))
              (Matrix.toEuclideanLin (pauliX_intervalMax chart q.1.val q.2.val)) := by
  unfold smearedOpIntervalMax
  rw [opCommutator_sum_univ_first]
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [opCommutator_sum_univ_second, Finset.smul_sum]
  refine Finset.sum_congr rfl ?_
  intro q _
  rw [← smul_smul]

theorem opCommutator_smearedOpIntervalMax_pauliY_eq_zero_of_spacelike_support (chart : EventChart)
    (φ : Fin 4 → Fin 4 → ℝ)
    (h : ∀ i j, φ i j ≠ 0 → spacelikeRelationMinkowski chart i.val j.val) :
    opCommutator (smearedOpIntervalMax chart φ) (Matrix.toEuclideanLin pauliY_comm) = 0 := by
  rw [opCommutator_smearedOpIntervalMax_toEuclideanLin_pauliY]
  refine Finset.sum_eq_zero ?_
  intro p _
  by_cases hφ : φ p.1 p.2 = 0
  · simp [hφ]
  · rw [opCommutator_pauliX_intervalMax_pauliY_smul,
      microcausality_intervalMax_minkowski chart p.1.val p.2.val (h p.1 p.2 hφ)]
    simp

end

end Hqiv.QM
