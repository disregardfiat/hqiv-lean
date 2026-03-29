import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.VecNotation
import Hqiv.QuantumMechanics.PauliCommutatorExample
import Hqiv.QuantumMechanics.ContinuumManyBodyQFTScaffold
import Hqiv.QuantumMechanics.HorizonFreeFieldScaffold

/-!
# Interval–max geometry **in** the operator commutator (Pauli carrier)

The scalar **surrogate** `commutatorKernelIntervalMax chart x y = max 0 (η(x−y))` from
`ContinuumManyBodyQFTScaffold` is promoted to a **coefficient on genuine matrices**:

* `pauliX_intervalMax chart x y := (commutatorKernelIntervalMax chart x y) • pauliX`
* `matComm (pauliX_intervalMax …) pauliY = κ • matComm pauliX pauliY` with `κ` the interval max.

On `LatticeHilbert 2` via `Matrix.toEuclideanLin`, **`opCommutator`** matches `toEuclideanLin` of the same
matrix commutator (`opCommutator_toEuclideanLin_matComm`).

**CCR caveat (`CCRFiniteDimObstruction`):** there are **no** `A,B ∈ Mat_{n×n}(ℂ)` with `[A,B] = I`.
Scaling **one** factor by `κ = max 0 η` yields `[κ σ_x, σ_y] = κ [σ_x, σ_y]`, which is **κ times a fixed
traceless** commutator — consistent with `Tr([A,B]) = 0`.  This is the honest finite-dimensional insertion of
the interval functional into the **algebraic** commutator, **not** a claim of literal Heisenberg `ℏ·I` on
fixed `n`.
-/

namespace Hqiv.QM

open Matrix

/-- Left factor: Pauli `σ_x` scaled by the interval–max causal functional `max 0 η`. -/
noncomputable def pauliX_intervalMax (chart : EventChart) (x y : EventLabel) : Matrix (Fin 2) (Fin 2) ℂ :=
  (commutatorKernelIntervalMax chart x y : ℂ) • pauliX_comm

theorem matComm_smul_left (κ : ℂ) (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    matComm (κ • A) B = κ • matComm A B := by
  unfold matComm
  rw [smul_mul_assoc, Matrix.mul_smul, smul_sub]

theorem matComm_pauliX_intervalMax_pauliY (chart : EventChart) (x y : EventLabel) :
    matComm (pauliX_intervalMax chart x y) pauliY_comm =
      (commutatorKernelIntervalMax chart x y : ℂ) • matComm pauliX_comm pauliY_comm :=
  matComm_smul_left _ _ _

theorem opCommutator_toEuclideanLin_matComm (A B : Matrix (Fin 2) (Fin 2) ℂ) :
    opCommutator (Matrix.toEuclideanLin A) (Matrix.toEuclideanLin B) =
      Matrix.toEuclideanLin (matComm A B) := by
  unfold opCommutator matComm
  rw [toEuclideanLin_comp_mul (n := 2), toEuclideanLin_comp_mul (n := 2) (A := B) (B := A)]
  exact (LinearMap.map_sub (Matrix.toEuclideanLin (m := Fin 2) (n := Fin 2) (𝕜 := ℂ)).toLinearMap
    (A * B) (B * A)).symm

/-- **Genuine** `opCommutator` on `LatticeHilbert 2` with interval–max coefficient on `σ_x`. -/
theorem opCommutator_pauliX_intervalMax_pauliY (chart : EventChart) (x y : EventLabel) :
    opCommutator (Matrix.toEuclideanLin (pauliX_intervalMax chart x y))
        (Matrix.toEuclideanLin pauliY_comm) =
      Matrix.toEuclideanLin ((commutatorKernelIntervalMax chart x y : ℂ) • matComm pauliX_comm pauliY_comm) := by
  rw [opCommutator_toEuclideanLin_matComm, matComm_pauliX_intervalMax_pauliY]

theorem opCommutator_pauliX_intervalMax_pauliY_smul (chart : EventChart) (x y : EventLabel) :
    opCommutator (Matrix.toEuclideanLin (pauliX_intervalMax chart x y))
        (Matrix.toEuclideanLin pauliY_comm) =
      (commutatorKernelIntervalMax chart x y : ℂ) • Matrix.toEuclideanLin (matComm pauliX_comm pauliY_comm) := by
  rw [opCommutator_pauliX_intervalMax_pauliY]
  rw [LinearEquiv.map_smul]

/-- If the interval–max scalar **vanishes**, the Pauli commutator lift is **zero** (boundary / lightlike witness). -/
theorem opCommutator_pauliX_intervalMax_pauliY_eq_zero_of_comm_kernel_eq_zero {chart : EventChart} {x y : EventLabel}
    (hκ : commutatorKernelIntervalMax chart x y = 0) :
    opCommutator (Matrix.toEuclideanLin (pauliX_intervalMax chart x y))
        (Matrix.toEuclideanLin pauliY_comm) = 0 := by
  rw [opCommutator_pauliX_intervalMax_pauliY_smul, hκ]
  simp

/-!
### Lightlike unit chart: `η = 0` ⇒ `κ = 0` ⇒ `opCommutator = 0`

Events `0` and `1` sit at `(1,1,0,0)` and `(0,0,0,0)`; separation is lightlike, so `max 0 η = 0`.
-/

/-- Lightlike-separation witness: `η((1,1,0,0) - 0) = 0`. -/
noncomputable def chartLightlikeBoundaryExample : EventChart
  | 0 => ![1, 1, 0, 0]
  | 1 => ![0, 0, 0, 0]
  | _ => ![0, 0, 0, 0]

theorem chartLightlikeBoundaryExample_interval_sq :
    minkowskiIntervalSq (minkowskiSep (chartLightlikeBoundaryExample 0) (chartLightlikeBoundaryExample 1)) = 0 := by
  have hsep :
      minkowskiSep (chartLightlikeBoundaryExample 0) (chartLightlikeBoundaryExample 1) = ![1, 1, 0, 0] := by
    funext i
    fin_cases i <;> simp [chartLightlikeBoundaryExample, minkowskiSep, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [hsep]
  simp [minkowskiIntervalSq, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem commutatorKernelIntervalMax_chartLightlikeBoundaryExample_0_1 :
    commutatorKernelIntervalMax chartLightlikeBoundaryExample 0 1 = 0 := by
  unfold commutatorKernelIntervalMax
  rw [chartLightlikeBoundaryExample_interval_sq]
  simp

theorem opCommutator_pauli_intervalMax_lightlike_boundary_example :
    opCommutator (Matrix.toEuclideanLin (pauliX_intervalMax chartLightlikeBoundaryExample 0 1))
      (Matrix.toEuclideanLin pauliY_comm) = 0 :=
  opCommutator_pauliX_intervalMax_pauliY_eq_zero_of_comm_kernel_eq_zero
    commutatorKernelIntervalMax_chartLightlikeBoundaryExample_0_1

end Hqiv.QM
