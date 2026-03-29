import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

/-!
# Pauli matrices: explicit **nonzero** matrix commutator (toy)

Standard Pauli `σ_x`, `σ_y` on `ℂ²`.  The commutator `[σ_x, σ_y]` is **nonzero** (proven via the
`(0,0)` entry), illustrating that noncommutative observables are easy to formalize before one
embeds CCR/Weyl relations into the HQIV lattice diagonal scaffold.

Names are suffixed `_comm` to avoid clashing with `UncertaintyPrinciple`’s `pauliX` / `pauliY` / `pauliZ`
when both modules appear in the same environment (e.g. `HQIVLEAN`).

Compare `Hqiv.QM.smearedField_opCommutator_eq_zero`: diagonal smeared fields commute.
-/

namespace Hqiv.QM

open Matrix

/-- Pauli `σ_x` (commutator toy; distinct name from `UncertaintyPrinciple.pauliX`). -/
noncomputable def pauliX_comm : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![(0 : ℂ), 1], ![1, 0]]

/-- Pauli `σ_y` (commutator toy; distinct name from `UncertaintyPrinciple.pauliY`). -/
noncomputable def pauliY_comm : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of ![![0, -Complex.I], ![Complex.I, 0]]

/-- Matrix commutator `AB - BA`. -/
noncomputable def matComm {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  A * B - B * A

theorem matComm_pauli_xy_entry00_ne_zero : matComm pauliX_comm pauliY_comm (0 : Fin 2) (0 : Fin 2) ≠ 0 := by
  unfold matComm pauliX_comm pauliY_comm
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.of_apply, Finset.sum_fin_eq_sum_range,
    Finset.sum_range_succ, Matrix.cons_val']
  intro h
  rw [sub_eq_zero] at h
  have hre := congr_arg Complex.re h
  have him := congr_arg Complex.im h
  norm_num at hre him

end Hqiv.QM
