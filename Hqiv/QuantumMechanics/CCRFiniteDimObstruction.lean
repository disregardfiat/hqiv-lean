import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-!
# No **exact** CCR on a **fixed** finite matrix algebra

The Heisenberg relation `[X, P] = i ℏ` (normalized to `[A, B] = 1` in units with `ℏ = 1`)
cannot hold as an **identity of n×n matrices** for fixed `n` with `A, B ∈ Mat_{n×n}(ℂ)`:
`Tr([A,B]) = 0` but `Tr(I) = n`.  This is pure linear algebra.

**HQIV scope:** observables are not required to live on a single global infinite-dimensional space.
The formalism is built for **finite** causal **patches** (past light cone, horizon-limited modes,
shell cutoffs) and **limits** as accessible resources grow (`shell_to_harmonic_limit`, asymptotic
ratio statements)—not for importing full textbook `L²(ℝ³)` QFT as a precondition.

So: the obstruction rules out **one** bad formalization (“exact CCR as literal fixed `Mat_n`”);
it does **not** say the project must prove Stone–von Neumann or use `ℓ²(ℕ)`.  Truncated / effective
brackets, patchwise operators, and flattened potentials in the light-cone narrative stay inside
finite-dimensional linear algebra at each stage.

**Interval-weighted commutators:** `IntervalMaxOperatorCommutator` inserts the causal functional
`commutatorKernelIntervalMax` as a **scalar on one factor** (Pauli carrier), giving
`[κ σ_x, σ_y] = κ [σ_x, σ_y]` on matrices and the matching `opCommutator` on `LatticeHilbert 2` — still
traceless, not `κ·I`.
-/

namespace Hqiv.QM

open Matrix

/-- Trace of a commutator is zero (`Tr(AB) = Tr(BA)`). -/
theorem Matrix.trace_commutator_eq_zero {n : Type*} [Fintype n] [DecidableEq n]
    (A B : Matrix n n ℂ) : (A * B - B * A).trace = 0 := by
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- No pair of finite matrices satisfies the normalized CCR `[A,B] = I` when `n` is nonempty. -/
theorem not_exists_matrix_CCR_one {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n] :
    ¬ ∃ A B : Matrix n n ℂ, A * B - B * A = 1 := by
  rintro ⟨A, B, h⟩
  have h0 := congr_arg Matrix.trace h
  rw [Matrix.trace_commutator_eq_zero, Matrix.trace_one] at h0
  have hcard : Fintype.card n = 0 := (Nat.cast_eq_zero (R := ℂ)).1 h0.symm
  linarith [Fintype.card_pos (α := n), hcard]

end Hqiv.QM
