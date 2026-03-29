import Hqiv.QuantumComputing.OSHoracle
import Hqiv.QuantumComputing.DigitalQuantumSimulation

/-!
# Density domain: where sparse tracking can (and cannot) beat dense angular simulation

This file does **not** compare quantum hardware to classical silicon. It compares two **classical**
implementations of the same finite digital model:

* **Dense track:** store one amplitude per harmonic index — `Fintype.card (HarmonicIndex L) = (L+1)²`
  slots (`DigitalQuantumSimulation`).
* **Sparse track:** store a list of `(wrapped index, octonion)` pairs (`OSHoracle.SparseRegister`).

**Memory crossover (proved):** if the sparse list length exceeds the angular basis dimension, the list
representation uses **more** storage cells than the dense vector — there is no memory edge.

**Computational caveat (types):** `applyGateSparse` builds a full `DiscreteState L` and applies
`HQIVGate.toEquiv` to it, so one step is not sub-linear in `(L+1)²` in this formalization; any
“speedup domain” is therefore about **support bookkeeping / pruning**, not a claim of o(B) gate
application unless the gate implementation is strengthened.

For the **idealized** ratio “dense cells / sparse cells” when `0 < |R| ≤ B`, see
`idealizedDenseVsSparseMemoryRatio`.
-/

namespace Hqiv.QuantumComputing

/-- Angular harmonic basis size at cutoff `L` (same as `sparseBasisCard` / `Fintype.card`). -/
abbrev basisDim (L : ℕ) : ℕ :=
  sparseBasisCard L

theorem basisDim_eq_card_harmonic (L : ℕ) : basisDim L = Fintype.card (HarmonicIndex L) := by
  rw [basisDim, sparseBasisCard, ← simulation_basis_card L]

theorem basisDim_pos (L : ℕ) : 0 < basisDim L := by
  simp [basisDim, sparseBasisCard]

theorem wrapIdx_lt_basisDim (L i : ℕ) : wrapIdx L i < basisDim L := by
  unfold wrapIdx basisDim sparseBasisCard
  refine Nat.mod_lt _ ?_
  exact Nat.pow_pos (Nat.succ_pos L)

/-- Bookkeeping upper bound for a dense state: one slot per basis element. -/
def denseStateStorageBound (L : ℕ) : ℕ :=
  basisDim L

/-- Bookkeeping upper bound for a sparse list: one cell per cons. -/
def sparseListStorageBound (_L : ℕ) (r : SparseRegister L) : ℕ :=
  r.length

theorem sparse_storage_le_dense_when_short_support (L : ℕ) (r : SparseRegister L)
    (h : r.length ≤ basisDim L) : sparseListStorageBound L r ≤ denseStateStorageBound L := by
  simpa [sparseListStorageBound, denseStateStorageBound] using h

/-- **Memory edge lost:** if the sparse list is longer than the basis, storing the list uses more
cells than storing a dense amplitude vector (idealized cell count). -/
theorem sparse_storage_worse_than_dense (L : ℕ) (r : SparseRegister L)
    (h : basisDim L < r.length) : denseStateStorageBound L < sparseListStorageBound L r := by
  simpa [sparseListStorageBound, denseStateStorageBound] using h

/-- One sparse gate step doubles list length (`OSHoracle`). -/
theorem one_step_sparse_length_doubles {L : ℕ} (g : HQIVGate L) (r : SparseRegister L) :
    (applyGateSparse g r).length = 2 * r.length :=
  applyGateSparse_length_eq_two_mul g r

/-- **Dynamic crossover:** after a single sparse gate, list length is `2 * r.length`; if that exceeds
the basis dimension, the sparse track already uses more storage cells than a dense amplitude vector. -/
theorem one_step_sparse_storage_worse_than_dense {L : ℕ} (g : HQIVGate L) (r : SparseRegister L)
    (h : basisDim L < 2 * r.length) :
    denseStateStorageBound L < sparseListStorageBound L (applyGateSparse g r) := by
  rw [sparseListStorageBound, denseStateStorageBound, one_step_sparse_length_doubles g r]
  exact h

/-- Idealized ratio: how many dense basis cells per sparse list cell (floor division; if
`r.length = 0`, the ratio is `0`). Meaningful when `r.length` is a modest fraction of `basisDim L`
and duplicates are absent or merged. -/
def idealizedDenseVsSparseMemoryRatio (L : ℕ) (r : SparseRegister L) : ℕ :=
  basisDim L / r.length

theorem idealizedRatio_le_basisDim (L : ℕ) (r : SparseRegister L) :
    idealizedDenseVsSparseMemoryRatio L r ≤ basisDim L := by
  unfold idealizedDenseVsSparseMemoryRatio
  exact Nat.div_le_self _ _

theorem idealizedRatio_ge_two_of (L : ℕ) (r : SparseRegister L) (hr : 0 < r.length)
    (h2 : 2 * r.length ≤ basisDim L) : 2 ≤ idealizedDenseVsSparseMemoryRatio L r := by
  unfold idealizedDenseVsSparseMemoryRatio
  exact (Nat.le_div_iff_mul_le hr).mpr h2

/-- Pair `(support length, basis dim)` for reporting density; not a `ℝ`-valued fraction in Lean. -/
def supportDensityPair (L : ℕ) (r : SparseRegister L) : ℕ × ℕ :=
  (r.length, basisDim L)

end Hqiv.QuantumComputing
