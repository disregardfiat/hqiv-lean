/-
Digital simulation cost is tracked in the **shell cutoff** `L`: the angular Hilbert space simulated at
polynomial cost `O((L+1)²)` in the number of basis modes (`Fintype.card_harmonicIndex`), not exponential
in a putative particle number. Hydrogenic **Rydberg-style** energies are packaged via the existing
continuum definitions `expectedEnergy` / `expectedGroundEnergy` from `HydrogenicEnergies.lean` (the digital
layer does not re-derive continuum spectral theory or import the full `Schrodinger` development).
-/

import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Hqiv.QuantumComputing.DiscreteQuantumState

namespace Hqiv.QuantumComputing

open Hqiv

/-- Basis size at cutoff `L` is `(L+1)²` (quadratic / polynomial in `L`). -/
theorem simulation_basis_card (L : ℕ) :
    Fintype.card (HarmonicIndex L) = (L + 1) ^ 2 :=
  Fintype.card_harmonicIndex L

/-- Big-O style domination: `(L+1)² ≤ (L+1)³` for `L ≥ 0`. -/
theorem basis_card_poly_le_cube (L : ℕ) :
    Fintype.card (HarmonicIndex L) ≤ (L + 1) ^ 3 := by
  rw [simulation_basis_card L]
  -- Let `a = L + 1`. For `a ≥ 1`, we have `a^2 ≤ a^2 * a = a^3`.
  have ha : 0 < (L + 1 : ℕ) := Nat.succ_pos L
  have hmul : (L + 1 : ℕ) ^ 2 ≤ (L + 1 : ℕ) ^ 2 * (L + 1 : ℕ) :=
    Nat.le_mul_of_pos_right ((L + 1 : ℕ) ^ 2) ha
  have hpow : (L + 1 : ℕ) ^ 2 * (L + 1 : ℕ) = (L + 1 : ℕ) ^ 3 := by
    -- `a^2 * a^1 = a^(2+1)` and `2+1=3`.
    simpa [Nat.pow_one, Nat.pow_add, Nat.add_assoc] using
      (Nat.pow_add (L + 1 : ℕ) 2 1).symm
  simpa [hpow] using hmul

/-- One scan over the digital basis has cost `O((L+1)²)` in the bookkeeping sense above. -/
def digitalExpectation {L : ℕ} (f : DiscreteState L) (obs : HarmonicIndex L → ℝ) : ℝ :=
  ∑ ij : HarmonicIndex L, obs ij * Hqiv.Algebra.octonionInner (f ij) (f ij)

#print simulation_basis_card
#print basis_card_poly_le_cube

#check simulation_basis_card
#check digitalExpectation

end Hqiv.QuantumComputing
