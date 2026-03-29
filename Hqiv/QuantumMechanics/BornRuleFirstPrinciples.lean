import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

import Hqiv.QuantumMechanics.BornMeasurementFinite

/-!
# Born rule from first principles (finite `Fin n` carrier)

This module proves that the **Born weights** `|ψᵢ|²` / `‖ψ‖²` used in
`BornMeasurementFinite` are not an ad hoc choice: they are the **unique**
normalized nonnegative probability assignment satisfying **amplitude--square
coherence**—the requirement that outcome probabilities are proportional to squared
amplitudes in every pair of directions.

Mathematically this is the standard finite-dimensional argument behind the Born
rule (ratio uniqueness); we package it as a single hypothesis class so other
modules can cite `bornProbN_unique_of_coherence` instead of assuming Born
probabilities.

No new physics axioms: the only structural input is coherence + normalization.
-/

namespace Hqiv.QM

open scoped BigOperators
open Finset

/-- Squared-amplitude coherence: probabilities track amplitude squares pairwise
(`pᵢ |ψⱼ|² = pⱼ |ψᵢ|²`), the usual “Born ratios” condition without naming `p` yet. -/
def BornCoherent {n : ℕ} (ψ : StateN n) (p : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, (ψ j) ^ 2 * p i = (ψ i) ^ 2 * p j

theorem bornProbN_coherent {n : ℕ} (ψ : StateN n) (hden : normSq ψ ≠ 0) :
    BornCoherent ψ (bornProbN ψ) := by
  intro i j
  unfold bornProbN bornWeight
  field_simp [hden]

/-- **Uniqueness (first principles):** any nonnegative probability vector that sums to `1`
and is Born-coherent for nonzero `ψ` equals `bornProbN ψ`. -/
theorem bornProbN_unique_of_coherence {n : ℕ} (ψ : StateN n) (p : Fin n → ℝ)
    (hsum : (∑ i : Fin n, p i) = 1)
    (hn : ∀ i : Fin n, 0 ≤ p i)
    (hcoh : BornCoherent ψ p)
    (hψ : ∃ k : Fin n, ψ k ≠ 0) :
    ∀ i : Fin n, p i = bornProbN ψ i := by
  have hpos : 0 < normSq ψ := normSq_pos_of_exists_nonzero ψ hψ
  have hden : normSq ψ ≠ 0 := ne_of_gt hpos
  rcases hψ with ⟨j0, hj0⟩
  have hj0sq : 0 < (ψ j0) ^ 2 := by
    have : (ψ j0) ^ 2 ≠ 0 := pow_ne_zero 2 hj0
    have nn : 0 ≤ (ψ j0) ^ 2 := by nlinarith
    exact lt_of_le_of_ne nn (Ne.symm this)
  -- `p j0 = (ψ j0)² / ‖ψ‖²` from summing coherence against `j0`
  have hsumj0 :
      ((ψ j0) ^ 2 : ℝ) * (∑ i : Fin n, p i) = p j0 * normSq ψ := by
    calc
      ((ψ j0) ^ 2 : ℝ) * (∑ i : Fin n, p i)
          = ∑ i : Fin n, ((ψ j0) ^ 2 * p i) := by rw [Finset.mul_sum]
      _ = ∑ i : Fin n, ((ψ i) ^ 2 * p j0) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            exact hcoh i j0
      _ = ∑ i : Fin n, (p j0 * (ψ i) ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro i _; ring
      _ = p j0 * (∑ i : Fin n, (ψ i) ^ 2) := by
            rw [← mul_sum (Finset.univ : Finset (Fin n)) (fun i : Fin n => (ψ i) ^ 2) (p j0)]
      _ = p j0 * normSq ψ := by rw [normSq]
  rw [hsum] at hsumj0
  simp only [mul_one] at hsumj0
  have hpj0 : p j0 = (ψ j0) ^ 2 / normSq ψ := by
    field_simp [hden] at hsumj0 ⊢
    linarith
  intro i
  by_cases hi : ψ i = 0
  · -- zero amplitude ⇒ zero probability on both sides
    have hci0 : (ψ j0) ^ 2 * p i = 0 := by
      have h := hcoh i j0
      rw [hi] at h
      simpa [zero_pow two_ne_zero, mul_zero] using h
    have hψsq0 : (ψ j0) ^ 2 ≠ 0 := ne_of_gt hj0sq
    have pi0 : p i = 0 := by
      rcases mul_eq_zero.mp hci0 with h | h
      · exact (hψsq0 h).elim
      · exact h
    rw [pi0]
    unfold bornProbN bornWeight
    rw [hi]
    simp only [zero_pow (Nat.succ_ne_zero 1), zero_div]
  · -- nonzero amplitude: ratio from coherence with `j0`
    have hci := hcoh i j0
    rw [hpj0] at hci
    unfold bornProbN bornWeight
    field_simp [hden, hi] at hci ⊢
    have hpi : 0 ≤ p i := hn i
    have hpj0_nn : 0 ≤ p j0 := hn j0
    nlinarith [hpi, hpj0_nn, hj0sq, hpos]

end Hqiv.QM
