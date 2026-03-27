import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace Hqiv.QM

open scoped BigOperators

/-!
# Finite-dimensional Born normalization and measurement closure

This module lifts the two-component measurement bookkeeping to a finite
`Fin n` state space, proving Born-probability normalization and explicit
collapse-energy bookkeeping with auxiliary and birefringence-redshift channels.

SO(8)-closure interface hooks are intentionally kept in a separate module so
this file remains lightweight for routine QM work.
-/

/-- Finite real-carrier state with `n` outcomes. -/
abbrev StateN (n : ℕ) := Fin n → ℝ

/-- Redshifted observed energy channel (finite-state module-local version). -/
noncomputable def redshiftedEnergyN (Epost z : ℝ) : ℝ :=
  Epost / (1 + z)

/-- Birefringence-linked redshift in the HQIV "now" bookkeeping chain. -/
noncomputable def birefringenceRedshiftN (betaRad kappaBeta : ℝ) : ℝ :=
  Real.exp (betaRad / kappaBeta) - 1

theorem one_add_birefringenceRedshiftN (betaRad kappaBeta : ℝ) :
    1 + birefringenceRedshiftN betaRad kappaBeta = Real.exp (betaRad / kappaBeta) := by
  unfold birefringenceRedshiftN
  ring

theorem birefringenceRedshiftN_ne_neg_one (betaRad kappaBeta : ℝ) :
    birefringenceRedshiftN betaRad kappaBeta ≠ -1 := by
  unfold birefringenceRedshiftN
  have hexp : 0 < Real.exp (betaRad / kappaBeta) := Real.exp_pos (betaRad / kappaBeta)
  linarith

theorem redshiftedEnergyN_birefringence_balance
    (Epost betaRad kappaBeta : ℝ) :
    redshiftedEnergyN Epost (birefringenceRedshiftN betaRad kappaBeta)
      * Real.exp (betaRad / kappaBeta) = Epost := by
  unfold redshiftedEnergyN
  have hden : 1 + birefringenceRedshiftN betaRad kappaBeta ≠ 0 := by
    have hz : birefringenceRedshiftN betaRad kappaBeta ≠ -1 :=
      birefringenceRedshiftN_ne_neg_one betaRad kappaBeta
    intro hzero
    apply hz
    linarith
  rw [one_add_birefringenceRedshiftN]
  calc
    (Epost / Real.exp (betaRad / kappaBeta)) * Real.exp (betaRad / kappaBeta)
        = Epost * (Real.exp (betaRad / kappaBeta) / Real.exp (betaRad / kappaBeta)) := by ring
    _ = Epost * 1 := by rw [div_self (by
          have hpos : 0 < Real.exp (betaRad / kappaBeta) := Real.exp_pos _
          linarith)]
    _ = Epost := by ring

/-- Squared-norm (informational energy) on the finite carrier. -/
noncomputable def normSq {n : ℕ} (ψ : StateN n) : ℝ :=
  ∑ i : Fin n, (ψ i) ^ 2

/-- Born weight for outcome `i`. -/
noncomputable def bornWeight {n : ℕ} (ψ : StateN n) (i : Fin n) : ℝ :=
  (ψ i) ^ 2

/-- Born probability for outcome `i`. -/
noncomputable def bornProbN {n : ℕ} (ψ : StateN n) (i : Fin n) : ℝ :=
  bornWeight ψ i / normSq ψ

theorem normSq_nonneg {n : ℕ} (ψ : StateN n) : 0 ≤ normSq ψ := by
  unfold normSq
  exact Finset.sum_nonneg (fun i _ => by nlinarith [(sq_nonneg (ψ i))])

theorem normSq_pos_of_exists_nonzero {n : ℕ} (ψ : StateN n)
    (h : ∃ i : Fin n, ψ i ≠ 0) : 0 < normSq ψ := by
  rcases h with ⟨i0, hi0⟩
  have hterm : 0 < (ψ i0) ^ 2 := by
    have hsq : (ψ i0) ^ 2 ≠ 0 := by exact pow_ne_zero 2 hi0
    have hnn : 0 ≤ (ψ i0) ^ 2 := by nlinarith
    exact lt_of_le_of_ne hnn (Ne.symm hsq)
  have hrest_nonneg : 0 ≤ Finset.sum (Finset.univ.erase i0) (fun j => (ψ j) ^ 2) := by
    exact Finset.sum_nonneg (fun j hj => by nlinarith [(sq_nonneg (ψ j))])
  have hsplit : normSq ψ = (ψ i0) ^ 2 + Finset.sum (Finset.univ.erase i0) (fun j => (ψ j) ^ 2) := by
    have hsum := Finset.sum_erase_add (s := Finset.univ) (a := i0) (f := fun j : Fin n => (ψ j) ^ 2) (Finset.mem_univ i0)
    unfold normSq
    rw [← hsum]
    ac_rfl
  rw [hsplit]
  exact add_pos_of_pos_of_nonneg hterm hrest_nonneg

theorem bornProbN_nonneg {n : ℕ} (ψ : StateN n) (i : Fin n)
    (hpos : 0 < normSq ψ) : 0 ≤ bornProbN ψ i := by
  unfold bornProbN bornWeight
  have hnum : 0 ≤ (ψ i) ^ 2 := by nlinarith
  exact div_nonneg hnum (le_of_lt hpos)

theorem sum_bornWeight_eq_normSq {n : ℕ} (ψ : StateN n) :
    (∑ i : Fin n, bornWeight ψ i) = normSq ψ := by
  rfl

theorem sum_bornProbN_eq_one {n : ℕ} (ψ : StateN n)
    (hden : normSq ψ ≠ 0) :
    (∑ i : Fin n, bornProbN ψ i) = 1 := by
  unfold bornProbN bornWeight
  calc
    (∑ i : Fin n, (ψ i) ^ 2 / normSq ψ)
        = (∑ i : Fin n, (ψ i) ^ 2) / normSq ψ := by
            simp [Finset.sum_div]
    _ = normSq ψ / normSq ψ := by rfl
    _ = 1 := by exact div_self hden

/-- Outcome-conditioned collapse to basis outcome `i`. -/
def collapseTo {n : ℕ} (i : Fin n) (ψ : StateN n) : StateN n :=
  fun j => if j = i then ψ i else 0

theorem collapseTo_support {n : ℕ} (i : Fin n) (ψ : StateN n) :
    ∀ j : Fin n, j ≠ i → collapseTo i ψ j = 0 := by
  intro j hj
  unfold collapseTo
  simp [hj]

theorem normSq_collapseTo_eq_weight {n : ℕ} (i : Fin n) (ψ : StateN n) :
    normSq (collapseTo i ψ) = bornWeight ψ i := by
  unfold normSq collapseTo bornWeight
  simp

/-- Auxiliary transfer for selected outcome in finite-dimensional collapse. -/
noncomputable def auxTransferForOutcome {n : ℕ} (i : Fin n) (ψ : StateN n) : ℝ :=
  normSq ψ - normSq (collapseTo i ψ)

theorem measurement_energy_closure_with_aux_N {n : ℕ} (i : Fin n) (ψ : StateN n) :
    normSq ψ = normSq (collapseTo i ψ) + auxTransferForOutcome i ψ := by
  unfold auxTransferForOutcome
  ring

theorem auxTransferForOutcome_nonneg {n : ℕ} (i : Fin n) (ψ : StateN n) :
    0 ≤ auxTransferForOutcome i ψ := by
  unfold auxTransferForOutcome
  rw [normSq_collapseTo_eq_weight]
  unfold bornWeight normSq
  have hrest_nonneg : 0 ≤ Finset.sum (Finset.univ.erase i) (fun j => (ψ j) ^ 2) := by
    exact Finset.sum_nonneg (fun j hj => by nlinarith [(sq_nonneg (ψ j))])
  have hsplit :
      (∑ j : Fin n, (ψ j) ^ 2) = (ψ i) ^ 2 + Finset.sum (Finset.univ.erase i) (fun j => (ψ j) ^ 2) := by
    have hsum := Finset.sum_erase_add (s := Finset.univ) (a := i) (f := fun j : Fin n => (ψ j) ^ 2) (Finset.mem_univ i)
    rw [← hsum]
    ac_rfl
  rw [hsplit]
  nlinarith [hrest_nonneg]

theorem measurement_observed_energy_with_aux_and_birefringence_N
    {n : ℕ} (i : Fin n) (ψ : StateN n) (betaRad kappaBeta : ℝ) :
    normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ := by
  have haux : normSq ψ = normSq (collapseTo i ψ) + auxTransferForOutcome i ψ :=
    measurement_energy_closure_with_aux_N i ψ
  have hred :
      redshiftedEnergyN (normSq (collapseTo i ψ))
        (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
      = normSq (collapseTo i ψ) := by
    exact redshiftedEnergyN_birefringence_balance (normSq (collapseTo i ψ)) betaRad kappaBeta
  calc
    normSq ψ
        = normSq (collapseTo i ψ) + auxTransferForOutcome i ψ := haux
    _ = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ := by rw [hred]

end Hqiv.QM
