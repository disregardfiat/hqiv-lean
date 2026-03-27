import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Hqiv.QuantumMechanics.BornMeasurementFinite

namespace Hqiv.QM

open scoped BigOperators

/-!
# Horizon-limited QM/QFT closure

This module packages an end-to-end "in-domain" closure layer:

1. finite-channel composition closure on `StateN`,
2. Born normalization for nonzero finite states,
3. measurement ledger closure (aux + redshift/birefringence channels),
4. compositional marginal-invariance lemma (no-signaling style scaffold).

It is intentionally horizon-limited and representation-level, and provides
fully normalized finite Born distributions plus finite stochastic-channel
composition closure on top of the measurement ledger.
-/

/-- A horizon domain witness: finite shell cutoff and finite carrier cutoff. -/
structure HorizonDomain where
  shellCutoff : ℕ
  carrierCutoff : ℕ

/-- Finite channel on `StateN n` with norm-squared preservation. -/
structure FiniteChannel (n : ℕ) where
  map : StateN n → StateN n
  preservesNormSq : ∀ ψ, normSq (map ψ) = normSq ψ

/-- Identity finite channel. -/
def finiteChannelId (n : ℕ) : FiniteChannel n where
  map := fun ψ => ψ
  preservesNormSq := by intro ψ; rfl

/-- Composition of finite channels. -/
def finiteChannelComp {n : ℕ} (C2 C1 : FiniteChannel n) : FiniteChannel n where
  map := fun ψ => C2.map (C1.map ψ)
  preservesNormSq := by
    intro ψ
    rw [C2.preservesNormSq, C1.preservesNormSq]

theorem finiteChannelComp_assoc {n : ℕ}
    (C3 C2 C1 : FiniteChannel n) :
    finiteChannelComp C3 (finiteChannelComp C2 C1)
      = finiteChannelComp (finiteChannelComp C3 C2) C1 := by
  cases C1
  cases C2
  cases C3
  rfl

theorem finiteChannelComp_id_left {n : ℕ} (C : FiniteChannel n) :
    finiteChannelComp (finiteChannelId n) C = C := by
  cases C
  rfl

theorem finiteChannelComp_id_right {n : ℕ} (C : FiniteChannel n) :
    finiteChannelComp C (finiteChannelId n) = C := by
  cases C
  rfl

/-- Born normalization for nonzero finite states. -/
theorem born_probs_sum_one_of_nonzero_state
    {n : ℕ} (ψ : StateN n) (h : ∃ i : Fin n, ψ i ≠ 0) :
    (∑ i : Fin n, bornProbN ψ i) = 1 := by
  apply sum_bornProbN_eq_one
  have hpos : 0 < normSq ψ := normSq_pos_of_exists_nonzero ψ h
  linarith

/--
No-signaling-style marginal invariance predicate for a chosen marginal witness `F`.
If `F` is invariant under local/update channels, composition stays invariant.
-/
def MarginalInvariant {n : ℕ} (F : StateN n → ℝ) (C : FiniteChannel n) : Prop :=
  ∀ ψ, F (C.map ψ) = F ψ

theorem marginalInvariant_comp {n : ℕ}
    (F : StateN n → ℝ) (C2 C1 : FiniteChannel n)
    (h1 : MarginalInvariant F C1)
    (h2 : MarginalInvariant F C2) :
    MarginalInvariant F (finiteChannelComp C2 C1) := by
  intro ψ
  calc
    F ((finiteChannelComp C2 C1).map ψ) = F (C1.map ψ) := by
      exact h2 (C1.map ψ)
    _ = F ψ := by
      exact h1 ψ

/-- Finite measurement ledger closure: pre-energy = post + auxiliary transfer. -/
theorem horizon_measurement_energy_closure_with_aux
    {n : ℕ} (i : Fin n) (ψ : StateN n) :
    normSq ψ = normSq (collapseTo i ψ) + auxTransferForOutcome i ψ :=
  measurement_energy_closure_with_aux_N i ψ

/--
Finite measurement ledger with observed redshift/birefringence channel:
pre-energy equals observed post-energy channel plus auxiliary transfer.
-/
theorem horizon_measurement_observed_energy_closure
    {n : ℕ} (i : Fin n) (ψ : StateN n) (betaRad kappaBeta : ℝ) :
    normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ :=
  measurement_observed_energy_with_aux_and_birefringence_N i ψ betaRad kappaBeta

/--
Horizon-limited closure statement (representation-level):
finite channels preserve norm-squared and measurement closes the ledger with
auxiliary and redshift channels.
-/
theorem horizon_limited_qm_closure_statement
    {n : ℕ} (C : FiniteChannel n) (ψ : StateN n) :
    normSq (C.map ψ) = normSq ψ := by
  exact C.preservesNormSq ψ

/-! ## Finite distributions and stochastic (CPTP-style classical) channels -/

/-- Finite normalized distribution on `Fin n`. -/
structure DistN (n : ℕ) where
  prob : Fin n → ℝ
  nonneg : ∀ i, 0 ≤ prob i
  sum_one : (∑ i : Fin n, prob i) = 1

/-- Born distribution induced by a nonzero state. -/
noncomputable def bornDistOfState {n : ℕ} (ψ : StateN n)
    (h : ∃ i : Fin n, ψ i ≠ 0) : DistN n where
  prob := bornProbN ψ
  nonneg := by
    intro i
    exact bornProbN_nonneg ψ i (normSq_pos_of_exists_nonzero ψ h)
  sum_one := by
    exact born_probs_sum_one_of_nonzero_state ψ h

/-- Transition kernel `n -> m` with nonnegative rows that each sum to one. -/
structure StochasticKernel (n m : ℕ) where
  K : Fin n → Fin m → ℝ
  nonneg : ∀ i j, 0 ≤ K i j
  row_sum_one : ∀ i, (∑ j : Fin m, K i j) = 1

/-- Push-forward of a finite distribution through a stochastic kernel. -/
noncomputable def pushDist {n m : ℕ}
    (κ : StochasticKernel n m) (p : DistN n) : DistN m where
  prob := fun j => ∑ i : Fin n, p.prob i * κ.K i j
  nonneg := by
    intro j
    exact Finset.sum_nonneg (fun i _ =>
      mul_nonneg (p.nonneg i) (κ.nonneg i j))
  sum_one := by
    calc
      (∑ j : Fin m, (∑ i : Fin n, p.prob i * κ.K i j))
          = ∑ i : Fin n, (∑ j : Fin m, p.prob i * κ.K i j) := by
              simpa using Finset.sum_comm
      _ = ∑ i : Fin n, p.prob i * (∑ j : Fin m, κ.K i j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [Finset.mul_sum]
      _ = ∑ i : Fin n, p.prob i * 1 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [κ.row_sum_one i]
      _ = ∑ i : Fin n, p.prob i := by simp
      _ = 1 := p.sum_one

/-- Composition of stochastic kernels. -/
noncomputable def composeKernel {n m l : ℕ}
    (κ2 : StochasticKernel m l) (κ1 : StochasticKernel n m) : StochasticKernel n l where
  K := fun i k => ∑ j : Fin m, κ1.K i j * κ2.K j k
  nonneg := by
    intro i k
    exact Finset.sum_nonneg (fun j _ =>
      mul_nonneg (κ1.nonneg i j) (κ2.nonneg j k))
  row_sum_one := by
    intro i
    calc
      (∑ k : Fin l, (∑ j : Fin m, κ1.K i j * κ2.K j k))
          = ∑ j : Fin m, (∑ k : Fin l, κ1.K i j * κ2.K j k) := by
              simpa using Finset.sum_comm
      _ = ∑ j : Fin m, κ1.K i j * (∑ k : Fin l, κ2.K j k) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Finset.mul_sum]
      _ = ∑ j : Fin m, κ1.K i j * 1 := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [κ2.row_sum_one j]
      _ = ∑ j : Fin m, κ1.K i j := by simp
      _ = 1 := κ1.row_sum_one i

theorem pushDist_compose {n m l : ℕ}
    (κ2 : StochasticKernel m l) (κ1 : StochasticKernel n m) (p : DistN n) :
    (pushDist κ2 (pushDist κ1 p)).prob
      = (pushDist (composeKernel κ2 κ1) p).prob := by
  funext k
  change (∑ j : Fin m, (∑ i : Fin n, p.prob i * κ1.K i j) * κ2.K j k)
      = (∑ i : Fin n, p.prob i * (∑ j : Fin m, κ1.K i j * κ2.K j k))
  calc
    (∑ j : Fin m, (∑ i : Fin n, p.prob i * κ1.K i j) * κ2.K j k)
        = ∑ j : Fin m, (∑ i : Fin n, (p.prob i * κ1.K i j) * κ2.K j k) := by
            refine Finset.sum_congr rfl ?_
            intro j _
            rw [Finset.sum_mul]
    _ = ∑ j : Fin m, (∑ i : Fin n, p.prob i * (κ1.K i j * κ2.K j k)) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          refine Finset.sum_congr rfl ?_
          intro i _
          ring
    _ = ∑ i : Fin n, (∑ j : Fin m, p.prob i * (κ1.K i j * κ2.K j k)) := by
          simpa using Finset.sum_comm
    _ = (∑ i : Fin n, p.prob i * (∑ j : Fin m, κ1.K i j * κ2.K j k)) := by
          refine Finset.sum_congr rfl ?_
          intro i _
          rw [Finset.mul_sum]

/--
Master horizon-limited closure theorem (finite layer):
for any nonzero state, Born probabilities are normalized; any finite stochastic
post-processing preserves normalization; and measurement energy bookkeeping is
closed via auxiliary + birefringence/redshift channels.
-/
theorem horizon_masterpiece_finite_closure
    {n m : ℕ} (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
    (normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ) := by
  refine ⟨?_, ?_⟩
  · exact (pushDist κ (bornDistOfState ψ hψ)).sum_one
  · exact horizon_measurement_observed_energy_closure i ψ betaRad kappaBeta

end Hqiv.QM
