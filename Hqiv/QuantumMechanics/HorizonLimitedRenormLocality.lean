import Mathlib.Data.Real.Basic
import Hqiv.QuantumMechanics.HorizonLimitedQM_QFT_Closure

namespace Hqiv.QM

/-!
# Horizon-limited continuum closure (renormalization + locality package)

This module packages the remaining continuum-QFT bridge requirements into a
single formal assumption bundle and proves the corresponding closure statement.
It is designed to align with standard QFT criteria while keeping the domain
explicitly horizon-limited.
-/

/-- Assumption bundle for horizon-limited continuum closure. -/
structure HorizonContinuumAxioms where
  shell_to_harmonic_limit : Prop
  renormalization_in_domain : Prop
  microcausality_in_domain : Prop
  spin_statistics_in_domain : Prop
  cptp_density_closure_in_domain : Prop
  cluster_decomposition_in_domain : Prop
  scattering_consistency_in_domain : Prop

/-- Master closure claim in the horizon-limited continuum domain. -/
def HorizonContinuumClosureStatement : Prop :=
  ∃ A : HorizonContinuumAxioms,
    A.shell_to_harmonic_limit ∧
    A.renormalization_in_domain ∧
    A.microcausality_in_domain ∧
    A.spin_statistics_in_domain ∧
    A.cptp_density_closure_in_domain ∧
    A.cluster_decomposition_in_domain ∧
    A.scattering_consistency_in_domain

/--
If the continuum bridge axioms hold, then the horizon-limited continuum
closure statement holds.
-/
theorem horizon_continuum_closure_of_axioms
    (A : HorizonContinuumAxioms)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hSpin : A.spin_statistics_in_domain)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    HorizonContinuumClosureStatement := by
  refine ⟨A, hShell, hRenorm, hLocal, hSpin, hCptp, hCluster, hScatter⟩

/--
Convenience theorem: the finite masterpiece closure plus continuum assumptions
gives the full horizon-limited QM/QFT closure package.
-/
theorem horizon_qm_qft_full_package
    {n m : ℕ}
    (ψ : StateN n) (hψ : ∃ i : Fin n, ψ i ≠ 0)
    (κ : StochasticKernel n m) (i : Fin n) (betaRad kappaBeta : ℝ)
    (A : HorizonContinuumAxioms)
    (hShell : A.shell_to_harmonic_limit)
    (hRenorm : A.renormalization_in_domain)
    (hLocal : A.microcausality_in_domain)
    (hSpin : A.spin_statistics_in_domain)
    (hCptp : A.cptp_density_closure_in_domain)
    (hCluster : A.cluster_decomposition_in_domain)
    (hScatter : A.scattering_consistency_in_domain) :
    ((∑ j : Fin m, (pushDist κ (bornDistOfState ψ hψ)).prob j) = 1) ∧
    (normSq ψ
      = redshiftedEnergyN (normSq (collapseTo i ψ))
          (birefringenceRedshiftN betaRad kappaBeta)
          * Real.exp (betaRad / kappaBeta)
        + auxTransferForOutcome i ψ) ∧
    HorizonContinuumClosureStatement := by
  refine ⟨?_, ?_, ?_⟩
  · exact (horizon_masterpiece_finite_closure ψ hψ κ i betaRad kappaBeta).1
  · exact (horizon_masterpiece_finite_closure ψ hψ κ i betaRad kappaBeta).2
  · exact horizon_continuum_closure_of_axioms A hShell hRenorm hLocal hSpin hCptp hCluster hScatter

end Hqiv.QM
