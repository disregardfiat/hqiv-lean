import Hqiv.QuantumMechanics.HorizonLimitedRenormLocality
import Hqiv.QuantumMechanics.PatchIntervalMaxSmeared

namespace Hqiv.QM

/-!
# Continuum many-body QFT: aliases onto the horizon closure bundle

This module depends on `HorizonLimitedRenormLocality` (and thus on
`SpinStatistics`). Import it when you want **one-line** access to the full
`HorizonContinuumClosureStatementCoreHQIV` package under many-body naming.

For a dependency-light scaffold + the shell/harmonic `Tendsto` lemma, use
`ContinuumManyBodyQFTScaffold` instead.

Partial continuum closure with the proved shell/harmonic ratio bridge and **structured**
scaffold witnesses for renorm/cluster/scattering lives in `HorizonLimitedRenormLocality` as
`horizonContinuumAxiomsMinimal_ratioWitness` and `continuum_many_body_closure_ratioWitness_trivialRest`.

To pair that pipeline with continuum O–Maxwell on `Fin 4 → ℝ`, import
`Hqiv.Physics.LightConeMaxwellQFTBridge` (`LightConeFunctionalBridge`, `MaxwellQFTChart`).
-/

/-- Same as `HorizonContinuumClosureStatementCoreHQIV`. -/
abbrev ContinuumManyBodyQFT_InDomainStatement : Prop :=
  HorizonContinuumClosureStatementCoreHQIV

/-- Continuum closure from `HorizonContinuumAxiomsMinimal` + HQIV discharges. -/
abbrev continuum_many_body_closure_minimal_HQIV :=
  @horizon_continuum_closure_minimal_HQIV

/-- Finite + continuum full package (minimal axioms). -/
abbrev continuum_many_body_qft_full_package_minimal_HQIV :=
  @horizon_qm_qft_full_package_minimal_HQIV

/-- The **scalar** interval-max microcausality scaffold (`microcausality_in_domain_minkowski_interval_scaffold`)
is complemented by proved **operator** smearing/vanishing lemmas in `PatchIntervalMaxSmeared` (same η-spacelike
hypothesis kills both `commutatorKernelIntervalMax` and the Pauli commutator lift).  The formal
`HorizonContinuumAxiomsMinimal.microcausality_in_domain` field for `…_minkowskiIntervalWitness` remains the
scalar `Prop`; this declaration is documentation + a single import anchor. -/
theorem continuum_interval_max_microcausality_operator_layer_notes :
    microcausality_in_domain_minkowski_interval_scaffold ∧
      (∀ (chart : EventChart) (φ : Fin 4 → Fin 4 → ℝ),
        (∀ i j, φ i j ≠ 0 → spacelikeRelationMinkowski chart i.val j.val) →
          smearedOpIntervalMax chart φ = 0) :=
  ⟨microcausality_in_domain_minkowski_interval_scaffold_holds,
    fun chart φ h => smearedOpIntervalMax_eq_zero_of_spacelike_support chart φ h⟩

end Hqiv.QM
