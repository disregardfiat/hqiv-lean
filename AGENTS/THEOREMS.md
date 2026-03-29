# Theorems and defs with usable outputs

Lean names are given in **fully qualified** form where helpful; short names assume `open Hqiv` or the module namespace as documented. Use `#check` / `grep` in-repo for the exact type.

## Discrete light cone (`Hqiv.Geometry.OctonionicLightCone`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.latticeSimplexCount` | Stars-and-bars count on the 3D null lattice at shell `m`. |
| `Hqiv.latticeSimplexCount_eq` | Closed form `latticeSimplexCount m = (m+2)(m+1)`. |
| `Hqiv.cumLatticeSimplexCount_closed` | Hockey-stick / closed form for cumulative count. |
| `Hqiv.available_modes` | ℝ-valued mode budget at shell `m` (4·(m+2)(m+1)); ties to octonion factor via `available_modes_octonion`. |
| `Hqiv.new_modes` | Incremental new modes; `new_modes_succ` relates successive shells. |
| `Hqiv.alpha` / `Hqiv.alpha_eq_3_5` | **Sole** HQIV curvature-imprint exponent: `α = 3/5` (proved); physical derivation in companion HQIV + Brodie 2026 (see `AGENTS/ASSUMPTIONS.md` §1b). |
| `Hqiv.latticeAlphaRatio_eq_alpha` | Discrete ratio equals `α` for every `n`. |
| `Hqiv.alpha_gamma_forced_pair` / `Hqiv.lattice_imprint_ratio_forced_three_fifths` | `AlphaGammaForcedByLattice`: joint uniqueness `α = 3/5`, `γ = 2/5`, `α + γ = 1`; per-shell imprint ratio equals `3/5`. |
| `Hqiv.curvature_norm_*` / `Hqiv.deltaE_eq` | Curvature norm and δ_E imprint from the combinatorial structure. |
| `Hqiv.curvature_integral_ge_harmonic` / `curvature_integral_le_harmonic_mul_log` | Analytic sandwich for growth of curvature integral. |
| `Hqiv.omega_k_at_horizon` / `Hqiv.omega_k_partial_tends_to_atTop` | Horizon-indexed curvature ratio and asymptotic behaviour. |

## HQVM metric (`Hqiv.Geometry.HQVMetric`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.HQVM_lapse` | ADM lapse `N = 1 + Φ + φ t` (informational-energy / monogamy story in module doc). |
| `Hqiv.timeAngle` | `φ * t` piece tied to horizon coupling in docs. |
| `Hqiv.gamma_HQIV` / `Hqiv.gamma_eq_2_5` | **Sole** HQIV monogamy / horizon-overlap coefficient: `γ := 1 − α`, proved `γ = 2/5`; same external provenance as `α` (companion HQIV + Brodie 2026). |
| `Hqiv.G_eff` / Friedmann-related defs | Effective `G` as function of `φ`; homogeneous-limit statements in-file. |

## SM–GR unification (`Hqiv.Physics.SM_GR_Unification`, namespace `Hqiv`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.alpha_derived` | Same canonical `alpha = 3/5` (`SM_GR_Unification`; provenance: companion HQIV + Brodie 2026). |
| `Hqiv.gamma_derived` | Same canonical `gamma_HQIV = 2/5`. |
| `Hqiv.alpha_GUT_eq_1_42` | `α_GUT = 1/42`. |
| `Hqiv.one_over_alpha_EM_derived` / `Hqiv.one_over_alpha_EM_derived_closed_form` | `1/α_eff` at `φ(m)` expanded to `42 * (1 + c·(3/5)·log(2(m+1)+1))` (no extra lattice parameters). |
| `Hqiv.electroweakPhiShell` / `Hqiv.one_over_alpha_EM_derived_electroweak_closed` | Electroweak shell `referenceM+1` → `log` argument `13`. |
| `Hqiv.one_over_alpha_EM_at_MZ_eq` | Numeric `1/α_EM(M_Z) = 127.9` as `rfl` (paper-aligned witness; see `one_over_alpha_EM_derived_*` for symbolic derivation). |
| `Hqiv.HQIV_satisfies_YangMills_SM_GR_Unification` | Main “unification satisfied” proposition bundle. |
| `Hqiv.sm_constants_at_now_derived` | Packaging of derived-at-now constants (see theorem statement). |
| `Hqiv.higgs_mass_from_proton_mass` / `Hqiv.higgs_mass_numerical` | Higgs scale from proton anchor + numeric literal. |
| `Hqiv.m_proton_MeV_in_interval` / `Hqiv.m_neutron_MeV_in_interval` | Baryon mass intervals in MeV (paper-style). |

## Conserved-content mass bridge (`Hqiv.Physics.ConservedContentMassBridge`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.FermionContentClass` | Inductive ν / charged lepton / quark (narrative: 1 / 2 / 3 Fano triples). |
| `Hqiv.Physics.conservedTripleCount` | Maps each class to `1`, `2`, or `3`. |
| `Hqiv.Physics.intrinsicWaveComplexity` | `(conservedTripleCount c)²` with strict ordering lemmas. |
| `Hqiv.Physics.m_nu_e_derived_lt_m_tau_from_resonance` | Derived ν\_e scale `<` τ witness (`m_tau_from_resonance`). |
| `Hqiv.Physics.m_tau_from_resonance_lt_m_top_GeV` | τ witness `<` top GeV anchor. |
| `Hqiv.Physics.observed_mass_hierarchy_ν_e_tau_top` | Conjunction of the two strict inequalities (same ℝ units as the witness defs). |
| `Hqiv.Physics.massScalingAnsatz` | `k * l² * effCorrected δ m` (ties to `GlobalDetuning`; `k` is an explicit positive scale, not derived from δ_E in this file). |
| `Hqiv.Physics.massScalingAnsatz_lt_of_lt_l` / `massScalingAnsatz_lt_of_lt_m` | Strict monotonicity in `l` (fixed shell) and in shell `m` (fixed `l`), under `RindlerDenDeltaPos` / `0 ≤ δ` as stated. |
| `Hqiv.Physics.neutrinoShellCandidate` | `Finset.Icc 4 6` (candidate small-`m` band for the ν narrative). |
| `Hqiv.Physics.referenceNeutrinoShell_mem` | `5 ∈ neutrinoShellCandidate`. |

## SO(8) closure (`Hqiv.GeneratorsLieClosure`, `Hqiv.SO8Closure`, `Hqiv.Algebra.SO8ClosureAbstract`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.so8_generators_linear_independent` | 28 generators linearly independent over ℝ. |
| `Hqiv.lieBracket_in_span` | Closure of Lie bracket in span of generators (coefficient expansion). |
| `Hqiv.generators_from_octonion_closure` | Narrative bridge: generators from octonion/Lie data (see statement). |
| `Hqiv.Algebra.span_G2_union_Delta_le_span_so8Generator` / `Hqiv.Algebra.finrank_span_G2_union_Delta_le_15` / `Hqiv.Algebra.exists_so8Generator_not_mem_span_G2_union_Delta` | Linear span of `G₂ ∪ {Δ}` is **≤15**-dimensional and lies in `span(so8)`; cannot exhaust 28-dim `𝔰𝔬(8)` (`SO8ClosureAbstract`). |
| `Hqiv.QM.opCommutator_smearedOpIntervalMax_pair` | Bilinear (double) sum for `opCommutator` of two smeared interval–max Pauli operators (`PatchIntervalMaxSmeared`). |
| `Hqiv.QM.continuum_interval_max_microcausality_operator_layer_notes` | Scalar interval-max microcausality + operator smearing vanishing packaged (`ContinuumManyBodyQFTClosureLink`). |

## Spin–statistics (`Hqiv.Physics.SpinStatistics`, namespace `Hqiv.Physics`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.HQIV_satisfies_SpinStatistics_from_triality_and_causality` | Main constructive satisfaction statement used by QM/QFT bridge modules. |

## QM / QFT horizon packages (`Hqiv.QuantumMechanics.*`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.QM.bornProbN_unique_of_coherence` | Finite `Fin n`: normalized nonnegative `p` with `BornCoherent ψ p` is uniquely `bornProbN ψ` (`BornRuleFirstPrinciples`). |
| `Hqiv.QM.born_from_coherence_unique` | Alias for `bornProbN_unique_of_coherence` (`BornGleasonDecisionScaffold`). |
| `Hqiv.QM.GleasonAnalyticTarget` / `Hqiv.QM.DecisionTheoreticBornTarget` | Scaffold types documenting the **Gleason** (projection-lattice measure) and **decision-theoretic Born** programs; not analytic proofs—see module doc (`BornGleasonDecisionScaffold`). |
| `Hqiv.QM.opCommutator` / `Hqiv.QM.smearedField_opCommutator_eq_zero` | Operator commutator on `LatticeHilbert n`; diagonal smeared fields commute (`HorizonFreeFieldScaffold`). |
| `Hqiv.QM.fieldOpFromChart` / `Hqiv.QM.fieldOpFromChart_microcausal_op` | Chart coordinates as weights on `LatticeHilbert 4`; abelian ⇒ commutator `0` (`MinkowskiFieldOperatorScaffold`). |
| `Hqiv.QM.matComm` / `Hqiv.QM.matComm_pauli_xy_entry00_ne_zero` | Pauli matrices: **nonzero** commutator entry (`PauliCommutatorExample`). |
| `Hqiv.QM.pauliX_intervalMax` / `Hqiv.QM.opCommutator_pauliX_intervalMax_pauliY` / `Hqiv.QM.opCommutator_toEuclideanLin_matComm` | Interval–max `max 0 η` as coefficient on `σ_x`; genuine `matComm` / `opCommutator` on `ℂ²` (`IntervalMaxOperatorCommutator`; not literal `[A,B]=I`, see `CCRFiniteDimObstruction`). |
| `Hqiv.QM.opCommutator_sum_finset_first` / `Hqiv.QM.opCommutator_sum_univ_first` | `opCommutator` is linear in the **first** argument; commutes with finite `Finset`/`Fintype` sums (`HorizonFreeFieldScaffold`). |
| `Hqiv.QM.opCommutator_pauliX_intervalMax_pauliY_eq_zero_of_comm_kernel_eq_zero` / `Hqiv.QM.chartLightlikeBoundaryExample` / `Hqiv.QM.opCommutator_pauli_intervalMax_lightlike_boundary_example` | `κ = max 0 η = 0` (lightlike boundary) ⇒ Pauli commutator lift `0` (`IntervalMaxOperatorCommutator`). |
| `Hqiv.QM.WeightSupportInRegionPair` / `Hqiv.QM.smearedOpIntervalMax` / `Hqiv.QM.smearedOpIntervalMax_patchEventChartFour_eq_zero_of_disjoint_spatial_regions` / `Hqiv.QM.opCommutator_smearedOpIntervalMax_pauliY_eq_zero_of_spacelike_support` | Bilinear smearing of interval–max Pauli ops on the patch; vanishing on η-spacelike support; disjoint spatial regions ⇒ `0` (`PatchIntervalMaxSmeared`). |
| `Hqiv.QM.Matrix.trace_commutator_eq_zero` / `Hqiv.QM.not_exists_matrix_CCR_one` | Trace kills **exact** `[A,B]=I` on fixed `Mat_{n×n}(ℂ)`; HQIV still uses **finite patches** + **limits**, not global `L²` as a formal requirement (`CCRFiniteDimObstruction`). |
| `Hqiv.QM.diagonalSmearedNet` / `Hqiv.QM.diagonalSmearedNet_isotony` / `Hqiv.QM.diagonalSmearedNet_commute_all_regions` | Constant diagonal local net; commuting observables across regions (`LocalAlgebraNetScaffold`). |
| `Hqiv.QM.WeightSupportInRegion` / `Hqiv.QM.patchAlgebraAt` / `Hqiv.QM.patchAlgebraAt_isotony` | Smeared weights supported in `R : Finset (Fin 4)`; genuine isotony (`PatchQFTBridge`). |
| `Hqiv.QM.patchChartPoint` / `Hqiv.QM.minkowski_spacelike_patchChartPoint_spatial` / `Hqiv.QM.regions_disjoint_spatial_spacelike` | Minkowski corner embedding; spatial pairs spacelike; disjoint spatial regions ⇒ spacelike pairs (`PatchQFTBridge`). |
| `Hqiv.QM.patchEventChartFour` / `Hqiv.QM.spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions` | `EventChart` on ℕ (`n<4` ↔ corners); disjoint spatial regions ⇒ `spacelikeRelationMinkowski` on labels (`PatchQFTBridge`). |
| `Hqiv.QM.microcausality_zero_comm_patchEventChartFour` | `MicrocausalityStatement commutatorKernelZero (spacelikeRelationMinkowski patchEventChartFour)`. |
| `Hqiv.QM.patchAlgebra_opComm_zero_and_events_spacelike_in_patchChart` | `patchAlgebraAt` commutator `0` ∧ labels spacelike in `patchEventChartFour` when regions satisfy the spatial disjoint hypotheses. |
| `Hqiv.QM.HorizonContinuumAxioms` (in `HorizonLimitedRenormLocality.lean`) | **Record of Props** — explicit slots for continuum closure (not a single Lean `axiom`). Concrete operator content feeding the narrative: `PatchIntervalMaxSmeared` (smeared interval–max Pauli) + `IntervalMaxOperatorCommutator`. |
| `Hqiv.QM.horizon_continuum_closure_core_HQIV` | Closure theorem when core axioms + proved spin-stat + finite CPTP slot align (see file). Related: `Hqiv.QM.horizon_qm_qft_full_package_core_HQIV`, `Hqiv.QM.horizon_continuum_closure_of_axioms`. |
| `Hqiv.QM.horizonContinuumAxiomsMinimal_ratioWitness_all_slots` | Conjunction of the five proved fields for `horizonContinuumAxiomsMinimal_ratioWitness`. |
| `Hqiv.QM.minkowskiIntervalSq` / `Hqiv.QM.spacelikeRelationMinkowski` / `Hqiv.QM.minkowski_spacelike_of_same_time` | Flat $(+,{-},{-},{-})$ interval and chart-pulled-back spacelike relation; same-time spatial separation ⇒ spacelike. |
| `Hqiv.QM.microcausality_in_domain_minkowski_scaffold_holds` | ∀ charts, `MicrocausalityStatement commutatorKernelZero (spacelikeRelationMinkowski chart)` (zero kernel; Minkowski predicate). |
| `Hqiv.QM.commutatorKernelIntervalMax_exists_ne_zero` / `Hqiv.QM.microcausality_intervalMax_scaffold_and_surrogate_nonzero` | Some chart has **nonzero** interval-max surrogate; combined with interval-max microcausality on all charts (`ContinuumManyBodyQFTScaffold`). |
| `Hqiv.QM.commutatorKernelIntervalMax` / `Hqiv.QM.microcausality_in_domain_minkowski_interval_scaffold_holds` | `max 0 η` commutator surrogate; microcausal w.r.t. η-spacelike; see `commutatorKernelIntervalMax_nontrivial`. |
| `Hqiv.QM.commutatorKernelIntervalMax_patchEventChartFour_0_4_eq_one` / `…_ne_zero` | On `patchEventChartFour`, labels `0` and `4` give **η = 1** ⇒ surrogate **nonzero** (timelike domain); `microcausality_patchEventChartFour_intervalMax_and_nonzero` (`PatchQFTBridge`). |
| `Hqiv.QM.continuum_many_body_closure_minkowskiMicroWitness` | Same closure as `continuum_many_body_closure_ratioWitness_trivialRest` but microcausality slot uses the Minkowski scaffold. |
| `Hqiv.QM.continuum_many_body_closure_minkowskiIntervalWitness` | Same closure with interval-max surrogate (nonzero on some timelike pairs). |
| `Hqiv.QM.microcausality_zero_comm_allSpacelike_holds` / `Hqiv.QM.scattering_consistency_unit_channel_holds` | Degenerate “all spacelike” schema + unit scattering channel in `[0,1]` (`ContinuumManyBodyQFTScaffold`). |

## Light cone ↔ Maxwell ↔ QM bridge (`Hqiv.Physics.LightConeMaxwellQFTBridge`)

| Name | Output / meaning |
|------|------------------|
| `Hqiv.Physics.accessibleModeBudgetUpToShell` | ℝ mode budget on shells `0…M` (= `Hqiv.available_modes M`); finite-patch alias for grepability. |
| `Hqiv.Physics.accessibleModeBudgetUpToShell_eq_sum_new_modes` | Patch budget = cumulative `∑_{i≤M} new_modes i` (`SphericalHarmonicsBridge.sum_new_modes_eq_available_modes`). |
| `Hqiv.Physics.accessiblePatch_modeBudget_div_harmonic_tends_four` | `accessibleModeBudgetUpToShell M / sphericalHarmonicCumulativeCount M → 4` as `M → ∞`. |
| `Hqiv.Physics.PhotonHorizonModeLimitValue` / `Hqiv.Physics.PhotonHorizonModeLimit` | **Definite** asymptotic value `4` (= octonion factor); alias for `ShellToHarmonicLimit` (`photonHorizonModeLimit_holds`). |
| `Hqiv.Physics.photonHorizonModeLimit_tendsto` | `Tendsto` of the mode ratio to `𝓝 PhotonHorizonModeLimitValue` (same as harmonic bridge). |
| `Hqiv.Physics.accessiblePatch_shellToHarmonicLimit` | Same `Prop` as `shell_to_harmonic_limit_holds` — named for finite-patch narrative. |
| `Hqiv.Physics.realShellPlusOneFromTimeAngle` / `realShellPlusOneFromTimeAngle_timeAngle_phi_shell_unit` | Continuous coordinate `θ/2`; at `θ = timeAngle (phi_of_shell m) 1` equals `m+1` (`AuxiliaryField`, `HQVMetric`). |
| `Hqiv.Physics.shellIndexFromTimeAngle` / `shellIndexFromTimeAngle_timeAngle_phi_shell` | `⌊max(0,(m+1)t-1)⌋₊` from `θ = timeAngle (phi_of_shell m) t`. |
| `Hqiv.Physics.accessibleModeBudgetUpToTimeAngle` / `accessibleModeBudgetUpToPhiTime` | Mode budget from time-angle–derived shell index; `accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit` at `t=1`. |
| `Hqiv.Physics.lightCone_discreteModes_shellToHarmonicLimit` | Same as `shell_to_harmonic_limit_holds` — discrete `available_modes` ladder vs harmonic count. |
| `Hqiv.Physics.lightCone_emergent_coordsField_constPhi_eq_general` | Constant φ on chart ⇒ emergent O–Maxwell coords RHS = `emergentMaxwellInhomogeneous_O_general` (`ContinuumOmaxwellClosure`). |
| `Hqiv.Physics.lightCone_ratioWitnessBridge_shellProof_eq_discreteLimit` | Identifies `ratioWitnessBridge.shellProof` with `lightCone_discreteModes_shellToHarmonicLimit`. |

*For a full list of `theorem`/`lemma` lines, agents can run `rg '^theorem |^lemma ' Hqiv/` — this file is intentionally curated, not exhaustive.*
