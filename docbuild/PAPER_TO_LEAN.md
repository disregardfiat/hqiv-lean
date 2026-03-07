# Paper-to-Lean mapping

The HQIV paper is at **`/home/jr/Repos/HQIV/paper/main.tex`** (sibling repo `HQIV`). This file maps the paper’s machine-verified and first-principles claims to the Lean 4 formalisation in this repo.

---

## What the paper says is Lean-verified

The paper (abstract, Sec. 2.6, Sec. 7, Sec. 9, tables) explicitly cites:

- **α = 3/5** (“Lean-proved lattice ratio”)
- **6⁷√3** as the exact combinatorial invariant (curvature norm)
- **Ω_k^true = omega_k_from_shell_integral** (“machine-verified in Lean 4”)
- **δ_E(m)** first-principles formula (“machine-verified, no free parameters”)
- **HQIV/Physics/SM_GR_Unification.lean** and curvature modules for “true spatial curvature as dynamic output of the shell integral”

---

## Paper claim → Lean location

| Paper | Lean |
|-------|------|
| **Lattice / light cone** | |
| New modes per shell = 8 × stars-and-bars(m) | `OctonionicLightCone`: `new_modes`, `latticeSimplexCount`, `available_modes_octonion` |
| T(m) = T_Pl/(m+1), φ_m = 2/R_h | `shell_shape`, `curvatureDensity`; φ on shells in `AuxiliaryField` (`phi_of_shell`) |
| Hockey-stick identity, factor 1/6 from combinatorics | `cumLatticeSimplexCount_hockey_stick`, `cumLatticeSimplexCount_closed` |
| **α = 3/5** (Lean-proved) | `OctonionicLightCone`: `alpha_eq_3_5`, `latticeAlphaRatio_eq_alpha`, `tendsto_latticeAlphaRatio` |
| **Curvature imprint δ_E(m)** = (1/(m+1))(1 + α ln(T_Pl/T)) × 6⁷√3 | `shell_shape_formula`, `curvatureDensity`, `deltaE_eq`, `deltaE_exact_norm`; `curvature_norm_combinatorial` |
| **6⁷√3** from cube (6 dirs) × octonion dim 7 × √3 | `curvature_norm_combinatorial_eq`, `curvature_norm_from_cube`, `curvature_norm_determined_by_structure`, `curvature_norm_combinatorial_exact` |
| **Ω_k^true** = shell integral (dynamic, no input amplitude) | `curvature_integral`, `omega_k_at_horizon`, `omega_k_partial`; `omega_k_at_horizon_eq`, `omega_k_at_horizon_depends_on_horizon` |
| Curvature integral bounds (harmonic, Θ(log n)) | `curvature_integral_ge_harmonic`, `curvature_integral_le_harmonic_mul_log`, `curvature_integral_asymptotic_upper` |
| **HQVM / action** | |
| Lapse N = 1 + Φ + φ t | `HQVMetric`: `HQVM_lapse`, `ADM_lapse_eq_HQVM_lapse` |
| (3−γ)H² = 8π G_eff(φ)(ρ_m + ρ_r) | `HQVM_Friedmann_eq`, `HQVM_Friedmann_eq_def` |
| Friedmann from action; equations from variation | `Action`: `S_HQVM_grav_zero_iff_Friedmann`, `equations_from_action`, `action_O_Maxwell_EL_eq_emergent` |
| Same φ, α in gauge and gravity | `GRFromMaxwell`: `same_phi_in_O_Maxwell_and_HQVM`, `same_alpha_in_O_Maxwell_and_HQVM`, `O_Maxwell_determines_HQVM_GR_homogeneous` |
| Covariant O-Maxwell; existence of covariant solution | `CovariantSolution`: `covariant_eq_iff_emergent_flat`, `exists_covariant_solution`, `trivial_is_covariant_solution` |
| **SO(8) / Lie closure** | |
| Lie algebra closes to so(8); 28 generators | `GeneratorsFromAxioms`: `lieClosureDim_eq_so8GeneratorCount`; `GeneratorsLieClosure`: `so8_generators_linear_independent`, `generators_from_octonion_closure` |
| **Baryogenesis** | |
| m_QCD, m_lockin, T_QCD, T_lockin from lattice | `Baryogenesis`: `m_lockin_eq_m_QCD_add_steps`, `T_QCD_eq`, `T_lockin_eq`, etc. |
| η = 6.10×10⁻¹⁰ (paper value); same curvature imprint | `eta_paper`, `eta_paper_eq`, `eta_paper_pos`; baryogenesis shells and curvature imprint usage |
| **SM–GR unification** | |
| SM constants at “now”; Yang–Mills problem statement | `SM_GR_Unification`: `sm_constants_now`, `HQIV_satisfies_YangMills_SM_GR_Unification`, `unification_action_yields_O_Maxwell` |
| “Now” (H = H₀, φ = 1) | `Now`: `nowCondition`, `exists_unique_now_phi`, `H0_ref_eq` |

---

## Not in Lean (paper only or external)

- **γ ≈ 0.40**: from entanglement monogamy; taken as input in Lean (`gamma_HQIV` in `HQVMetric`).
- **Numerical pipelines**: `forward_4d_evolution`, beta engine, CLASS, Monte Carlo baryogenesis → Python/repo, not Lean.
- **Phenomenological normalisation A**: paper’s δ_E^phen(m) = A×δ_E(m); Lean has first-principles δ_E only.
- **Specific observational fits**: CMB peak positions, 51.2 Gyr age, σ₈, etc. → CLASS/scripts.
- **Full derivation of inertia f(a,φ)** from overlap integral → paper (Brodie et al.); Lean uses the resulting form.
- **Schüller hyperbolicity → metric**: geometric route stated in paper; not formalised in Lean.
- **Anomaly cancellation, triality, Higgs mass formula**: paper + code (e.g. `matrices.py`); Spin(8) structure and Lie closure are in Lean.

---

## Summary

- **Everything that the paper calls “Lean-proved” or “machine-verified”** (α = 3/5, 6⁷√3, curvature imprint formula, shell integral as source of Ω_k^true, horizon-dependent Ω_k) **is formalised and proved** in this repo (no `sorry`).
- **Action, HQVM, O-Maxwell, covariant solutions, and “equations from action”** are in Lean and built.
- **SO(8) closure, baryogenesis shell/T/η definitions, and SM–GR unification statement** are in Lean.
- **Numerical values, CLASS, and phenomenological normalisation A** remain outside Lean by design; the paper’s first-principles and combinatorial content that it attributes to Lean are covered here.
