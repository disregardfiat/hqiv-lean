# Assumptions, defs, and hidden handwaving

This is an **honest inventory** of what the formal development rests on besides “proofs in Lean.” It is aimed at agents who must not confuse marketing language in comments with Mathlib’s logical foundations.

## 1. Conceptual “axioms” of HQIV (paper-level)

These are **not** necessarily `axiom` declarations in Lean. They are the **narrative foundations** repeated in module docs:

- **Discrete null lattice / counting:** New modes per shell follow stars-and-bars combinatorics on the 3D null lattice, multiplied by the octonion factor (encoded as defs and theorems in `OctonionicLightCone`).
- **Informational-energy / monogamy (metric sector):** ADM lapse `N = 1 + Φ + φ t` and the HQVM line element story (`HQVMetric` and related files). `φ` is tied to the auxiliary-field ladder (`AuxiliaryField`), not introduced as a free continuous parameter in the comments’ intent.

Agents should treat **Mathlib** as the substrate for analysis, linear algebra, and `ℝ`.

## 1b. Canonical `α` and `γ` (sole HQIV identifiers; companion + Brodie provenance)

In this repository, **there is only one** curvature-imprint exponent and **only one** monogamy / horizon-overlap coefficient in the HQIV sense:

| Lean name | Role | Proved value |
|-----------|------|----------------|
| `Hqiv.alpha` (`OctonionicLightCone`) | Curvature imprint / $G_{\mathrm{eff}}$ ladder exponent | `3/5` (`alpha_eq_3_5`) |
| `Hqiv.gamma_HQIV` (`HQVMetric`) | Monogamy split; **defined** as `1 - alpha` | `2/5` (`gamma_eq_2_5`) |

No alternate “HQIV α” or “HQIV γ” definitions appear elsewhere: downstream physics (`SM_GR_Unification`, `AuxiliaryField`, CMB hooks, **etc.**) refers to these symbols only.

**Uniqueness is forced in Lean:** `latticeAlphaRatio_eq_alpha` identifies the shell-wise imprint ratio with `alpha` for every `n`; `alpha_eq_3_5` evaluates `alpha = 3/5`; `gamma_HQIV := 1 - alpha` and `gamma_eq_2_5` give `2/5` with `alpha_add_gamma = 1`. These are bundled as `alpha_gamma_forced_pair` in `Hqiv/Geometry/AlphaGammaForcedByLattice.lean`. The **thermodynamic / geometric narrative** explaining why this discrete structure is the HQIV vacuum lives in the **companion HQIV manuscript** and **Brodie (2026)** (`ettinger2026hqiv`, `brodie2026`); Lean **discharges** the rational identities and the complement split, not a menu of tunable parameters.

## 2. Lean `axiom` keyword

A search for user-declared `axiom` statements in `Hqiv/` shows **no free-standing HQIV physics axioms** of the kind “we assume this unprovable proposition.” Discussion of “axiom” in the codebase is overwhelmingly **documentation** (e.g. “single axiom”, “informational-energy axiom”) attached to **definitions** or **named Prop bundles**.

**Explicit `Prop` bundles** (e.g. `HorizonContinuumAxioms`, `HorizonContinuumAxiomsCore` in `HorizonLimitedRenormLocality.lean`) are **assumption records**: they make the continuum-QFT bridge requirements **visible**. Some slots are discharged by other modules (e.g. spin–statistics via `SpinStatistics`). **Scattering-consistency** is not only schematic: `ContinuumManyBodyQFTScaffold` gives proved `[0,1]` channels (including zero / unit channels and an **associator–vorticity** channel from `OctonionBasics`), and `Hqiv.QM.continuum_scattering_associatorVorticity_holds` packages one of these in `HorizonLimitedRenormLocality`. **Microcausality** has **Minkowski** upgrades: `spacelikeRelationMinkowski` with either the zero kernel (`microcausality_in_domain_minkowski_scaffold`) or the **interval-max** surrogate `commutatorKernelIntervalMax` = `max 0 η` (`microcausality_in_domain_minkowski_interval_scaffold` — vanishes on spacelike pairs, positive on some timelike pairs; `commutatorKernelIntervalMax_nontrivial`). Operator-level **scaffolds** exist (`opCommutator`, `fieldOpFromChart`, Pauli **toy**); **exact CCR `[A,B]=I` as literal fixed-size matrices** is impossible (`not_exists_matrix_CCR_one`—trace obstruction); a **minimal local net** (`diagonalSmearedNet`) is formalized with trivial isotony.  HQIV does **not** aim to import full textbook infinite-dimensional QFT as a prerequisite: physics is phrased in **finite** accessible regions inside the light cone, with **limits** as cutoff / horizon resources grow (e.g. shell→harmonic).  Stronger patchwise nets, effective brackets, and continuum limits remain to be formalized; global `L²` representations are optional background, not a stated goal of this repo.  A named **finite-patch** hook is `Hqiv.Physics.accessibleModeBudgetUpToShell` (= cumulative mode budget on shells `0…M`, tied to `sum_new_modes`) and the limit lemmas `accessiblePatch_shellToHarmonicLimit` / `accessiblePatch_modeBudget_div_harmonic_tends_four` in `LightConeMaxwellQFTBridge`.  **Time ↔ shell** on the same ladder uses `timeAngle` with `phi_of_shell` (`shellIndexFromTimeAngle`, `accessibleModeBudgetUpToPhiTime`, unit-time match `accessibleModeBudgetUpToPhiTime_eq_accessibleModeBudgetUpToShell_unit`).  **Event chart:** `Hqiv.QM.patchEventChartFour` ties `EventLabel = ℕ` to the same corners as `patchChartPoint` for `n < 4`; `spacelikeRelationMinkowski_patchEventChartFour_of_disjoint_regions` links disjoint spatial **Fin 4** regions to η-spacelike **ℕ** pairs (with `microcausality_zero_comm_patchEventChartFour` for the zero commutator surrogate).  **Definite horizon / photon refinement limit:** `Hqiv.Physics.PhotonHorizonModeLimit` / `PhotonHorizonModeLimitValue` (`4`) and `photonHorizonModeLimit_tendsto` — EM null-ladder vs cumulative `S²` harmonics; curvature–horizon growth is separate (`omega_k_partial_tends_to_atTop` in `OctonionicLightCone`).  **Interval-max commutator surrogate** `max 0 η` is **not** globally zero: `commutatorKernelIntervalMax_exists_ne_zero`, `microcausality_intervalMax_scaffold_and_surrogate_nonzero`; on the patch chart, `commutatorKernelIntervalMax_patchEventChartFour_0_4_ne_zero` (labels `0` vs parked `4`).

## 3. Mathlib (and dependencies)

- **Every proof** ultimately rests on **Mathlib’s** axioms for classical mathematics (reals, sets, linear algebra, etc.). This is standard; no attempt is made here to re-derive foundations.
- **Trust boundary:** If Mathlib is trusted, the HQIV proofs are “relative to Mathlib + the items below.”

## 4. Script-generated and numeric data in Lean

- **`GeneratorsLieClosureData0` … `GeneratorsLieClosureData27` and related files:** Large **precomputed** coefficient data (from Python scripts in `scripts/`, per `README.md`) to keep the SO(8) Lie closure proof tractable in Lean. This is **not** magic: it is **imported data** baked into lemmas. Agents should treat it as “verified external input” unless they re-run the scripts and regenerate.
- **`so8Generator` matrices:** Originate from the same pipeline as `matrices.py` / project scripts (see repo docs).

## 5. `sorry` (known gaps)

| Location | What is left |
|----------|----------------|
| `Hqiv/Algebra/SO8ClosureAbstract.lean` | **Corrected (2026-03):** linear `Submodule.span ℝ (G₂ ∪ {Δ})` has `finrank ≤ 15` (`finrank_span_G2_union_Delta_le_15`), so it **cannot** equal the 28-dim `span(so8Generator)` — see `exists_so8Generator_not_mem_span_G2_union_Delta`.  **`span_G2_union_Delta_le_span_so8Generator`** (containment in `span(so8)`) is proved.  Lie-subalgebra **generation** by brackets is the right notion for closure; use `GeneratorsLieClosure` / `lieBracket_in_span`, not bare linear span of 15 matrices. |
| Root `tmp_*.lean` (if present) | Scratch files — **gitignored** (`.gitignore`); local only, not part of the library story. |

**Do not** claim “zero sorry in the entire repo” without running `rg 'sorry' --glob '*.lean'` — the README’s “100% proved” claim targets the **intended release stack**; verify against the actual `lake` target you build.

## 6. Numeric literals and `rfl` proofs

Many “physical outputs” (e.g. `1/α_EM(M_Z) = 127.9`, Higgs mass ratio) are **fixed by definition** in Lean and then proved by `rfl` or `norm_num`. That means:

- They are **exactly as trustworthy as the numeric encoding** and the **paper alignment** they are meant to match.
- They are **not** independent predictions produced by a separate numeric solver inside Lean unless a separate proof says so.

## 7. Conventions (not secret, but easy to misread)

- **`referenceM`, `qcdShell`, `latticeStepCount`:** Discrete **anchor indices** for the shell story; documented in `OctonionicLightCone` and the main README. Changing them changes **which shell** is “reference,” not Mathlib.
- **Natural units:** `T_Pl`, `G₀`, `H₀` set to 1 in many places — a **modeling convention**, stated in module docs.

## 7b. Lepton shells (canonical: lock-in + `ChargedLeptonResonance`)

- **`LeptonGenerationLockin`**: **structural** alignment with quarks — **τ at `referenceM`**
  (lock-in), **μ and e on strictly larger ℕ shells**, so **the electron sits on the highest shell
  index** among charged leptons in that module.
- **`ChargedLeptonResonance`**: geometric `resonance_k_*`, `m_tau_Pl`, `resonanceProduct`, etc., on
  those same three shells (imported by `SM_GR_Unification`).
- **Archived only:** the old **τ = highest ℕ shell** Planck-volume book-keeping (`m_e < m_mu < m_tau`
  with τ at `274211`) is kept as `archive/abandoned/GenerationResonanceTauHighestShell.lean` and is
  **not** in the default lake targets.
- **Continuous shells:** nothing in the formalism *requires* shell labels to be integers; the
  repo’s **proved** surfaces use **ℕ** for `shellSurface` and detuning. A future layer could use
  `ℝ` labels with the same `(m+1)(m+2)` pattern evaluated on non-integer points — not done here.
- **Cumulative rapidity (dynamic Rindler δ):** `Hqiv.Physics.delta_auxiliary_phi_per_shell` and
  `rindlerDenWithDeltaRapidity` in `GlobalDetuning` add `β_cum * (φ·t)` on the same lattice time
  track as `timeAngle` — in-repo defs/theorems, not a `sorry`.

## 8. Imports = logical dependency (not “handwaving,” but easy to miss)

If module A imports module B, **all** definitions and axioms of B (and Mathlib transitive closure) are in force. The root `HQIVLEAN.lean` lists the **intended** high-level import graph; individual features may compile under smaller `lake` targets — see `lakefile.toml`.

## 9. When to update this file

Update **ASSUMPTIONS.md** when you:

- Add or remove a `sorry`
- Add new script-generated data files
- Introduce new explicit `Prop` assumption bundles for bridges
- Change numeric reference literals that are proved by `rfl`

## 10. What can be improved (vs what stays)

Rough priority for **actually reducing** handwaving or confusion:

| Item | Can we “take care of it”? | Notes |
|------|---------------------------|--------|
| **§5 — `SO8ClosureAbstract` linear span** | **Resolved (dimension obstruction).** | The old target `so8Generator_mem_span_G2_Delta` / `G2_plus_Delta_closes_to_so8_full` was **not mathematically valid** for linear span (15 generators vs 28 dimensions). Replaced by `span_G2_union_Delta_le_span_so8Generator`, `finrank_span_G2_union_Delta_le_15`, `exists_so8Generator_not_mem_span_G2_union_Delta`. Lie-generated closure remains future formalization. |
| **§5 — `tmp_*.lean` scratch files** | **Mostly done.** | Root `tmp_*.lean` is **gitignored**; delete local copies if you want `rg sorry` to skip them entirely. |
| **§4 — Lie-closure data files** | **Partially.** | Keep as data; add optional CI: re-run `scripts/print_*.py --write` and fail on `git diff`, or record a checksum in this doc. Reduces “silent drift,” not the need for precomputed coefficients. |
| **§2 — `HorizonContinuumAxioms*` records** | **Clarity + partial discharge.** | Shell→harmonic and several **finite-layer** witnesses (microcausality kernel, cluster triviality, **scattering channels** including associator/vorticity) are **proved** under the minimal ratio witness (`horizonContinuumAxiomsMinimal_ratioWitness_all_slots`, `continuum_scattering_associatorVorticity_holds`). Microcausality also has **Minkowski** variants (`continuum_many_body_closure_minkowskiMicroWitness`, `continuum_many_body_closure_minkowskiIntervalWitness`, `spacelikeRelationMinkowski`) — η-spacelike pairs; either a zero commutator surrogate or `max 0 η` (nontrivial on timelike pairs). Operator fields / patchwise nets beyond the diagonal scaffold remain future work.  The intended physics stays **inside** finite accessible light-cone regions with **asymptotic limits** (shell ladder, mode budgets), not a mandatory global infinite-dimensional carrier. What remains “schematic” is mainly **full** textbook continuum renormalisation / arbitrary external QFT input — not something this repo targets as one closed theorem. Rename (`Hypothesis` vs `Axiom`) or split docs if agents still conflate “bridge record” with “unproved physics.” |
| **§6 — numeric `rfl` witnesses** | **Partially.** | Refactor into named `def`s (e.g. `paperWitness_one_over_alpha_EM`) with one docstring, or derive from a smaller set of definitions — improves auditability; does not turn witnesses into independent Lean computations unless you build that derivation. |
| **§1 — paper-level “two axioms”** | **No (in-repo).** | Physics design; formalised as definitions + theorems. |
| **§3 — Mathlib** | **No.** | Standard trust unless you port to a smaller foundation (out of scope). |
| **§7–8 — conventions / imports** | **Documentation only.** | Already honest; expand module docs if something is still ambiguous. |

**Highest ROI:** (1) formalize **Lie-subalgebra** closure (iterated brackets from `G₂ ∪ {Δ}`), not linear span — see §5; (2) optional: delete local root `tmp_*.lean` if you want cleaner `rg` sweeps (they are gitignored); (3) optional CI on regeneration of `GeneratorsLieClosureData*`.
