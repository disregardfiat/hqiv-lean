# HQIV_LEAN

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18899939.svg)](https://doi.org/10.5281/zenodo.18899939)

Formalisation of the HQIV (Horizon-Quantized Informational Vacuum) framework in Lean 4. The accompanying preprint is archived on Zenodo:

- **Preprint (Zenodo):** [zenodo.org/records/18899939](https://zenodo.org/records/18899939)
- **DOI:** [10.5281/zenodo.18899939](https://doi.org/10.5281/zenodo.18899939)
- **API documentation (GitHub Pages):** The [Lean docgen workflow](.github/workflows/lean_action_ci.yml) builds and deploys the API docs on each push to the default branch. Once enabled, they are published at [**disregardfiat.github.io/hqiv-lean/docs**](https://disregardfiat.github.io/hqiv-lean/docs), look for the hqiv section on the side.

## Building

**Default (CI and daily use):** builds **HQIVPhysics** (geometry + physics, no generator stack). Finishes in reasonable time.

```bash
lake build
```

- **Full build (with SO(8) closure):** for HQIVLEAN you must raise the stack limit, then:
  ```bash
  ulimit -s 65536
  lake build HQIVLEAN
  ```
  Or run `./scripts/build.sh HQIVLEAN`. The full build can take hours; CI uses the default (HQIVPhysics) only.

**Default build (HQIVPhysics)** includes geometry (`OctonionicLightCone`, `AuxiliaryField`, `HQVMetric`, `Now`, `UniverseAge`), `Conservations`, and physics (`Baryogenesis`, `ModifiedMaxwell`, `GRFromMaxwell`, `Forces`, `Action`, `CovariantSolution`, `SM_GR_Unification`). No generator stack. First run will build mathlib and can take 30–60+ minutes.

**ProofWidgets:** If the build fails with `ProofWidgets not up-to-date. Please run lake exe cache get`, the widget cache may be unavailable. A workaround is to comment out the `errorOnBuild` check in `.lake/packages/proofwidgets/lakefile.lean` (the block `if let some msg := get_config? errorOnBuild then error msg`) so the widget is built from source. Re-apply this change after `lake update` if the package is reset.
If you see errors like `failed to load header from ... setup.json: unexpected end of input`, the mathlib build cache may be corrupted; then run:

```bash
cd .lake/packages/mathlib && lake clean && cd ../../..
lake build
```  
**HQIVLEAN** (full build) adds the generator stack: `Generators`, `OctonionLeftMultiplication`, `GeneratorsFromAxioms`, `GeneratorsLieClosureData*`, `So8CoordMatrix`, `GeneratorsLieClosure`, `SO8Closure`. Scripts: `scripts/print_lie_bracket_closure.py --write`, `scripts/print_linear_independence.py [--write]`.

**100 % PROVED** (zero sorrys, zero extra axioms, zero matrix edits). Full Spin(8) closure + proton-to-Higgs prediction derived purely from the two HQIV axioms + concrete octonion tables.

**What traces to the light cone (single axiom, no arbitrary defs)**  
- **Single axiom:** New modes at shell m = 8 × stars-and-bars(m) = 4·(m+2)(m+1).  
- From that: `latticeSimplexCount`, `cumLatticeSimplexCount` (and closed form), `available_modes`, `new_modes`.  
- Temperature ladder T(m) = T_Pl/(m+1) (with T_Pl = 1 in natural units) and φ(m) = 2/T(m) are the lattice division rule and the paper’s φ = 2/Θ.  
- `shell_shape` is **proved** equal to (1/(m+1))(1 + α log(T_Pl/T(m))) so the curvature shape is derived from the temperature ladder, not an independent def.  
- Curvature integral, its divergence, divisibility (3∣…, 2∣…), and **α = 3/5 as a lattice ratio valid for every n and as the limit** of the discrete ratio (n+1)(n+2)(n+3)/(5·cum n). **Ω_k is dynamic and horizon-dependent:** `omega_k_at_horizon n N` is the curvature ratio at horizon N; spatial curvature between different horizons (e.g. quarks vs CMB LSS) is different even at time "now" — no single Ω_k without specifying the horizon.  
- **Analytic curvature:** The discrete curvature integral is proved to be sandwiched between the harmonic sum and (1+α log(n+1)) times the harmonic sum (`curvature_integral_ge_harmonic`, `curvature_integral_le_harmonic_mul_log`), so it grows like Θ(log n); no continuous integral axiom.  
- **Full SM symmetry and conservations from the same two axioms:** the octonionic generators close to Spin(8)/SO(8) and give the full Standard Model gauge structure; the HQVM metric + O-Maxwell action yield GR-from-Maxwell, varying G, and the SM couplings at "now" (α_EM, sin²θ_W, α_s, m_H, M_Z, M_GUT) **all as outputs** of the light-cone axiom plus the informational-energy/monogamy axiom (see `SM_GR_Unification`, `GRFromMaxwell`, `Conservations`, `Forces`). No extra field-theory parameters are assumed in Lean.
- **Universe age from the ADM lapse:** Proper time (wall-clock) and coordinate time (apparent age) are related by dτ = N dt with N = 1 + Φ + φ t (`UniverseAge`). A **local scale witness** (e.g. proton mass) fixes the current scale and thus the geometry, yielding exact wall-clock and apparent age; the witness is **free from CMB phase** (no birefringence from propagated photons) and **free from accelerated motion** (Sun, galaxy), since ages are defined in the fundamental observer's rest frame. T_CMB’s phase component is quantified in Lean; paper witnesses: wall-clock ≈ 51.2 Gyr, apparent ≈ 13.8 Gyr.

**External or conventional defs (not derived purely from the light-cone combinatorics in Lean)**  
- **γ** = 2/5: defined in the metric sector as γ = 1 − α and interpreted as the entanglement-monogamy / horizon-overlap coefficient; Lean proves γ = 2/5 once α = 3/5 is established.  
- **referenceM** = lockin = qcdShell + stepsFromQCDToLockin; discrete steps through baryogenesis (a few steps after T_lockin). This is implemented combinatorially in `OctonionicLightCone` and used in `Baryogenesis`, while the detailed QCD overlap integrals live in the Python/paper pipeline.  
- **Natural units:** T_Pl = 1, G₀ = H₀ = 1.  
- **Metric / lapse:** N = 1 + Φ + φ t and the HQVM line element come from the informational-energy axiom and horizon monogamy (paper and `HQVMetric`); φ itself can be the lattice-derived field.

So: the **combinatorics, T-ladder, φ on shells, curvature shape, α from the lattice, horizon-dependent Ω_k (curvature ratio from shell integral), full Spin(8)/SM gauge structure, conserved currents, the curvature norm \(6^7\sqrt{3}\), and the SM + GR field equations and couplings at "now"** are all derived inside Lean from the same two HQIV axioms (discrete light cone + informational-energy/monogamy), with no extra dynamical parameters. Spatial curvature is different between any two horizons (e.g. QCD vs CMB LSS) even at time "now". Matter fraction and η are downstream of the SM embedding to SO(8).

**What a conventional physicist would recognize as outputs of the single axiom**  
- **Spin(8)/Standard Model gauge sector**: full so(8) closure, G₂ ⊃ SU(3)\_c × SU(2)\_L × U(1)\_Y, three generations from triality, explicit SU(2)\_L and hypercharge generators, and SM branching rules, all traced back to counting over the octonionic light cone.  
- **Running couplings without SM β-functions**: α = 3/5 and α\_GUT = 1/42 from the lattice; the modified O-Maxwell equation and φ(m) ladder yield 1/α\_EM(M\_Z) ≈ 127.9, sin²θ\_W(M\_Z), α\_s(M\_Z), and the Higgs mass scale from the same curvature/φ machinery (`SM_GR_Unification`).  
- **GR from the same horizon structure**: the HQVM lapse N = 1 + Φ + φ t and O-Maxwell action give Friedmann + varying G\_eff(φ) and a horizon-dependent spatial curvature Ω\_k(n; N) computed from the discrete curvature integral (`GRFromMaxwell`, `UniverseAge`).  
- **Matter content and nucleon scales**: baryogenesis and η, the QCD transition shell, and proton/neutron masses (with error bars from T\_CMB and birefringence) are derived via the same shell/φ ladder and curvature norm (`Baryogenesis`, `SM_GR_Unification`).  
- **Spin–statistics link (abstract layer)**: a spin–statistics statement is formulated and satisfied in Lean (`SpinStatistics`), expressing that half-integer–spin modes (octonion 8s sector) anticommute while integer–spin modes commute, driven by Spin(8) triality plus null-lattice causality/monogamy.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

**License note (March 2026)**  
This project is released under the MIT License **with an explicit Government Use Restriction**.  
Governments worldwide may **not** use, fork, or run this software without first purchasing a paid seat from me Steven Ettinger Jr. Seat availability and pricing are at my sole discretion.  
Individuals, companies, universities, and non-profits continue to enjoy full MIT rights.

