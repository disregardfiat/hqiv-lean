# HQIV_LEAN

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.18899939.svg)](https://doi.org/10.5281/zenodo.18899939)

Formalisation of the HQIV (Horizon-Quantized Informational Vacuum) framework in Lean 4. The accompanying preprint is archived on Zenodo:

- **Preprint (Zenodo):** [zenodo.org/records/18899939](https://zenodo.org/records/18899939)
- **DOI:** [10.5281/zenodo.18899939](https://doi.org/10.5281/zenodo.18899939)
- **API documentation (GitHub Pages):** The [Lean docgen workflow](.github/workflows/lean_action_ci.yml) builds and deploys the API docs on each push to the default branch. Once enabled, they are published at [**disregardfiat.github.io/HQIV_LEAN/docs**](https://disregardfiat.github.io/HQIV_LEAN/docs).

## Building

```bash
lake build
```

If the build exits with **code 134** (stack overflow in `GeneratorsLieClosureData`):

- **Daily work (no SO(8) generator stack):** `lake build HQIVPhysics` or `./scripts/build.sh`
- **Full build (with SO(8) closure):** you must raise the stack limit **in the same shell** before any `lake` command, then build:
  ```bash
  ulimit -s 65536
  lake build HQIVLEAN
  ```
  Or run `./scripts/build.sh HQIVLEAN` (the script sets ulimit before building).

**Default build** is the root plus the current formal core: `OctonionicLightCone`, `AuxiliaryField`, `HQVMetric`, and the generator stack (`Generators`, `OctonionLeftMultiplication`, `GeneratorsFromAxioms`, `GeneratorsLieClosureData`, `So8CoordMatrix`, `GeneratorsLieClosure`). Downstream (`Now`, `Conservations`, `Forces`, `SM_GR_Unification`, `Baryogenesis`) remains unlinked; set `globs = ["HQIVLEAN", "Hqiv.+"]` in `lakefile.toml` to build all. The first run will build mathlib and can take 30–60+ minutes.

**ProofWidgets:** If the build fails with `ProofWidgets not up-to-date. Please run lake exe cache get`, the widget cache may be unavailable. A workaround is to comment out the `errorOnBuild` check in `.lake/packages/proofwidgets/lakefile.lean` (the block `if let some msg := get_config? errorOnBuild then error msg`) so the widget is built from source. Re-apply this change after `lake update` if the package is reset.
If you see errors like `failed to load header from ... setup.json: unexpected end of input`, the mathlib build cache may be corrupted; then run:

```bash
cd .lake/packages/mathlib && lake clean && cd ../../..
lake build
```  
Current build: `Hqiv.Geometry.OctonionicLightCone`, `AuxiliaryField`, `HQVMetric`, `Hqiv.Generators`, `Hqiv.OctonionLeftMultiplication`, `Hqiv.GeneratorsFromAxioms`, `Hqiv.GeneratorsLieClosureData`, `Hqiv.So8CoordMatrix`, `Hqiv.GeneratorsLieClosure`. Full tree (when re-enabled): `Now`, `Conservations`, `Forces`, `SM_GR_Unification`, `Baryogenesis`, etc. Scripts: `scripts/print_lie_bracket_closure.py --write`, `scripts/print_linear_independence.py [--write]`.

**What traces to the light cone (single axiom, no arbitrary defs)**  
- **Single axiom:** New modes at shell m = 8 × stars-and-bars(m) = 4·(m+2)(m+1).  
- From that: `latticeSimplexCount`, `cumLatticeSimplexCount` (and closed form), `available_modes`, `new_modes`.  
- Temperature ladder T(m) = T_Pl/(m+1) (with T_Pl = 1 in natural units) and φ(m) = 2/T(m) are the lattice division rule and the paper’s φ = 2/Θ.  
- `shell_shape` is **proved** equal to (1/(m+1))(1 + α log(T_Pl/T(m))) so the curvature shape is derived from the temperature ladder, not an independent def.  
- Curvature integral, its divergence, divisibility (3∣…, 2∣…), α = 3/5 as lattice ratio and limit. **Ω_k is dynamic and horizon-dependent:** `omega_k_at_horizon n N` is the curvature ratio at horizon N; spatial curvature between different horizons (e.g. quarks vs CMB LSS) is different even at time "now" — no single Ω_k without specifying the horizon.
- **Analytic curvature:** The discrete curvature integral is proved to be sandwiched between the harmonic sum and (1+α log(n+1)) times the harmonic sum (`curvature_integral_ge_harmonic`, `curvature_integral_le_harmonic_mul_log`), so it grows like Θ(log n); no continuous integral axiom.

**External or conventional defs (not derived from the light cone in Lean)**  
- **α** = 0.60: we prove α = 3/5 and that the lattice ratio (n+1)(n+2)(n+3)/(5·cum n) = 3/5 for all n and tends to 3/5 as n → ∞.  
- **γ** = 2/5: from entanglement monogamy (metric sector), not from the lattice.  
- **curvature_norm_combinatorial** = 6⁷√3: **not chosen by convenience.** It is uniquely determined by three structural inputs: (1) 3D cube → 6 directions (3 axes × 2 signs); (2) octonion algebra → 7 imaginary units; (3) unit-cube half-diagonal → √3. No free parameter; change any input and the number changes. Matter fraction and η require the full SM embedding to SO(8).  
- **referenceM** = lockin = qcdShell + stepsFromQCDToLockin; discrete steps through baryogenesis (a few steps after T_lockin).  
- **Natural units:** T_Pl = 1, G₀ = H₀ = 1.  
- **Metric / lapse:** N = 1 + Φ + φ t and the HQVM line element come from the informational-energy axiom (paper), not from the light cone; φ can be the lattice-derived field.

So: the **combinatorics, T-ladder, φ on shells, curvature shape, α from the lattice, and horizon-dependent Ω_k (curvature ratio from shell integral)** come from the light-cone axiom; **γ**, the curvature norm (6⁷√3), **referenceM**, and the metric form are inputs or conventions. Spatial curvature is different between any two horizons (e.g. QCD vs CMB LSS) even at "now". Matter fraction and η are downstream of the SM embedding to SO(8).

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

