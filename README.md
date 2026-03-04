# HQIV_LEAN

Formalisation of the HQIV (Horizon-Quantized Informational Vacuum) framework in Lean 4.  
Modules: `Hqiv.Geometry.OctonionicLightCone`, `AuxiliaryField`, `HQVMetric`, `Hqiv.Generators` (28 so(8) generators; **antisymmetry proved**), `Hqiv.OctonionLeftMultiplication` (L(e_1)..L(e_7)), `Hqiv.GeneratorsFromAxioms` (L, Δ, g₂; target statements), `Hqiv.GeneratorsLieClosureData` (Lie bracket coefficients), `Hqiv.GeneratorsLieClosure` (**Lie bracket closure proved**: all [g_i,g_j] in span; `generators_from_octonion_closure`; linear independence stated, proof depends on `so8CoordMatrix_det_ne_zero`), `Hqiv.So8CoordMatrix` (28×28 coord matrix for linear independence), `Hqiv.Conservations`. Scripts: `scripts/print_lie_bracket_closure.py --write`, `scripts/print_linear_independence.py [--write]`.

**What traces to the light cone (single axiom, no arbitrary defs)**  
- **Single axiom:** New modes at shell m = 8 × stars-and-bars(m) = 4·(m+2)(m+1).  
- From that: `latticeSimplexCount`, `cumLatticeSimplexCount` (and closed form), `available_modes`, `new_modes`.  
- Temperature ladder T(m) = T_Pl/(m+1) (with T_Pl = 1 in natural units) and φ(m) = 2/T(m) are the lattice division rule and the paper’s φ = 2/Θ.  
- `shell_shape` is **proved** equal to (1/(m+1))(1 + α log(T_Pl/T(m))) so the curvature shape is derived from the temperature ladder, not an independent def.  
- Curvature integral, its divergence, divisibility (3∣…, 2∣…), α = 3/5 as lattice ratio and limit, and Ω_k at chosen horizon are proved from the lattice.

**External or conventional defs (not derived from the light cone in Lean)**  
- **α** = 0.60: we prove α = 3/5 and that the lattice ratio (n+1)(n+2)(n+3)/(5·cum n) = 3/5 for all n and tends to 3/5 as n → ∞.  
- **γ** = 2/5: from entanglement monogamy (metric sector), not from the lattice.  
- **curvature_norm_combinatorial** = 6⁷√3: **not chosen by convenience.** It is uniquely determined by three structural inputs: (1) 3D cube → 6 directions (3 axes × 2 signs); (2) octonion algebra → 7 imaginary units; (3) unit-cube half-diagonal → √3. No free parameter; change any input and the number changes. Matter fraction and η require the full SM embedding to SO(8).  
- **omega_k_true** = 0.0098: calibration constant (paper value).  
- **referenceM** = 500: for numerics only; theory uses ∃ transition shell.  
- **Natural units:** T_Pl = 1, G₀ = H₀ = 1.  
- **Metric / lapse:** N = 1 + Φ + φ t and the HQVM line element come from the informational-energy axiom (paper), not from the light cone; φ can be the lattice-derived field.

So: the **combinatorics, T-ladder, φ on shells, curvature shape, α from the lattice, and Ω_k equation** come from the light-cone axiom; **γ**, the curvature norm (6⁷√3, determined by cube + octonion + unit cube, not tuned), **omega_k_true**, **referenceM**, and the metric form are inputs or conventions. Matter fraction and η are downstream of the SM embedding to SO(8).

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

