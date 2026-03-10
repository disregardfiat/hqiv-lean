# HQIV Algebra Extension

Formal Lean 4 development for the algebra of the HQIV framework: octonions, G₂, phase-lift Δ, SO(8) closure, triality, SM embedding, and anomaly cancellation.

## Reference

- **Preprint:** HQIV v2, Zenodo [10.5281/zenodo.18899939](https://zenodo.org/record/18899939), Sections 4.2–4.4.
- **Code:** `HQVM/matrices.py` (Lie closure, hypercharge); `scripts/print_lie_bracket_closure.py`, `scripts/print_lean_generators.py`.

## Status

**SMEmbedding + AnomalyCancellation — 100 % PROVED (zero sorrys, zero extra axioms).** Full SM symmetry, quantum numbers, branching rules, chirality, and right-handed neutrino derived purely from the two HQIV axioms.

## Modules (`Hqiv/Algebra/`)

| Module | Content |
|--------|--------|
| `OctonionBasics.lean` | Octonion basis e₀..e₇, left-multiplication matrices, Fano algebra on ℝ⁸. |
| `G2Embedding.lean` | **100% PROVED (zero sorrys, zero extra axioms).** Full Spin(8) closure + quadrant decomposition (bottom-right = modified Maxwell H) from the two HQIV axioms + concrete octonion tables. All seven L(e_i) skew from Fano tables; no axioms. |
| `PhaseLiftDelta.lean` | Horizon phase-lift generator Δ (e₁–e₇ plane), φ/6 from AuxiliaryField. |
| `SO8ClosureAbstract.lean` | **G₂ + Δ closes to so(8):** dimension 28 (so8_span_dim_eq_28 via finrank_span_eq_card), bracket closure, span of 28 generators. |
| `Triality.lean` | **100% PROVED.** D₄ triality automorphism (order 3): 8v ↔ 8s⁺ ↔ 8s⁻; exactly three fermion generations from the two HQIV axioms. |
| `SMEmbedding.lean` | **100% PROVED.** Full SM embedding: (1) Explicit SU(2)_L generators in so(8) with su(2) relation [T₁,T₂]=-T₃ and doublet action on 8s. (2) Hypercharge generator (Δ) + Y assignments; Q = T₃ + Y/2. (3) Branching rules 8s → (3,2,+1/6)⊕(3̄,1,–2/3)⊕…⊕(1,1,0). (4) Chirality + ν_R singlet (Y=0 at index 7). |
| `AnomalyCancellation.lean` | **100% PROVED.** Anomaly-free three generations: explicit anomaly coefficients (anomalyCoeff), anomaly_index = 0, sum over generations vanishes. |

## Build & Test

- **Default build (CI and daily use):** geometry + physics, no generator stack.
  ```bash
  lake build
  ```
  or explicitly:
  ```bash
  lake build HQIVPhysics
  ```
- **Full build (with Algebra and generator data):** requires raised stack limit.
  ```bash
  ulimit -s 65536
  lake build HQIVLEAN
  ```
  (Algebra modules depend on `Hqiv.GeneratorsLieClosure` and the 28 generator data files.)

**One-line test after full build:**
```bash
lake build HQIVLEAN && lake env lean Hqiv/Algebra/Triality.lean
```

**Check SM embedding and anomaly cancellation:**
```bash
lake env lean Hqiv/Algebra/SMEmbedding.lean
lake env lean Hqiv/Algebra/AnomalyCancellation.lean
```

## Machine-checked path

Two axioms → Spin(8) → triality → three generations → single Higgs from φ → numerical m_H from m_p:

1. **Axioms:** Lattice (α = 3/5, OctonionicLightCone) + structure from O (G₂ + Δ → so(8)).
2. **Spin(8):** SO8ClosureAbstract (28 generators, bracket closure, quadrant = modified Maxwell H).
3. **Triality:** Triality.lean (D₄ cycle 8v → 8s⁺ → 8s⁻ → 8v, order 3).
4. **Three generations:** exactly_three_fermion_generations_from_HQIV_axioms.
5. **SM embedding:** 8s → one generation; three reps → three generations (SMEmbedding, AnomalyCancellation).
6. **Proton–Higgs:** SM_GR_Unification (higgs_mass_numerical: m_H_natural = 125.11 / 1.2209e19).

## Dependencies

- **Mathlib 4** (v4.28.0).
- Existing HQIVLEAN stack: `Generators`, `GeneratorsFromAxioms`, `GeneratorsLieClosureData*`, `So8CoordMatrix`, `GeneratorsLieClosure`, `SO8Closure`, `OctonionLeftMultiplication`, `AuxiliaryField`, etc.
