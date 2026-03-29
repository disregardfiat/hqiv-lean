# Agent-friendly map (HQIV_LEAN)

This folder is for **AI agents and new contributors** who need orientation without reading the whole Mathlib-sized dependency graph. It stays next to the project `README.md` and is updated when the formal story changes in a material way.

**Canonical HQIV constants:** $\alpha=3/5$ (`Hqiv.alpha`) and $\gamma=2/5$ (`Hqiv.gamma_HQIV`) are the **only** curvature-imprint and monogamy parameters in this formalism; physical derivation is in the companion HQIV manuscript and Brodie (2026). See [ASSUMPTIONS.md](./ASSUMPTIONS.md) §1b.

| Doc | Contents |
|-----|----------|
| [THEOREMS.md](./THEOREMS.md) | Curated **theorems and defs with usable outputs** (Lean names, modules, what you get) |
| [ASSUMPTIONS.md](./ASSUMPTIONS.md) | **Honest accounting**: conceptual axioms, Mathlib trust, script data, `sorry`s, bridge assumptions |

## Quick table of contents (code areas)

- **Root imports:** `HQIVLEAN.lean` — single entry listing the modules pulled into the full library build.
- **Light cone & combinatorics:** `Hqiv/Geometry/OctonionicLightCone.lean`, `SphericalHarmonicsBridge.lean`
- **Metric / lapse / cosmology bridge:** `Hqiv/Geometry/HQVMetric.lean`, `HQVMPerturbations.lean`, `HQVMCLASSBridge.lean`, `UniverseAge.lean`, `Now.lean`
- **Auxiliary field / φ ladder:** `Hqiv/Geometry/AuxiliaryField.lean` (+ smeared/rapidity bridge modules as needed)
- **SO(8) / octonions:** `Hqiv/Generators*.lean`, `OctonionLeftMultiplication.lean`, `SO8Closure.lean`, `Hqiv/Algebra/*`
- **Physics unification & forces:** `Hqiv/Physics/SM_GR_Unification.lean`, `GRFromMaxwell.lean`, `Forces.lean`, `Action.lean`, `ModifiedMaxwell.lean`, `Baryogenesis.lean`
- **QM / QFT bridges:** `Hqiv/QuantumMechanics/*` (e.g. `HorizonLimitedQM_QFT_Closure.lean`, `HorizonLimitedRenormLocality.lean`); finite **accessible** light-cone patches and **limits** as cutoff grows (not global infinite-dimensional QFT as a prerequisite) — see `Hqiv/Physics/LightConeMaxwellQFTBridge.lean` (`accessibleModeBudgetUpToShell`, `shellIndexFromTimeAngle` / `accessibleModeBudgetUpToPhiTime`, …).
- **Quantum computing / protein hooks:** `Hqiv/QuantumComputing/*`, `Hqiv/ProteinResearch/*`

## Build targets (what actually compiles)

See `lakefile.toml`. Roughly:

| Target | Role |
|--------|------|
| `HQIVWitnesses` | Minimal witness stack (fast CI / smoke) |
| `HQIVPhysics` | Geometry + physics + conservations **without** heavy `GeneratorsLieClosureData*` |
| `HQIVLEAN` | Full formal library including SO(8) Lie-closure data files |

Use the smallest target that contains the modules you are editing.

## Maintainer note

When you add a **user-facing** formal claim that agents should rely on, add a one-line entry under the right heading in `THEOREMS.md`. When you add **new trust assumptions** (script data, `sorry`, or explicit `Prop` bundles), document them in `ASSUMPTIONS.md`.

**Interactive:** `sim/patch_qft_bridge.html` — browser UI for mode budget, time-angle shell index, Minkowski `patchChartPoint` intervals, and disjoint spatial regions (aligns with `PatchQFTBridge` / `LightConeMaxwellQFTBridge`).
