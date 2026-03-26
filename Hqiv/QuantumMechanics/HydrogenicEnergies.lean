/-
Closed-form hydrogenic energy scales used by `Schrodinger.lean` and `QuantumComputing/DigitalQuantumSimulation`.
Factored out so the digital simulation layer need not import the full continuum Schrödinger development
(operators, wavefunctions, calculus).
-/

import Hqiv.Physics.Forces
import Hqiv.Physics.SM_GR_Unification

namespace Hqiv

/-- Expected ground-state energy for a hydrogenic system in the HQIV effective description
(same formula as the former inline definition in `Schrodinger.lean`). -/
noncomputable def expectedGroundEnergy (Z : ℕ) (μ : ℝ) : ℝ :=
  - μ * (Z : ℝ) ^ 2 * (alpha_EM_at_MZ ^ 2) / 2

/-- Expected energy for principal quantum number `n ≥ 1` (Rydberg-style `∝ 1/n²`). -/
noncomputable def expectedEnergy (n : ℕ) (Z : ℕ) (μ : ℝ) : ℝ :=
  if hn : 0 < n then
    - μ * ((Z : ℝ) ^ 2) * (alpha_EM_at_MZ ^ 2) /
        (2 * (hbar_SI ^ 2) * (n : ℝ) ^ 2)
  else
    0

end Hqiv
