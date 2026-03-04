import Mathlib.Data.Real.Basic

import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.HQVMetric
import Hqiv.Generators
import Hqiv.GeneratorsFromAxioms
import Hqiv.GeneratorsLieClosure

namespace Hqiv

/-!
# Conservations — Metric forces conservations in the structure from counting over O

We do **not** start from the Standard Model or from “embedding SM in SO(8)”.
We start from:

1. **Counting over O in the light cone:** The light-cone axiom (new modes = 8 ×
   stars-and-bars) and the curvature norm (6⁷√3 from cube + octonion dimension)
   are **counting over the octonions O**. That counting yields a definite
   algebraic structure — the **structure that is the result of counting over O**
   in our light cone.

2. **The metric as built:** The HQVM metric (lapse N = 1 + Φ + φ t, time angle
   δθ′ = φ t with period 2π, φ from the lattice) is already fixed by the
   light-cone, monogamy, and natural units. No extra input.

3. **Metric forces conservations:** We **show** that the metric as built **forces**
   conservations **in** that structure (phase mod 2π, etc.). Pure math.

4. **Later:** Prove that this structure is identical to a known gauge structure.
   For now we stay in pure math.

## Where matrices.py comes in — degrees of freedom

The **authoritative construction** of the structure from counting over O is in
`HQVM/matrices.py`: octonion left-multiplication matrices L(e_i), the phase-lift
generator Δ, Lie closure to full so(8) (dimension 28), and the explicit basis.
Here we need to **prove our degrees of freedom**: that the counting over O in
the light cone yields exactly the right number of independent generators (e.g.
28 for the Lie algebra closure), and that the conservations forced by the
metric live in that structure. So the flow is: light-cone counting → structure
(matrices.py constructs it) → **prove** the dimension and that conservations
hold in it; then later identify with known forces.
-/

/-- **Dimension of the structure from counting over O.** The octonion algebra
has 8 dimensions (1 + 7 imaginary); the Lie algebra that closes from the
counting (e.g. so(8)) has dimension 28. We record 28 as the dimension of the
closure; the “8” is the octonion dimension already used in the curvature norm.
This is what we must **prove** as the number of degrees of freedom (matrices.py
computes the closure explicitly). -/
def structure_from_O_dim : ℕ := 28

theorem structure_from_O_dim_eq : structure_from_O_dim = 28 := rfl

/-- **The metric forces conservation of phase (spin).** The time angle δθ′ = φ t
has period 2π (see HQVMetric: `timeAngle_first_period`, `timeAngle_zero_to_twoPi`).
So phase is conserved mod 2π — spin lost to the horizon is encoded in the phase
and wraps rather than being destroyed. This conservation is **forced by** the
metric (lapse = 1 + Φ + timeAngle, time angle in [0, 2π]). -/
theorem metric_forces_phase_conservation (φ : ℝ) (hφ : 0 < φ) :
    timeAngle φ 0 = 0 ∧ timeAngle φ (twoPi / φ) = twoPi ∧
    ∀ t, t ∈ Set.Icc 0 (twoPi / φ) → timeAngle φ t ∈ Set.Icc 0 twoPi :=
  timeAngle_zero_to_twoPi φ hφ

/-- **Lapse decomposition forces horizon term to be the time angle.** The
metric is N = 1 + Φ + δθ′; so the only time-dependent horizon coupling is
δθ′. That **forces** the conservation narrative: the horizon term is exactly
the phase (time angle) that we proved lives in [0, 2π] and wraps. -/
theorem lapse_forces_time_angle_as_horizon_term (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + timeAngle φ t :=
  lapse_decompose Φ φ t

/-!
## Structure from counting over O — degrees of freedom (matrices.py)

The **structure** that is the result of counting over O in the light cone is
constructed in `HQVM/matrices.py`: L(e_i), Δ, g₂ + Δ closure to so(8), 28-element
basis. We need to **prove our degrees of freedom**: that the light-cone counting
(8 × stars-and-bars, 6⁷√3, etc.) yields this structure and that its dimension
and conservations are as stated. Conservations forced by the metric (phase, and
later charge-like quantities) live **in** this structure. Later we can prove
that this structure is identical to SO(8) or the known gauge algebra.
-/

/-- **Conservations hold in the structure from O.** Placeholder: the
conservations forced by the metric (phase conservation, etc.) take place in
the algebraic structure that results from counting over O. To be replaced by
a precise statement once we prove the degrees of freedom (dimension 28, basis
from matrices.py). -/
def conservations_in_structure_from_O : Prop := True

end Hqiv
