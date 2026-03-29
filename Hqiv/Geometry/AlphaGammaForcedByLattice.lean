import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.HQVMetric

/-!
# α and γ forced by the discrete lattice and unit split

**Uniqueness is not a separate axiom:** once the cumulative simplex count and hockey-stick
identity are in place, the imprint ratio `latticeAlphaRatio n` equals `alpha` for every shell
`n`, and `alpha = 3/5` is a proved rational equality. The monogamy coefficient is **not** a second
free parameter: `gamma_HQIV := 1 - alpha`, hence `gamma_HQIV = 2/5` and `alpha + gamma_HQIV = 1`.

This packages the forcing chain for citation from the paper and from `AGENTS` docs: the companion
HQIV manuscript and Brodie (2026) give the physical narrative; **Lean discharges the discrete
uniqueness** of the rational targets.
-/

namespace Hqiv

open scoped Real

/-- At every shell index `n`, the lattice curvature-imprint ratio equals **3/5** — not one value
among many, but the unique rational forced by `latticeAlphaRatio_eq_alpha` and `alpha_eq_3_5`. -/
theorem lattice_imprint_ratio_forced_three_fifths (n : Nat) :
    latticeAlphaRatio n = (3 / 5 : ℝ) := by
  rw [latticeAlphaRatio_eq_alpha, alpha_eq_3_5]

/-- The curvature imprint exponent is **uniquely** `3/5` in the discrete formalism (`alpha`). -/
theorem alpha_forced_three_fifths : alpha = (3 / 5 : ℝ) :=
  alpha_eq_3_5

/-- γ is **forced** by the unit split `γ = 1 − α` once α is fixed; no independent γ knob. -/
theorem gamma_forced_as_complement : gamma_HQIV = 1 - alpha := by
  unfold gamma_HQIV; rfl

/-- The monogamy coefficient is **uniquely** `2/5` given `alpha = 3/5`. -/
theorem gamma_forced_two_fifths : gamma_HQIV = (2 / 5 : ℝ) :=
  gamma_eq_2_5

/-- **Joint uniqueness:** the canonical `(α, γ)` pair enforced by the lattice + complement split. -/
theorem alpha_gamma_forced_pair :
    alpha = (3 / 5 : ℝ) ∧ gamma_HQIV = (2 / 5 : ℝ) ∧ alpha + gamma_HQIV = 1 :=
  ⟨alpha_eq_3_5, gamma_eq_2_5, alpha_add_gamma⟩

end Hqiv
