import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.QuantumMechanics.MonogamyTangles
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions

namespace Hqiv.QM

/-!
# Concrete QM Step: W Family Monogamy

Real-amplitude W-family slice

`|ψ⟩ = x |100⟩ + y |010⟩ + z |001⟩`, with `x^2 + y^2 + z^2 = 1`.

For this family, using the standard pure-state expressions:
* `τ_AB = 4 x^2 y^2`
* `τ_AC = 4 x^2 z^2`
* `τ_A|BC = 4 x^2 (y^2 + z^2)`

Hence CKW is saturated:
`τ_AB + τ_AC = τ_A|BC`.
-/

/-- Real-amplitude W-family state parameters. -/
structure WFamily where
  x : ℝ
  y : ℝ
  z : ℝ
  normalized : x ^ 2 + y ^ 2 + z ^ 2 = 1

/-- Pairwise tangle `τ_AB` on the W family. -/
def wTauAB (s : WFamily) : ℝ := 4 * s.x ^ 2 * s.y ^ 2

/-- Pairwise tangle `τ_AC` on the W family. -/
def wTauAC (s : WFamily) : ℝ := 4 * s.x ^ 2 * s.z ^ 2

/-- Global tangle `τ_A|BC` on the W family. -/
def wTauA_BC (s : WFamily) : ℝ := 4 * s.x ^ 2 * (s.y ^ 2 + s.z ^ 2)

theorem wTauAB_nonneg (s : WFamily) : 0 ≤ wTauAB s := by
  unfold wTauAB
  nlinarith [sq_nonneg s.x, sq_nonneg s.y]

theorem wTauAC_nonneg (s : WFamily) : 0 ≤ wTauAC s := by
  unfold wTauAC
  nlinarith [sq_nonneg s.x, sq_nonneg s.z]

theorem wTauA_BC_nonneg (s : WFamily) : 0 ≤ wTauA_BC s := by
  unfold wTauA_BC
  nlinarith [sq_nonneg s.x, sq_nonneg s.y, sq_nonneg s.z]

/-- CKW saturation identity for the W family. -/
theorem w_ckw_saturated (s : WFamily) :
    wTauAB s + wTauAC s = wTauA_BC s := by
  unfold wTauAB wTauAC wTauA_BC
  ring

/-- CKW monogamy for W family (as inequality, from saturation). -/
theorem w_ckw (s : WFamily) :
    ckwMonogamy (wTauAB s) (wTauAC s) (wTauA_BC s) := by
  unfold ckwMonogamy
  simp [w_ckw_saturated s]

/-- HQIV mode-corrected CKW holds for W family. -/
theorem w_corrected_mode (m : ℕ) (s : WFamily) :
    correctedCkwMonogamy m (wTauAB s) (wTauAC s) (wTauA_BC s) := by
  exact corrected_monogamy_of_ckw m (w_ckw s)

/-- HQIV mode+φ-corrected CKW holds for W family. -/
theorem w_corrected_mode_phi (m : ℕ) (s : WFamily) :
    correctedCkwMonogamyPhi m (wTauAB s) (wTauAC s) (wTauA_BC s) := by
  exact corrected_monogamy_of_ckw_phi m (w_ckw s)

/-- Pairwise tangle budget on the W family. -/
def wPairBudget (s : WFamily) : ℝ := wTauAB s + wTauAC s

theorem wPairBudget_nonneg (s : WFamily) : 0 ≤ wPairBudget s := by
  unfold wPairBudget
  exact add_nonneg (wTauAB_nonneg s) (wTauAC_nonneg s)

/-- Decoherence proxy monotonicity on W-family pairwise channel. -/
theorem w_coherence_proxy_step_nonincreasing (m : ℕ) (s : WFamily) :
    coherenceProxy (m + 1) (wPairBudget s) ≤ coherenceProxy m (wPairBudget s) := by
  exact coherenceProxy_step_nonincreasing_unconditional m (wPairBudget_nonneg s)

end Hqiv.QM
