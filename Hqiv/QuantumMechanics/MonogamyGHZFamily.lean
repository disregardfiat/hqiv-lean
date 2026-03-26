import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.QuantumMechanics.MonogamyTangles
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions

namespace Hqiv.QM

/-!
# Concrete QM Step: GHZ Family Monogamy

This module makes the monogamy pipeline concrete on the standard real-amplitude
GHZ slice:

`|ψ⟩ = a |000⟩ + b |111⟩`, with `a^2 + b^2 = 1`.

For this family:
* pairwise tangles vanish (`τ_AB = τ_AC = 0`);
* global tangle is `τ_A|BC = 4 a^2 b^2`.

So CKW is exact and the HQIV mode/phi-corrected inequalities follow immediately.
-/

/-- Real-amplitude GHZ-family state parameters. -/
structure GHZFamily where
  a : ℝ
  b : ℝ
  normalized : a ^ 2 + b ^ 2 = 1

/-- Pairwise tangle `τ_AB` on the GHZ family. -/
def ghzTauAB (_s : GHZFamily) : ℝ := 0

/-- Pairwise tangle `τ_AC` on the GHZ family. -/
def ghzTauAC (_s : GHZFamily) : ℝ := 0

/-- Global tangle `τ_A|BC` on the GHZ family. -/
def ghzTauA_BC (s : GHZFamily) : ℝ := 4 * s.a ^ 2 * s.b ^ 2

/-- Concurrence proxy on the GHZ family: `C_A|BC = 2 |ab|`. -/
def ghzConcurrenceA_BC (s : GHZFamily) : ℝ := 2 * |s.a * s.b|

theorem ghzTauA_BC_nonneg (s : GHZFamily) : 0 ≤ ghzTauA_BC s := by
  unfold ghzTauA_BC
  nlinarith [sq_nonneg s.a, sq_nonneg s.b]

theorem ghzConcurrence_sq_eq_tangle (s : GHZFamily) :
    ghzConcurrenceA_BC s ^ 2 = ghzTauA_BC s := by
  unfold ghzConcurrenceA_BC ghzTauA_BC
  ring_nf
  rw [sq_abs]
  ring

/-- CKW monogamy for GHZ family (`0 + 0 ≤ 4 a² b²`). -/
theorem ghz_ckw (s : GHZFamily) :
    ckwMonogamy (ghzTauAB s) (ghzTauAC s) (ghzTauA_BC s) := by
  unfold ckwMonogamy ghzTauAB ghzTauAC
  simpa using ghzTauA_BC_nonneg s

/-- HQIV mode-corrected CKW holds for GHZ family. -/
theorem ghz_corrected_mode (m : ℕ) (s : GHZFamily) :
    correctedCkwMonogamy m (ghzTauAB s) (ghzTauAC s) (ghzTauA_BC s) := by
  exact corrected_monogamy_of_ckw m (ghz_ckw s)

/-- HQIV mode+φ-corrected CKW holds for GHZ family. -/
theorem ghz_corrected_mode_phi (m : ℕ) (s : GHZFamily) :
    correctedCkwMonogamyPhi m (ghzTauAB s) (ghzTauAC s) (ghzTauA_BC s) := by
  exact corrected_monogamy_of_ckw_phi m (ghz_ckw s)

/-- GHZ pairwise tangle budget (vanishes identically). -/
def ghzPairBudget (s : GHZFamily) : ℝ := ghzTauAB s + ghzTauAC s

theorem ghzPairBudget_eq_zero (s : GHZFamily) : ghzPairBudget s = 0 := by
  unfold ghzPairBudget ghzTauAB ghzTauAC
  ring

/--
Decoherence monotonicity on the GHZ pairwise channel is immediate from the
unconditional φ-augmented theorem.
-/
theorem ghz_coherence_proxy_step_nonincreasing (m : ℕ) (s : GHZFamily) :
    coherenceProxy (m + 1) (ghzPairBudget s) ≤ coherenceProxy m (ghzPairBudget s) := by
  apply coherenceProxy_step_nonincreasing_unconditional
  rw [ghzPairBudget_eq_zero s]

end Hqiv.QM
