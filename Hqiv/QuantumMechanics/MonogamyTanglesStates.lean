import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.QuantumMechanics.MonogamyTangles

namespace Hqiv.QM

/-!
# Three-Qubit State Layer for HQIV Monogamy

This module adds a lightweight state-level scaffold:

* explicit three-qubit amplitudes `Fin 2 → Fin 2 → Fin 2 → ℂ`;
* a normalization predicate;
* a `TangleModel` interface that supplies state-level tangle observables.

The interface lets us prove HQIV mode-corrected monogamy theorems now, and later
replace the abstract observables with explicit concurrence/tangle formulas.
-/

/-- Pure three-qubit state amplitudes on the computational basis. -/
abbrev ThreeQubitAmp := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- Squared-norm weight of a single computational-basis amplitude. -/
noncomputable def ampWeight (ψ : ThreeQubitAmp) (i j k : Fin 2) : ℝ :=
  Complex.normSq (ψ i j k)

/-- Total norm-squared of a three-qubit state. -/
noncomputable def totalNormSq (ψ : ThreeQubitAmp) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2, ampWeight ψ i j k

/-- Unit-normalized pure three-qubit state predicate. -/
def isNormalizedThreeQubit (ψ : ThreeQubitAmp) : Prop :=
  totalNormSq ψ = 1

/--
Abstract interface for state-level tangles.

`tauAB`, `tauAC`, `tauA_BC` are intended to become concrete concurrence/tangle
expressions derived from `ψ` (e.g. via reduced density matrices).
-/
structure TangleModel where
  tauAB : ThreeQubitAmp → ℝ
  tauAC : ThreeQubitAmp → ℝ
  tauA_BC : ThreeQubitAmp → ℝ
  tauAB_nonneg : ∀ ψ, 0 ≤ tauAB ψ
  tauAC_nonneg : ∀ ψ, 0 ≤ tauAC ψ
  tauA_BC_nonneg : ∀ ψ, 0 ≤ tauA_BC ψ
  ckw_holds : ∀ ψ, isNormalizedThreeQubit ψ →
    ckwMonogamy (tauAB ψ) (tauAC ψ) (tauA_BC ψ)

/-- Pairwise tangle budget in a given model. -/
def pairwiseTangleSum (M : TangleModel) (ψ : ThreeQubitAmp) : ℝ :=
  M.tauAB ψ + M.tauAC ψ

/-- HQIV mode-corrected pairwise tangle budget. -/
noncomputable def correctedPairwiseTangleSum (M : TangleModel) (m : ℕ)
    (ψ : ThreeQubitAmp) : ℝ :=
  correctedPairTangle m (M.tauAB ψ) + correctedPairTangle m (M.tauAC ψ)

/--
State-level HQIV corrected monogamy:
any normalized state satisfying CKW in model `M` also satisfies the shell-weighted
HQIV monogamy inequality.
-/
theorem corrected_monogamy_of_model (M : TangleModel) (m : ℕ) (ψ : ThreeQubitAmp)
    (hψ : isNormalizedThreeQubit ψ) :
    correctedCkwMonogamy m (M.tauAB ψ) (M.tauAC ψ) (M.tauA_BC ψ) := by
  exact corrected_monogamy_of_ckw m (M.ckw_holds ψ hψ)

/--
If `etaMode m ≤ 1`, the HQIV correction tightens the pairwise tangle sum
for every state in the model.
-/
theorem corrected_pairwise_budget_le_uncorrected (M : TangleModel) (m : ℕ)
    (ψ : ThreeQubitAmp) (heta : etaMode m ≤ 1) :
    correctedPairwiseTangleSum M m ψ ≤ pairwiseTangleSum M ψ := by
  unfold correctedPairwiseTangleSum pairwiseTangleSum
  have hsum_nonneg : 0 ≤ M.tauAB ψ + M.tauAC ψ := by
    exact add_nonneg (M.tauAB_nonneg ψ) (M.tauAC_nonneg ψ)
  exact corrected_pair_sum_le_uncorrected m hsum_nonneg heta

end Hqiv.QM
