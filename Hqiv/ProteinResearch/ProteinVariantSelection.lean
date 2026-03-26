import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Hqiv.QM

/-!
# PROtien Variant Triage and Selection (Formal)

This module formalizes a decision layer for the five tested stepwise variants
reported in the PROtien run table.

Objective orientation (all lower is better):
* `finalRMSD`
* `finalGap`
* `caClashes`
* `ramOutliers`
* `missedContacts`
* `spuriousTight`

Primary admissibility gate (physics-first):
* clashes `≤ 5`
* Ramachandran outliers `= 0`
-/

inductive Variant
  | resonant_em_refresh_horizon15
  | resonant_no_em_refresh
  | legacy_sqrt_6axis_no_barrier_floor
  | sqrt_em_refresh_large_disp035
  | sqrt_em_refresh_horizon15
deriving DecidableEq, Repr

def finalRMSD : Variant → ℝ
  | .resonant_em_refresh_horizon15 => 25.315
  | .resonant_no_em_refresh => 25.350
  | .legacy_sqrt_6axis_no_barrier_floor => 25.405
  | .sqrt_em_refresh_large_disp035 => 25.428
  | .sqrt_em_refresh_horizon15 => 25.431

def finalGap : Variant → ℝ
  | .resonant_em_refresh_horizon15 => 39.805
  | .resonant_no_em_refresh => 40.184
  | .legacy_sqrt_6axis_no_barrier_floor => 38.739
  | .sqrt_em_refresh_large_disp035 => 39.701
  | .sqrt_em_refresh_horizon15 => 39.859

def caClashes : Variant → ℕ
  | .resonant_em_refresh_horizon15 => 2
  | .resonant_no_em_refresh => 3
  | .legacy_sqrt_6axis_no_barrier_floor => 13
  | .sqrt_em_refresh_large_disp035 => 5
  | .sqrt_em_refresh_horizon15 => 10

def ramOutliers : Variant → ℕ
  | .resonant_em_refresh_horizon15 => 0
  | .resonant_no_em_refresh => 0
  | .legacy_sqrt_6axis_no_barrier_floor => 0
  | .sqrt_em_refresh_large_disp035 => 0
  | .sqrt_em_refresh_horizon15 => 0

def missedContacts : Variant → ℕ
  | .resonant_em_refresh_horizon15 => 56
  | .resonant_no_em_refresh => 56
  | .legacy_sqrt_6axis_no_barrier_floor => 56
  | .sqrt_em_refresh_large_disp035 => 56
  | .sqrt_em_refresh_horizon15 => 56

def spuriousTight : Variant → ℕ
  | .resonant_em_refresh_horizon15 => 18
  | .resonant_no_em_refresh => 17
  | .legacy_sqrt_6axis_no_barrier_floor => 18
  | .sqrt_em_refresh_large_disp035 => 18
  | .sqrt_em_refresh_horizon15 => 18

/-- Hard admissibility gate for physically plausible candidates. -/
def admissible (v : Variant) : Prop :=
  caClashes v ≤ 5 ∧ ramOutliers v = 0

/-- Weak Pareto dominance over key geometry/fold metrics. -/
def dominates (a b : Variant) : Prop :=
  finalRMSD a ≤ finalRMSD b ∧
  finalGap a ≤ finalGap b ∧
  caClashes a ≤ caClashes b ∧
  missedContacts a ≤ missedContacts b

/-- Strictly better in at least one tracked metric. -/
def strictlyBetterSomewhere (a b : Variant) : Prop :=
  finalRMSD a < finalRMSD b ∨
  finalGap a < finalGap b ∨
  caClashes a < caClashes b ∨
  missedContacts a < missedContacts b

/-- Dominance with strict improvement somewhere. -/
def strictlyDominates (a b : Variant) : Prop :=
  dominates a b ∧ strictlyBetterSomewhere a b

theorem admissible_resonant_em_refresh_horizon15 :
    admissible .resonant_em_refresh_horizon15 := by
  unfold admissible caClashes ramOutliers
  norm_num

theorem admissible_resonant_no_em_refresh :
    admissible .resonant_no_em_refresh := by
  unfold admissible caClashes ramOutliers
  norm_num

theorem admissible_sqrt_em_refresh_large_disp035 :
    admissible .sqrt_em_refresh_large_disp035 := by
  unfold admissible caClashes ramOutliers
  norm_num

theorem not_admissible_legacy_sqrt_6axis_no_barrier_floor :
    ¬ admissible .legacy_sqrt_6axis_no_barrier_floor := by
  unfold admissible caClashes ramOutliers
  norm_num

theorem not_admissible_sqrt_em_refresh_horizon15 :
    ¬ admissible .sqrt_em_refresh_horizon15 := by
  unfold admissible caClashes ramOutliers
  norm_num

theorem resonant_em_refresh_strictly_dominates_resonant_no_em :
    strictlyDominates .resonant_em_refresh_horizon15 .resonant_no_em_refresh := by
  unfold strictlyDominates dominates strictlyBetterSomewhere
  unfold finalRMSD finalGap caClashes missedContacts
  constructor
  · norm_num
  · left
    norm_num

theorem resonant_em_refresh_beats_sqrt_large_disp_on_rmsd_and_clashes :
    finalRMSD .resonant_em_refresh_horizon15 < finalRMSD .sqrt_em_refresh_large_disp035 ∧
    caClashes .resonant_em_refresh_horizon15 < caClashes .sqrt_em_refresh_large_disp035 := by
  unfold finalRMSD caClashes
  norm_num

/--
Physics-safe winner theorem:
among admissible variants in this benchmark table, the resonant EM-refresh
horizon-15 variant minimizes final RMSD.
-/
theorem resonant_em_refresh_best_rmsd_among_admissible (v : Variant)
    (hav : admissible v) :
    finalRMSD .resonant_em_refresh_horizon15 ≤ finalRMSD v := by
  cases v
  · unfold finalRMSD
    norm_num
  · unfold finalRMSD
    norm_num
  · unfold admissible caClashes ramOutliers at hav
    norm_num at hav
  · unfold finalRMSD
    norm_num
  · unfold admissible caClashes ramOutliers at hav
    norm_num at hav

/--
Coagula policy theorem:
if a variant is selected only when admissible and not strictly dominated by any
admissible competitor, then selecting `resonant_em_refresh_horizon15` is justified.
-/
theorem coagula_selection_justified :
    admissible .resonant_em_refresh_horizon15 ∧
    (∀ v, admissible v → strictlyDominates v .resonant_em_refresh_horizon15 → False) := by
  constructor
  · exact admissible_resonant_em_refresh_horizon15
  · intro v hv hdom
    cases v
    · unfold strictlyDominates dominates strictlyBetterSomewhere at hdom
      norm_num at hdom
    · unfold strictlyDominates dominates strictlyBetterSomewhere at hdom
      unfold finalRMSD finalGap caClashes missedContacts at hdom
      norm_num at hdom
    · unfold admissible at hv
      unfold caClashes ramOutliers at hv
      norm_num at hv
    · unfold strictlyDominates dominates strictlyBetterSomewhere at hdom
      unfold finalRMSD finalGap caClashes missedContacts at hdom
      norm_num at hdom
    · unfold admissible at hv
      unfold caClashes ramOutliers at hv
      norm_num at hv

end Hqiv.QM
