import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.QuantumMechanics.MonogamyTangles
import Hqiv.QuantumMechanics.MonogamyGHZFamily
import Hqiv.QuantumMechanics.MonogamyWFamily

namespace Hqiv.QM

/-!
# GHZ-W Interpolation (Effective Tangle Path)

This module defines a simple interpolation parameter `lam ∈ [0,1]` between the
already formalized GHZ and W family tangle triplets. It provides:

* CKW along the whole path;
* endpoint identities (`λ=0` is W, `λ=1` is GHZ);
* HQIV mode and mode+φ corrected monogamy along the same path.
-/

structure GHZWInterp where
  ghz : GHZFamily
  w : WFamily
  lam : ℝ
  hlam0 : 0 ≤ lam
  hlam1 : lam ≤ 1

/-- Interpolated pairwise AB tangle. -/
def interpTauAB (s : GHZWInterp) : ℝ :=
  (1 - s.lam) * wTauAB s.w + s.lam * ghzTauAB s.ghz

/-- Interpolated pairwise AC tangle. -/
def interpTauAC (s : GHZWInterp) : ℝ :=
  (1 - s.lam) * wTauAC s.w + s.lam * ghzTauAC s.ghz

/-- Interpolated global tangle. -/
def interpTauA_BC (s : GHZWInterp) : ℝ :=
  (1 - s.lam) * wTauA_BC s.w + s.lam * ghzTauA_BC s.ghz

/-- CKW holds all along the interpolation path. -/
theorem interp_ckw (s : GHZWInterp) :
    ckwMonogamy (interpTauAB s) (interpTauAC s) (interpTauA_BC s) := by
  unfold ckwMonogamy interpTauAB interpTauAC interpTauA_BC
  have hw : wTauAB s.w + wTauAC s.w ≤ wTauA_BC s.w := w_ckw s.w
  have hg : ghzTauAB s.ghz + ghzTauAC s.ghz ≤ ghzTauA_BC s.ghz := ghz_ckw s.ghz
  have h1m : 0 ≤ 1 - s.lam := sub_nonneg.mpr s.hlam1
  nlinarith [hw, hg, h1m, s.hlam0]

/-- Interpolation endpoint `lam = 0` recovers W tangles. -/
theorem interp_at_zero (s : GHZWInterp) (h0 : s.lam = 0) :
    interpTauAB s = wTauAB s.w ∧
    interpTauAC s = wTauAC s.w ∧
    interpTauA_BC s = wTauA_BC s.w := by
  simp [interpTauAB, interpTauAC, interpTauA_BC, h0]

/-- Interpolation endpoint `lam = 1` recovers GHZ tangles. -/
theorem interp_at_one (s : GHZWInterp) (h1 : s.lam = 1) :
    interpTauAB s = ghzTauAB s.ghz ∧
    interpTauAC s = ghzTauAC s.ghz ∧
    interpTauA_BC s = ghzTauA_BC s.ghz := by
  simp [interpTauAB, interpTauAC, interpTauA_BC, h1]

/-- CKW slack (global minus pairwise budget) along interpolation. -/
def interpSlack (s : GHZWInterp) : ℝ :=
  interpTauA_BC s - (interpTauAB s + interpTauAC s)

theorem interpSlack_nonneg (s : GHZWInterp) : 0 ≤ interpSlack s := by
  unfold interpSlack
  exact sub_nonneg.mpr (interp_ckw s)

/-- HQIV mode-corrected CKW along interpolation. -/
theorem interp_corrected_mode (m : ℕ) (s : GHZWInterp) :
    correctedCkwMonogamy m (interpTauAB s) (interpTauAC s) (interpTauA_BC s) := by
  exact corrected_monogamy_of_ckw m (interp_ckw s)

/-- HQIV mode+φ-corrected CKW along interpolation. -/
theorem interp_corrected_mode_phi (m : ℕ) (s : GHZWInterp) :
    correctedCkwMonogamyPhi m (interpTauAB s) (interpTauAC s) (interpTauA_BC s) := by
  exact corrected_monogamy_of_ckw_phi m (interp_ckw s)

end Hqiv.QM
