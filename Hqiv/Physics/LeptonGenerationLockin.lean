import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.Baryogenesis
import Hqiv.Physics.FanoResonance
import Hqiv.Physics.SurfaceWaveSelfClock

namespace Hqiv.Physics

open scoped Real
open Hqiv

/-!
# Lepton generations parallel to quark lock-in (τ at reference horizon; μ, e on larger shells)

Lock-in supplies the **birth** condition; `SurfaceWaveSelfClock` + rapidity updates model relaxation
along the horizon ladder.

**Charged-lepton resonance factors** (`effectiveSurface`, `resonance_k_*`, `m_tau_Pl`, …) live in
`ChargedLeptonResonance`, using the shell triple below.

This module is the **structural** story aligned with **`QuarkMetaResonance`**: **decay / ordering
toward larger shells for lighter generations**, with the **electron on the highest shell** among
e, μ, τ (same narrative as the quark ladder; sector-specific ℕ values may differ).

* **Heavy generation (τ)** uses the **same discrete lock-in shell** as quark top:
  **`leptonHeavyVertexShell = referenceM`** (`m_top_at_lockin`, `m_lockin`).
* **μ and e** sit on **strictly larger** shell indices than τ with **increasing** leading surface
  `(m+1)(m+2)` — **lighter** generations on **outer** shells in this ℕ ordering.
* **Non-integer shells:** Lean uses **ℕ** here for `shellSurface` / `geometricResonanceStep`;
  a continuous shell coordinate in `ℝ` would be a separate layer (ratios can still match).
* **`T_lockin_now_lepton_fanovertex`** is **`T` at that shell**, hence **`T_lockin`** (same
  temperature as baryogenesis lock-in).

Resonance ratios between consecutive shells are **`geometricResonanceStep`** (detuned
surfaces), matching the quark internal ladder.

Shell numerals **`81`** and **`16336`** for μ/e are **placeholders** (ordered, separated from
`referenceM = 4`); replace when a first-principles pick is fixed.
-/

/-- **τ-generation shell:** quark-parallel heavy vertex at discrete lock-in (`referenceM`). -/
def leptonHeavyVertexShell : ℕ := referenceM

/-- **μ-generation shell** (strictly larger than `leptonHeavyVertexShell`). -/
def leptonMuonShell : ℕ := 81

/-- **e-generation shell** (strictly larger than `leptonMuonShell`). -/
def leptonElectronShell : ℕ := 16336

/-- Temperature at the τ / lock-in lepton fanovertex: equals **`T_lockin`**. -/
noncomputable def T_lockin_now_lepton_fanovertex : ℝ :=
  T leptonHeavyVertexShell

theorem leptonHeavyVertexShell_eq_referenceM : leptonHeavyVertexShell = referenceM :=
  rfl

theorem leptonHeavyVertexShell_eq_m_lockin : leptonHeavyVertexShell = m_lockin :=
  leptonHeavyVertexShell_eq_referenceM.trans m_lockin_eq_referenceM.symm

theorem T_lockin_now_lepton_fanovertex_eq_T_lockin :
    T_lockin_now_lepton_fanovertex = T_lockin := by
  unfold T_lockin_now_lepton_fanovertex T_lockin
  rfl

theorem lepton_shells_ordered :
    leptonHeavyVertexShell < leptonMuonShell ∧ leptonMuonShell < leptonElectronShell := by
  unfold leptonHeavyVertexShell leptonMuonShell leptonElectronShell referenceM qcdShell
    stepsFromQCDToLockin latticeStepCount
  constructor <;> norm_num

theorem shellSurface_lepton_chain_strict :
    shellSurface leptonHeavyVertexShell < shellSurface leptonMuonShell ∧
      shellSurface leptonMuonShell < shellSurface leptonElectronShell := by
  unfold shellSurface leptonHeavyVertexShell leptonMuonShell leptonElectronShell referenceM
    qcdShell stepsFromQCDToLockin latticeStepCount
  constructor <;> norm_num

/-- τ → μ geometric step (detuned surfaces), same combinator as quark internal octaves. -/
noncomputable def geometricResonanceStep_lepton_tau_mu : ℝ :=
  geometricResonanceStep leptonHeavyVertexShell leptonMuonShell

/-- μ → e geometric step. -/
noncomputable def geometricResonanceStep_lepton_mu_e : ℝ :=
  geometricResonanceStep leptonMuonShell leptonElectronShell

theorem geometricResonanceStep_lepton_tau_mu_pos : 0 < geometricResonanceStep_lepton_tau_mu :=
  geometricResonanceStep_pos leptonHeavyVertexShell leptonMuonShell

theorem geometricResonanceStep_lepton_mu_e_pos : 0 < geometricResonanceStep_lepton_mu_e :=
  geometricResonanceStep_pos leptonMuonShell leptonElectronShell

/-- Ladder temperature drops along μ and e (larger `m` ⇒ smaller `T(m)`). -/
theorem T_lepton_mu_lt_T_tau : T leptonMuonShell < T leptonHeavyVertexShell := by
  have h := lepton_shells_ordered.1
  rw [T_eq, T_eq]
  have h' : (leptonHeavyVertexShell + 1 : ℝ) < (leptonMuonShell + 1 : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ h
  exact one_div_lt_one_div_of_lt (by positivity) h'

theorem T_lepton_e_lt_T_mu : T leptonElectronShell < T leptonMuonShell := by
  have h := lepton_shells_ordered.2
  rw [T_eq, T_eq]
  have h' : (leptonMuonShell + 1 : ℝ) < (leptonElectronShell + 1 : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ h
  exact one_div_lt_one_div_of_lt (by positivity) h'

/-- τ birth line: at zero cumulative rapidity, self-clock base phase matches the Compton quarter-turn at `T_lockin`. -/
theorem lepton_tau_birth_at_lockin :
    selfClockPhase leptonHeavyVertexShell 0 = compton_quarter_turn_at_T_lockin := by
  simp [selfClockPhase, compton_quarter_turn_at_T_lockin, comptonAngularFrequency,
    leptonHeavyVertexShell_eq_m_lockin, add_zero]

end Hqiv.Physics
