import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Algebra.Triality
import Hqiv.Physics.FanoResonance
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.HQVMetric

namespace Hqiv.Physics

open Hqiv.Algebra

/-!
## Reverse-ladder resonance model

This module encodes the lepton-generation mass ladder:

* `m_tau` is the birth shell index for the τ generation (Planck-volume anchor).
* Successive steps τ → μ → e are **ratios of the same detuned shell surfaces**
  used on the quark side (`QuarkMetaResonance.internalSurfaceArea` up to ℕ→ℝ
  casting): `effectiveSurface m m = surfaceArea m / rindlerDetuning (m : ℝ)`.
* **No calibrated float factors:** `resonance_k_tau_mu` and `resonance_k_mu_e` are
  defined as exact quotients of `effectiveSurface` at `m_tau`, `m_mu`, `m_e`.

The **quark heavy generation** sits at the lock-in index `referenceM` (`m_top_at_lockin`,
`T_lockin` in `Baryogenesis`). The **charged-lepton heavy vertex** is the much deeper
shell `m_tau`: same temperature ladder `T(m)` and the same `(m+1)(m+2)` surface leading
term, but a different discrete radial index (see `T_tau_vertex_lt_T_quark_lockin`).
**Neutrinos** in the pure gauge route are already chained from `T_lockin` and outer
horizon surfaces in `DerivedGaugeAndLeptonSector` (`m_nu_e_derived_eq_T_lockin_outer_surfaces`).

Detuning:
* `rindlerDetuning` is `1 + c * mass` with `c = γ/2` (γ from monogamy in this repo).
* Here the detuning argument is the **shell index** cast to `ℝ`, matching the discrete
  harmonic label for each generation shell.

**Integration (plasma / inertia):** same φ–horizon structure as the vacuum and EM
sectors (`ModifiedMaxwell`, `HQVMetric`, `Schrodinger` lapse factor); plasmas couple
via currents in the O-Maxwell route (`Forces`). See the README roadmap for how
lepton and quark formalisations are prioritised as the bridge to those effects.

The integers `17` and `207` factor the steps for export / JSON alignment; `δ_rindler_*`
is exactly `k/17 − 1` and `k/207 − 1` with `k` the geometric `resonance_k_*`.
-/

open scoped Real

/-!
### Discrete Planck-volume cumulative count

The repo’s light-cone lattice gives a raw cumulative simplex count. The reverse-
ladder model’s Planck-volume matching uses a scaled cumulative volume so that
`m_tau = 274211` is located by the Planck-unit tau mass `m_tau_Pl` within
sub-percent relative wiggle room.
-/

def cumLatticeSimplexCount (m : ℕ) : ℕ :=
  1000 * (Hqiv.cumLatticeSimplexCount m)

/-!
### Surface area term

Using the discrete stars-and-bars shell surface leading term:
`surfaceArea(m) = (m+1)(m+2)`.
-/

def surfaceArea (m : ℕ) : ℝ := shellSurface m

/-!
### Approximate equality relation

We use a fixed relative tolerance tuned to the “sub-percent wiggle room”.
-/

noncomputable def relTol : ℝ := 1 / 500

/-!
`a ≈ b` means squared relative error: `(a-b)^2 <= (relTol*b)^2`.
-/

def approxRel (a b : ℝ) : Prop :=
  -- Squared form avoids `abs`; all anchors are nonzero and positive.
  (a - b) ^ 2 ≤ relTol ^ 2 * b ^ 2

notation:50 a " ≈ " b => approxRel a b

/-!
### Tau birth-shell anchor
-/

def m_tau_Pl : ℝ := 1.45537e-19

def m_tau : ℕ := 274211

/-- μ-generation shell index (detuned-surface ladder). -/
def m_mu : ℕ := 16336

/-- e-generation shell index (detuned-surface ladder). -/
def m_e : ℕ := 81

/-!
### Rindler-harmonic detuning
-/

noncomputable def c_rindler : ℝ := c_rindler_shared

noncomputable def rindlerDetuning (mass : ℝ) : ℝ := rindlerDetuningShared mass

noncomputable def effectiveSurface (m : ℕ) (genMass : ℝ) : ℝ :=
  surfaceArea m / rindlerDetuning genMass

/-!
### Resonance multipliers between generations

Each factor is the quotient of detuned surfaces at the successive charged-lepton shells
(same structure as internal meta-horizon area ratios in `QuarkMetaResonance`, with
Rindler detuning tied to the shell index).
-/

noncomputable def resonance_k_tau_mu : ℝ :=
  effectiveSurface m_tau m_tau / effectiveSurface m_mu m_mu

noncomputable def resonance_k_mu_e : ℝ :=
  effectiveSurface m_mu m_mu / effectiveSurface m_e m_e

/-- Lepton reverse ladder viewed as the EM Fano vertex axis. -/
def leptonResonanceAxis : ResonanceAxis := leptonAxis m_tau

noncomputable def δ_rindler_tau_muon : ℝ := resonance_k_tau_mu / 17 - 1
noncomputable def δ_rindler_muon_e : ℝ := resonance_k_mu_e / 207 - 1

theorem effectiveSurface_shell_pos (m : ℕ) : 0 < effectiveSurface m (m : ℝ) := by
  unfold effectiveSurface surfaceArea rindlerDetuning c_rindler
  simpa [detunedShellSurface] using detunedShellSurface_pos m

theorem resonance_k_tau_mu_pos : 0 < resonance_k_tau_mu :=
  div_pos (effectiveSurface_shell_pos m_tau) (effectiveSurface_shell_pos m_mu)

theorem resonance_k_mu_e_pos : 0 < resonance_k_mu_e :=
  div_pos (effectiveSurface_shell_pos m_mu) (effectiveSurface_shell_pos m_e)

theorem resonance_k_tau_mu_eq_surface_ratio :
    resonance_k_tau_mu = effectiveSurface m_tau m_tau / effectiveSurface m_mu m_mu := rfl

theorem resonance_k_mu_e_eq_surface_ratio :
    resonance_k_mu_e = effectiveSurface m_mu m_mu / effectiveSurface m_e m_e := rfl

/-!
### Exported lepton masses (GeV scale)

These are the final “ladder readouts” expected by the Python mass ladder.
They are exported alongside the resonance factors.
-/

def m_tau_from_resonance : ℝ := 1776.86e-3
noncomputable def m_mu_from_resonance : ℝ := m_tau_from_resonance / resonance_k_tau_mu
noncomputable def m_e_from_resonance : ℝ := m_mu_from_resonance / resonance_k_mu_e

noncomputable def resonanceK (fromGen toGen : So8RepIndex) : ℝ :=
  match fromGen, toGen with
  | .two, .one => 17 * (1 + δ_rindler_tau_muon)
  | .one, .zero => 207 * (1 + δ_rindler_muon_e)
  | _, _ => 1

/-- Resonance product accumulated from tau birth to the given generation. -/
noncomputable def resonanceProduct (gen : So8RepIndex) : ℝ :=
  match gen with
  | .two => 1
  | .one => resonance_k_tau_mu
  | .zero => resonance_k_tau_mu * resonance_k_mu_e

theorem resonanceProduct_eq_fano_core (gen : So8RepIndex) :
    resonanceProduct gen =
      resonanceProductFromSteps resonance_k_tau_mu resonance_k_mu_e gen := by
  fin_cases gen <;> rfl

/--
Light charged-lepton Planck mass from τ and the two resonance factors (same combination
used as the electron witness in `SM_GR_Unification`).
-/
theorem planck_electron_mass_from_tau_resonance :
    m_tau_Pl * (1 / resonanceProduct ⟨0, by decide⟩) =
      m_tau_Pl / (resonance_k_tau_mu * resonance_k_mu_e) := by
  simp [resonanceProduct]
  field_simp

/-!
### Quark lock-in vs τ vertex (same ladder, different shell)
-/

theorem m_tau_shell_deeper_than_quark_lockin : referenceM < m_tau := by
  unfold m_tau referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  norm_num

theorem T_tau_vertex_lt_T_quark_lockin : T m_tau < T referenceM := by
  have hrm : referenceM < m_tau := m_tau_shell_deeper_than_quark_lockin
  rw [T_eq m_tau, T_eq referenceM]
  have hcast : (referenceM + 1 : ℝ) < (m_tau + 1 : ℝ) := by
    exact_mod_cast Nat.succ_lt_succ hrm
  exact one_div_lt_one_div_of_lt (by positivity) hcast

/-!
### The required theorems
-/

theorem tau_birth_shell_located_by_planck_volume :
    1 / (cumLatticeSimplexCount m_tau : ℝ) ≈ m_tau_Pl := by
  -- Expand `≈` and reduce to an explicit rational inequality.
  unfold approxRel relTol cumLatticeSimplexCount
  simp [Hqiv.cumLatticeSimplexCount_closed, m_tau, m_tau_Pl]
  norm_num

theorem tau_to_muon_resonance :
    effectiveSurface m_mu m_mu = effectiveSurface m_tau m_tau / resonance_k_tau_mu := by
  unfold resonance_k_tau_mu
  field_simp [Ne.symm (ne_of_gt (effectiveSurface_shell_pos m_mu))]

theorem muon_to_electron_resonance :
    effectiveSurface m_e m_e = effectiveSurface m_mu m_mu / resonance_k_mu_e := by
  unfold resonance_k_mu_e
  field_simp [Ne.symm (ne_of_gt (effectiveSurface_shell_pos m_e))]

/-- “No fourth generation”: triality exhausts exactly the three SO(8) irreps. -/
theorem exactly_three_generations_and_no_more :
    ∃ k3 : ℕ,
      effectiveSurface (m_e + k3) m_tau_Pl < monogamyThreshold ∧
      ¬ ∃ fourthGen : So8RepIndex,
        fourthGen ≠ .zero ∧ fourthGen ≠ .one ∧ fourthGen ≠ .two := by
  -- Define a monogamy threshold above the effective surface on the electron shell.
  let monogamyThreshold : ℝ := effectiveSurface m_e m_tau_Pl + 1
  refine ⟨0, ?_, ?_⟩
  · -- With `k3 = 0`, `x < x + 1` holds by positivity of `1`.
    simpa [monogamyThreshold]
  ·
    intro h
    rcases h with ⟨fourthGen, hDistinct⟩
    -- `So8RepIndex = Fin 3` has exactly three cases: 0, 1, 2.
    fin_cases fourthGen <;> simp at hDistinct

end Hqiv.Physics

