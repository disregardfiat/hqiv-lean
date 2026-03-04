import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Hqiv.Geometry.OctonionicLightCone

namespace Hqiv

/‑!
# HQIV Auxiliary Field φ

The auxiliary scalar field φ in the homogeneous limit encodes the horizon‑entanglement
and varying‑coupling effect that feeds into the HQVM metric and effective Friedmann
dynamics.

All definitions here are in natural Planck units (T_Pl = 1, c = 1). The field is tied
directly to the same temperature ladder that underlies the curvature imprint.
‑/

/‑‑ Planck temperature in natural units. -/
def T_Pl : ℝ := 1.0

/‑‑ Temperature at radial shell `m` (HQIV temperature ladder). -/
def T (m : Nat) : ℝ := T_Pl / (m + 1 : ℝ)

/‑‑ Auxiliary field φ at shell `m` in the homogeneous limit.

Formally φ(m) = 2 / Θ_local(m); here we identify Θ_local(m) with the temperature
ladder T(m) in natural units as suggested in the paper. -/
def phi_of_shell (m : Nat) : ℝ :=
  2.0 / T m

/‑‑ Continuous version of the auxiliary field as a function of local temperature. -/
def phi_of_T (t : ℝ) : ℝ :=
  2.0 / t

/‑‑ Bridge lemma: the discrete shell version equals the continuous version. -/
theorem phi_of_shell_eq_phi_of_T (m : Nat) :
    phi_of_shell m = phi_of_T (T m) := by
  rfl

/‑‑ Helper: explicit closed form for φ(m) in terms of the shell index. -/
theorem phi_of_shell_closed_form (m : Nat) :
    phi_of_shell m = 2.0 * (m + 1 : ℝ) := by
  unfold phi_of_shell T T_Pl
  -- 2 / (1 / (m+1)) = 2 * (m+1)
  field_simp

/‑‑ Key connection lemma: `shell_shape` can be expressed purely in terms of φ.

Using the closed form φ(m) = 2(m+1), we have φ(m)/2 = m+1, so the original
shell shape
  shell_shape m = (1/(m+1)) * (1 + α log(m+1))
can be rewritten with the argument φ(m)/2. This makes φ reusable on the
HQVM / Friedmann side without duplicating the curvature definitions. -/
theorem shell_shape_in_terms_of_phi (m : Nat) :
    shell_shape m
      = (1 / (phi_of_shell m / 2.0))
          * (1 + alpha * Real.log (phi_of_shell m / 2.0)) := by
  -- First rewrite φ(m)/2 as (m+1).
  have hphi_div :
      phi_of_shell m / 2.0 = (m + 1 : ℝ) := by
    have hphi := phi_of_shell_closed_form m
    simp [hphi]  -- (2*(m+1))/2 = m+1
  -- Now unfold `shell_shape` and rewrite using `hphi_div`.
  unfold shell_shape
  -- `simp` eliminates the let‑binding and rewrites the log argument.
  simp [hphi_div]

-- Quick checks (visible in infoview)
#check phi_of_shell 0
#check phi_of_shell_closed_form
#check shell_shape_in_terms_of_phi

end Hqiv

