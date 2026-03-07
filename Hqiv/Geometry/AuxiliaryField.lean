import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

import Hqiv.Geometry.OctonionicLightCone

namespace Hqiv

/-!
# HQIV Auxiliary Field φ

The auxiliary scalar field φ in the homogeneous limit encodes the horizon-entanglement
and varying-coupling effect that feeds into the HQVM metric and effective Friedmann
dynamics.

All definitions here are in natural Planck units (T_Pl = 1, c = 1). The field is tied
directly to the same temperature ladder that underlies the curvature imprint.
-/

/-- Planck temperature in natural units. -/
noncomputable def T_Pl : ℝ := 1.0

/-- **T_Pl = 1 in natural units** (proved). -/
theorem T_Pl_eq : T_Pl = 1 := by unfold T_Pl; norm_num

/-- Temperature at radial shell `m` (HQIV temperature ladder). -/
noncomputable def T (m : Nat) : ℝ := T_Pl / (m + 1 : ℝ)

/-- Temperature ladder in closed form (no separate def): T(m) = 1/(m+1). -/
theorem T_eq (m : Nat) : T m = 1 / (m + 1 : ℝ) := by unfold T T_Pl; norm_num

/-- **T(m) is positive** for all shells (temperature ladder in natural units). -/
theorem T_pos (m : Nat) : 0 < T m := by
  rw [T_eq m]; positivity

/-- Auxiliary field φ at shell `m` in the homogeneous limit.

Formally φ(m) = 2 / Θ_local(m); here we identify Θ_local(m) with the temperature
ladder T(m) in natural units as suggested in the paper. -/
noncomputable def phi_of_shell (m : Nat) : ℝ :=
  2.0 / T m

/-- Continuous version of the auxiliary field as a function of local temperature. -/
noncomputable def phi_of_T (t : ℝ) : ℝ :=
  2.0 / t

/-- Bridge lemma: the discrete shell version equals the continuous version. -/
theorem phi_of_shell_eq_phi_of_T (m : Nat) :
    phi_of_shell m = phi_of_T (T m) := by
  unfold phi_of_shell phi_of_T; rw [T_eq m]

/-- Helper: explicit closed form for φ(m) in terms of the shell index. -/
theorem phi_of_shell_closed_form (m : Nat) :
    phi_of_shell m = 2.0 * (m + 1 : ℝ) := by
  unfold phi_of_shell T T_Pl
  field_simp
  norm_num

/-- **φ(m) is positive** and **φ(m) ≥ 2** for all shells (φ(0) = 2, then grows). -/
theorem phi_of_shell_pos (m : Nat) : 0 < phi_of_shell m := by
  rw [phi_of_shell_closed_form]; positivity

theorem phi_of_shell_ge_two (m : Nat) : (2 : ℝ) ≤ phi_of_shell m := by
  rw [phi_of_shell_closed_form]; have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; nlinarith

/-- Key connection lemma: `shell_shape` can be expressed purely in terms of φ.

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
    rw [phi_of_shell_closed_form m]; field_simp
  -- Prove LHS = (1/(m+1))*... = (1/(φ/2))*... using shell_shape_formula and hphi_div.
  trans (1 / (m + 1 : ℝ)) * (1 + alpha * Real.log (m + 1 : ℝ))
  · exact shell_shape_formula m
  · conv_rhs => repeat rw [hphi_div]; rfl

/-- **Shell shape from the temperature ladder:**  

Starting from the paper's expression
\[
  \text{shell\_shape}(m)
    = \frac{1}{m+1}\Bigl(1 + \alpha \log\frac{T_{\rm Pl}}{T(m)}\Bigr),
\]
and using the HQIV temperature ladder `T m = T_Pl / (m+1)` with `T_Pl = 1`
(`T_eq` and `T_Pl_eq`), we recover exactly the same formula used to define
`shell_shape` and `curvatureDensity`. This shows that the shape is *derived*
from the discrete temperature ladder, not an independent input. -/
theorem shell_shape_T_formula (m : Nat) :
    shell_shape m
      = (1 / (m + 1 : ℝ))
          * (1 + alpha * Real.log (T_Pl / T m)) := by
  -- First rewrite `T_Pl / T m` purely in terms of `(m+1)`.
  have hT : T_Pl / T m = (m + 1 : ℝ) := by
    rw [T_eq m, T_Pl_eq]
    field_simp [Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m)]
  -- Start from the closed-form shape that uses `m+1`.
  rw [shell_shape_formula m]
  congr 1
  rw [hT]

-- Quick checks (visible in infoview)
#check phi_of_shell 0
#check phi_of_shell_closed_form
#check shell_shape_in_terms_of_phi

end Hqiv

