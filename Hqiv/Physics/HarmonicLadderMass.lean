import Hqiv.Geometry.AuxiliaryField
import Hqiv.Physics.BoundStates
import Hqiv.Physics.HarmonicLadderGlobalDetuning

/-!
# Harmonic ladder and mass couplings

This module is the **single place** where the HQIV **discrete null-cone / temperature ladder**
is tied to **effective couplings and hydrogenic binding scales** without invoking Spin(8)
triality. The logical order for phenomenology is:

1. **Temperature ladder** `T m = T_Pl / (m+1)` with `T_Pl = 1` (`OctonionicLightCone`, `AuxiliaryField`).
2. **Auxiliary field** `φ(m) = phiTemperatureCoeff / T(m) = phiTemperatureCoeff * (m+1)` (`phi_of_shell_closed_form`).
3. **Curvature imprint** `shell_shape m` expressed from the same ladder (`shell_shape_T_formula`,
   `shell_shape_in_terms_of_phi`).
4. **O–Maxwell effective inverse α** at φ: `one_over_alpha_eff (phi_of_shell m) c` (`SM_GR_Unification`),
   hence `alphaEffShell m c` (`Schrodinger`).
5. **Hydrogenic binding** at shell `m`: `expectedGroundEnergyAtShell` / `E_bind_atomic_shell_magnitude`
   scale as `(α_eff(m))²` (`BoundStates`).

Triality (`SMEmbedding`, `Triality`) is a **separate** representation-layer fact; it does not
replace this ladder for mass/coupling structure — see `SMEmbedding` module doc.

**Reference:** same ladder as `phi_of_shell`, `shell_shape`, and `Hqiv.alphaEffShell` in
`Schrodinger` / `BoundStates`.
-/

namespace Hqiv.Physics

open Hqiv

/-- Effective α at shell `m` is the inverse of `one_over_alpha_eff` evaluated at **φ(m)**. -/
theorem alphaEffAtShell_eq_inverse_one_over_alpha_eff (m : ℕ) (c : ℝ) :
    alphaEffAtShell m c = (one_over_alpha_eff (phi_of_shell m) c)⁻¹ := by
  unfold alphaEffAtShell Hqiv.alphaEffShell Hqiv.oneOverAlphaEffShell
  rfl

/-- φ(m) on the discrete ladder: explicit linear growth in shell index (`AuxiliaryField`). -/
theorem phi_of_shell_from_ladder (m : Nat) :
    phi_of_shell m = phiTemperatureCoeff * (m + 1 : ℝ) :=
  phi_of_shell_closed_form m

/-- Curvature `shell_shape m` from the **same** temperature ratio `T_Pl / T m` as the ladder
    (`AuxiliaryField.shell_shape_T_formula`). -/
theorem shell_shape_from_temperature_ladder (m : Nat) :
    shell_shape m
      = (1 / (m + 1 : ℝ)) * (1 + alpha * Real.log (T_Pl / T m)) :=
  shell_shape_T_formula m

/-- Atomic binding **magnitude** at shell `m` is μ Z² α_eff(m)² / 2 (definitional). -/
theorem E_bind_atomic_magnitude_eq (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ) :
    E_bind_atomic_shell_magnitude m Z μ c
      = μ * (Z : ℝ) ^ 2 * (alphaEffAtShell m c) ^ 2 / 2 :=
  rfl

/-- Ground-state energy at shell `m` (signed) from the same α_eff(m). -/
theorem expectedGroundEnergyAtShell_eq (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ) :
    expectedGroundEnergyAtShell m Z μ c
      = - μ * (Z : ℝ) ^ 2 * (alphaEffAtShell m c) ^ 2 / 2 :=
  rfl

/-!
## One-line packaging

Use `harmonic_ladder_mass_coupling_chain` when you want a single `∧` stating that α_eff at
shell `m` comes from φ(m) and binding scales with its square.
-/

/-- Couplings at shell `m` factor through `phi_of_shell m`; binding energy uses `alphaEffAtShell`. -/
theorem harmonic_ladder_mass_coupling_chain (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ) :
    alphaEffAtShell m c = (one_over_alpha_eff (phi_of_shell m) c)⁻¹
      ∧ E_bind_atomic_shell_magnitude m Z μ c
          = μ * (Z : ℝ) ^ 2 * (one_over_alpha_eff (phi_of_shell m) c)⁻¹ ^ 2 / 2 := by
  constructor
  · exact alphaEffAtShell_eq_inverse_one_over_alpha_eff m c
  · rw [E_bind_atomic_magnitude_eq, alphaEffAtShell_eq_inverse_one_over_alpha_eff m c]

end Hqiv.Physics
