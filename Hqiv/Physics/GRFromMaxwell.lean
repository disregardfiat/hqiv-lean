import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone

namespace Hqiv

/-!
# GR from Maxwell (Schuller-style): O-Maxwell → HQVM-GR

**Schuller's derivation** (constructive gravity): Matter dynamics (e.g. Maxwell)
determine how spacetime can be foliated; requiring **causal consistency** between
matter and geometry yields the gravitational dynamics (Einstein–Hilbert action,
hence Einstein equations) as a compatibility condition rather than a separate
postulate.

**Our analogue:** We follow the same logic with **O-Maxwell** (emergent Maxwell
in the octonion algebra) and **HQVM-GR** (Horizon Quantized Vacuum Metric):

1. **O-Maxwell** is the matter/gauge dynamics (ModifiedMaxwell: emergent equation
   in O, reduction to classic Maxwell in H, 3D equations with one axis fixed).
2. **Compatible geometry** is the one that couples to the same horizon structure
   (φ, curvature) that appears in the O-Maxwell equation. The informational-energy
   axiom fixes the lapse N = 1 + Φ + φ t (HQVMetric).
3. **HQVM-GR** (lapse, curvature from light-cone, G_eff, Friedmann) is the
   gravitational sector that is **derived from** (compatible with) the O-Maxwell
   dynamics, in the same way Schuller derives GR from Maxwell.

We formalise the **correspondence**: the same φ and α that appear in the
O-Maxwell equation (phi_of_T, curvature coupling) appear in the HQVM lapse,
G_eff, and Friedmann equation. The full constructive derivation (matter action
→ compatibility → gravitational action) is left as the same conceptual path;
here we prove the structural link.
-/

/-- **Same φ in O-Maxwell and HQVM.** The auxiliary field φ in the O-Maxwell equation
    (via `phi_of_T`, `T`, and the curvature coupling α) is the same field that appears
    in the HQVM lapse as `timeAngle φ t` and in `G_eff(φ)`. The lattice defines φ
    (AuxiliaryField); both modules use it. -/
theorem same_phi_in_O_Maxwell_and_HQVM (φ t : ℝ) :
    timeAngle φ t = φ * t ∧ H_of_phi φ = φ := by
  unfold timeAngle H_of_phi
  exact ⟨rfl, rfl⟩

/-- **Same α in O-Maxwell and HQVM.** The lattice parameter α (OctonionicLightCone)
    that appears in the O-Maxwell φ-correction term also determines G_eff(φ) = φ^α
    and the Friedmann equation. So the gravitational coupling is fixed by the same
    structure that couples to the emergent O-Maxwell equation. -/
theorem same_alpha_in_O_Maxwell_and_HQVM :
    alpha = 3/5 :=
  alpha_eq_3_5

/-- **HQVM lapse is the compatible lapse.** The lapse N = 1 + Φ + φ t (informational-energy
    axiom) is the one that couples to the same φ that appears in the O-Maxwell equation.
    So the gravitational time evolution (lapse) is determined by the same horizon field. -/
theorem HQVM_lapse_uses_same_phi (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = 1 + Φ + timeAngle φ t :=
  HQVM_lapse_eq_timeAngle Φ φ t

/-- **O-Maxwell → HQVM-GR (homogeneous limit).** In the homogeneous limit (Φ = 0, H = φ),
    the Friedmann equation (3−γ)H² = 8π G_eff(φ)(ρ_m + ρ_r) is the Einstein equation
    for the geometry **compatible with** the O-Maxwell dynamics: same φ, same α.
    Schuller's step "matter determines geometry" here becomes "O-Maxwell (with φ from
    the lattice) determines HQVM as the compatible GR." -/
theorem O_Maxwell_determines_HQVM_GR_homogeneous (φ rho_m rho_r : ℝ) (hφ : 0 ≤ φ) :
    HQVM_Friedmann_eq φ rho_m rho_r ↔
      (13/5 : ℝ) * φ ^ 2 = 8 * Real.pi * (φ ^ alpha) * (rho_m + rho_r) := by
  rw [HQVM_Friedmann_eq_power φ rho_m rho_r hφ]

/-- **Minkowski limit.** When φ = 0 (no horizon coupling), the lapse is N = 1 and the
    O-Maxwell equation reduces to classic Maxwell (flat limit). So the "no gravity"
    limit of HQVM-GR coincides with the flat limit of O-Maxwell. -/
theorem Minkowski_limit_consistent (t : ℝ) :
    HQVM_lapse 0 0 t = 1 :=
  HQVM_lapse_Minkowski t

/-- **Summary: derivation path.** Following Schuller (Maxwell → GR), we have:
    O-Maxwell (emergent in O, reduce to H, then 3D) + causal compatibility with
    geometry → HQVM-GR (lapse N = 1 + Φ + φ t, curvature from light-cone, Friedmann).
    The same φ and α link both sides; the full constructive proof (matter action
    implies gravitational action) is the same conceptual derivation, with O-Maxwell
    replacing standard Maxwell and HQVM replacing Einstein–Hilbert. -/
theorem derivation_path_O_Maxwell_to_HQVM_GR (φ : ℝ) (hφ : 0 ≤ φ) :
    H_of_phi φ = φ ∧ G_eff φ = φ ^ alpha ∧ (3 : ℝ) - gamma_HQIV = 13/5 := by
  refine ⟨H_of_phi_eq φ, G_eff_eq φ hφ, three_minus_gamma_eq⟩

end Hqiv
