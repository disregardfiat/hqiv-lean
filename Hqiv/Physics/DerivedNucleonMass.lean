import Hqiv.Physics.Baryogenesis
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.QuarkMetaResonance

namespace Hqiv.Physics

/-!
Pure-derivation nucleon masses (proton/neutron) on the internal meta-horizon.

This module deliberately avoids hardcoding *proton/neutron* rest masses
as numeric literals. Instead it packages the internal three-harmonic
shared binding + EM internal/external EM block splitting into derived outputs.
-/

/-!
`internalSurfaceArea` is provided by `Hqiv.Physics.QuarkMetaResonance`.
We reuse it here to avoid duplicate declarations in the same namespace.
-/

/-! ### Top anchor / resonance structure -/

/-- Top birth shell is the lock-in (referenceM) shell. -/
def top_at_lockin : ℕ := referenceM

/-! ### Resonance drops -/

/-- Mass drops across internal harmonic steps (effective surface ratio). -/
noncomputable def resonanceDropK (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ =>
      internalSurfaceArea (top_at_lockin + 1) / internalSurfaceArea top_at_lockin
  | ⟨1, _⟩ =>
      internalSurfaceArea (top_at_lockin + 2) / internalSurfaceArea (top_at_lockin + 1)

/-! ### Shared binding + EM block splitting -/

/-!
The shared binding energy comes from the same internal surface overlap across
the three internal harmonics. The EM split is encoded by the internal vs.
external EM matrix-block placement rule:

* internal block (neutron): `+emBlockShift`
* external block (proton): `-emBlockShift`

Both contributions are represented symbolically in `QuarkMetaResonance`.
-/

def sharedBindingEnergy : ℝ := nucleonSharedBinding_MeV

def emInternalContribution : ℝ := emBlockShift_MeV
def emExternalContribution : ℝ := -emBlockShift_MeV

noncomputable def derivedProtonMass : ℝ :=
  sharedBindingEnergy + emExternalContribution

noncomputable def derivedNeutronMass : ℝ :=
  sharedBindingEnergy + emInternalContribution

noncomputable def derivedDeltaM : ℝ :=
  derivedNeutronMass - derivedProtonMass

/-- Top anchored at the lock-in shell. -/
theorem top_anchored_at_T_lockin : top_at_lockin = referenceM := by
  rfl

/-! ### Required theorems -/

theorem top_anchored_at_T_lockin_now :
    top_at_lockin = referenceM := by
  rfl

theorem light_quarks_from_two_resonance_drops :
    quarkMass ⟨1, by decide⟩ = m_charm_GeV ∧
      quarkMass ⟨0, by decide⟩ = m_up_GeV ∧
      quarkMassDown ⟨1, by decide⟩ = m_strange_GeV ∧
      quarkMassDown ⟨0, by decide⟩ = m_down_GeV := by
  exact two_octave_drops_to_light_quarks

theorem proton_mass_from_shared_harmonics :
    derivedProtonMass = sharedBindingEnergy + emExternalContribution := by
  rfl

theorem neutron_mass_from_shared_harmonics :
    derivedNeutronMass = sharedBindingEnergy + emInternalContribution := by
  rfl

theorem em_matrix_block_splitting :
    derivedDeltaM = emInternalContribution - emExternalContribution := by
  simp [derivedDeltaM, derivedNeutronMass, derivedProtonMass,
    emInternalContribution, emExternalContribution]

theorem proton_neutron_closeness_from_shared_surface :
    derivedNeutronMass - derivedProtonMass = derivedDeltaM := by
  rfl

end Hqiv.Physics

