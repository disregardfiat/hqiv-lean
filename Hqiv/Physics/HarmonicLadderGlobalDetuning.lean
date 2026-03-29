import Hqiv.Physics.GlobalDetuning
import Hqiv.Geometry.AuxiliaryField

/-!
# Harmonic ladder and global detuning (same shell index `m`)

The **temperature / auxiliary-field ladder** (`phi_of_shell m`, `shell_shape m`) uses the same
discrete shell index `m` as the **detuned surface** story. `effUnified h m` applies the global
shift `λ·obs` in the Rindler denominator at that shell — parallel to `LeptonResonanceGlobalDetuning`
and `QuarkLadderGlobalDetuning`, without mixing the O–Maxwell `alphaEffAtShell` construction
(which lives in `SM_GR_Unification` / `BoundStates`).

**Identification:** optional packaging via `GlobalDetuningHypothesis.fromLapseScalars` is in
`GlobalDetuning` (proved algebra with `HQVM_lapse`).
-/

namespace Hqiv.Physics

open scoped Real

noncomputable section

/-- Same shell `m` as `phi_of_shell m` and `shell_shape m` (`AuxiliaryField`). -/
noncomputable def effUnifiedHarmonicShell (h : GlobalDetuningHypothesis) (m : ℕ) : ℝ :=
  effUnified h m

theorem effUnifiedHarmonicShell_eq (h : GlobalDetuningHypothesis) (m : ℕ) :
    effUnifiedHarmonicShell h m = shellSurface m / (1 + c_rindler_shared * (m : ℝ) + deltaM h m) :=
  effUnified_eq_shell_over_det h m

theorem phi_of_shell_same_shell_index_as_effUnified (m : ℕ) :
    phi_of_shell m = phiTemperatureCoeff * (m + 1 : ℝ) :=
  phi_of_shell_closed_form m

end

end Hqiv.Physics
