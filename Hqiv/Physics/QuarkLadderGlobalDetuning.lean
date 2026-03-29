import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.QuarkMetaResonance

/-!
# Quark internal ladders with δ-corrected geometric steps

Shell triples and anchors follow `QuarkMetaResonance`. For a scalar `δ`, the step
`geometricResonanceStepCorrected δ m_heavy m_light` matches `geometricResonanceStep` when
`δ = 0` (`GlobalDetuning.geometricResonanceStepCorrected_zero`).

**No PDG closure:** same caveat as the lepton obstruction module.
-/

namespace Hqiv.Physics

open scoped Real

noncomputable section

/-! Up-type: top → charm → up -/

noncomputable def resonanceKInternalUpCorrected (δ : ℝ) (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ => geometricResonanceStepCorrected δ m_quark_up_top_shell m_quark_up_charm_shell
  | ⟨1, _⟩ => geometricResonanceStepCorrected δ m_quark_up_charm_shell m_quark_up_light_shell

theorem resonanceKInternalUpCorrected_zero (step : Fin 2) :
    resonanceKInternalUpCorrected 0 step = resonanceK_internal step := by
  fin_cases step <;> simp [resonanceKInternalUpCorrected, resonanceK_internal,
    geometricResonanceStepCorrected_zero]

/-! Down-type: bottom → strange → down -/

noncomputable def resonanceKInternalDownCorrected (δ : ℝ) (step : Fin 2) : ℝ :=
  match step with
  | ⟨0, _⟩ =>
      geometricResonanceStepCorrected δ m_quark_down_bottom_shell m_quark_down_strange_shell
  | ⟨1, _⟩ =>
      geometricResonanceStepCorrected δ m_quark_down_strange_shell m_quark_down_light_shell

theorem resonanceKInternalDownCorrected_zero (step : Fin 2) :
    resonanceKInternalDownCorrected 0 step = resonanceK_internal_down step := by
  fin_cases step <;> simp [resonanceKInternalDownCorrected, resonanceK_internal_down,
    geometricResonanceStepCorrected_zero]

/-! Unified surfaces at quark shells (same `GlobalDetuningHypothesis` as leptons). -/

noncomputable def effUnifiedUpTop (h : GlobalDetuningHypothesis) : ℝ :=
  effUnified h m_quark_up_top_shell

noncomputable def effUnifiedDownBottom (h : GlobalDetuningHypothesis) : ℝ :=
  effUnified h m_quark_down_bottom_shell

end

end Hqiv.Physics
