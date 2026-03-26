import Hqiv.ProteinResearch.ProteinNaturalFolding
import Hqiv.Geometry.HQVMPerturbations
import Hqiv.QuantumMechanics.UncertaintyPrinciple

namespace Hqiv.QM

open Hqiv

/-!
# Quantum exploration layer for natural folding

Classical folding updates (`naturalDisp`) can stall in poor local minima. This module
**promotes** the existing HQIV uncertainty infrastructure to a principled exploration
knob on the same `Coord3` chart as the HKE minimizer:

* **Energy–time scale:** `Hqiv.energyTimeResolutionScale ΔE = ħ/ΔE` (`HQVMPerturbations`),
  with `timeIncrementSubResolution` for clock increments (including WHIP `dt`).
* **Pauli Robertson bound:** `pauli_heisenberg_product` (`UncertaintyPrinciple`) is the
  proved finite-dimensional commutator/variance skeleton — the operational reminder that
  conjugate channels cannot both be arbitrarily sharp; algorithmically, that supports
  deliberate orthogonal-to-gradient exploration rather than pretending a single sharp
  configuration proxy is exact.

The **combined displacement** is the natural step plus a scaled exploration vector.
Lean stays deterministic: `ξ` is an arbitrary `Coord3` (e.g. from a sampler in code);
theorems state **first-order** consequences under explicit hypotheses.
-/

/-- `Coord3` from the protein stack matches the HQIV observer chart `Fin 3 → ℝ`. -/
theorem coord3_eq_observerChart : (Coord3 : Type) = Hqiv.ObserverChart :=
  rfl

/-- Exploration displacement in the same 3D chart as `naturalDisp`. -/
def quantumExploreDisp (amp : ℝ) (ξ : Coord3) : Coord3 :=
  smul3 amp ξ

/--
Amplitude `v * (ħ/ΔE)` from a dimensionless velocity-like factor `v` and energy scale `ΔE`.
Sub-resolution **time** hypotheses use `timeIncrementSubResolution` separately (e.g. on `whip.dt`).
-/
noncomputable def exploreAmp_energyTime (v ΔE : ℝ) : ℝ :=
  v * energyTimeResolutionScale ΔE

theorem exploreAmp_energyTime_nonneg {v ΔE : ℝ} (hv : 0 ≤ v) (hΔ : 0 < ΔE) :
    0 ≤ exploreAmp_energyTime v ΔE := by
  unfold exploreAmp_energyTime
  exact mul_nonneg hv (energyTimeResolutionScale_pos hΔ).le

/-- WHIP integration timestep is sub-resolution for `ΔE` in the HQIV SI convention. -/
def whipSubResolution (w : WHIP6DoF) (ΔE : ℝ) : Prop :=
  timeIncrementSubResolution w.dt ΔE

/--
Full update: natural HQIV folding displacement plus quantum exploration in `Coord3`.
-/
noncomputable def naturalDispQuantum (s : NaturalFoldState) (amp : ℝ) (ξ : Coord3) : Coord3 :=
  add3 (naturalDisp s) (quantumExploreDisp amp ξ)

theorem naturalDispQuantum_decomposes (s : NaturalFoldState) (amp : ℝ) (ξ : Coord3) :
    naturalDispQuantum s amp ξ =
      add3 (naturalDisp s) (smul3 amp ξ) := by
  rfl

theorem linearizedDelta_quantum_explore (g : Coord3) (amp : ℝ) (ξ : Coord3) :
    linearizedDelta g (quantumExploreDisp amp ξ) = amp * linearizedDelta g ξ := by
  unfold quantumExploreDisp
  exact linearizedDelta_smul_right g ξ amp

theorem naturalDispQuantum_linearized
    (s : NaturalFoldState) (amp : ℝ) (ξ : Coord3) :
    linearizedDelta s.grad (naturalDispQuantum s amp ξ) =
      linearizedDelta s.grad (naturalDisp s) + amp * linearizedDelta s.grad ξ := by
  rw [naturalDispQuantum_decomposes, linearizedDelta_add, linearizedDelta_smul_right]

/--
If exploration is first-order orthogonal to the local gradient (`dot3 grad ξ = 0`), the
exploration term does not contribute to the linearized energy proxy.
-/
theorem linearizedDelta_explore_orthogonal (g ξ : Coord3) (amp : ℝ) (h : dot3 g ξ = 0) :
    linearizedDelta g (quantumExploreDisp amp ξ) = 0 := by
  unfold quantumExploreDisp
  rw [linearizedDelta_smul_right]
  simp [linearizedDelta, h]

/--
First-order descent of `naturalDisp` is **preserved** when exploration is orthogonal to the
gradient and `amp ≥ 0` (exploration adds no linearized work along `grad`).
-/
theorem naturalQuantum_first_order_descent_orthogonal
    (s : NaturalFoldState)
    (amp : ℝ) (ξ : Coord3)
    (hstep : 0 ≤ s.stepSize)
    (hcarrier : linearizedDelta s.grad (carrierDisp s) ≤ 0)
    (horth : dot3 s.grad ξ = 0) :
    linearizedDelta s.grad (naturalDispQuantum s amp ξ) ≤ 0 := by
  rw [naturalDispQuantum_linearized]
  have hex : linearizedDelta s.grad ξ = 0 := by
    unfold linearizedDelta
    exact horth
  rw [hex, mul_zero, add_zero]
  exact natural_first_order_descent s hstep hcarrier

/--
**Non-orthogonal exploration:** if the exploration direction is not uphill to first order
(`linearizedDelta grad ξ ≤ 0`) and `amp ≥ 0`, the total linearized proxy is still not worse
than the natural step alone.
-/
theorem naturalQuantum_first_order_descent_explore_downhill
    (s : NaturalFoldState)
    (amp : ℝ) (ξ : Coord3)
    (hamp : 0 ≤ amp)
    (hex : linearizedDelta s.grad ξ ≤ 0) :
    linearizedDelta s.grad (naturalDispQuantum s amp ξ) ≤
      linearizedDelta s.grad (naturalDisp s) := by
  rw [naturalDispQuantum_linearized]
  have hterm : amp * linearizedDelta s.grad ξ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hamp hex
  linarith

/-- Pauli σₓ/σ_z Robertson product bound (unit spinor); informational twin for exploration. -/
theorem pauli_exploration_uncertainty (ψ : H) (hψ : ‖ψ‖ = 1) :
    stdDev linX ψ * stdDev linZ ψ ≥ |Complex.re (expect linY ψ)| :=
  pauli_heisenberg_product ψ hψ

end Hqiv.QM
