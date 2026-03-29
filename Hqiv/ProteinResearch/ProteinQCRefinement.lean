import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Hqiv.ProteinResearch.AtomEnergyOSHoracleBridge
import Hqiv.ProteinResearch.ProteinFoldingQuantumChemistry
import Hqiv.ProteinResearch.ProteinHKEMinimizer

/-!
# Post–Cα quantum-chemistry refinement (HQIV-native energy + proved descent)

This formalizes the **same algorithm shape** as a Python “final step” after Cα / OSH folding:

* **Fixed shells** `Fin n → ℕ` (from the horizon ladder; see `latticeFullModeEnergy` in
  `AtomEnergyOSHoracleBridge` / `ProteinFoldingQuantumChemistry`).
* **Geometry** `Fin n → Coord3` (heavy-atom or Cα sites — same ℝ³ chart as `ProteinHKEMinimizer`).
* **Soft clash** on unordered pairs `i < j`: if inter-site distance `< σ`, penalty `(σ - d)²`; else `0`.
* **Total** `E = E_site(shell) + w * E_clash(pos)` with `w ≥ 0`.

The **site block** does not depend on coordinates in this layer (shells chosen outside the inner
refinement loop); clash is what the gradient step acts on first-order.  Python computes true
∇E numerically; Lean proves the **linearized** descent properties of a **per-site steepest** step
`-step * grad` matching that usage.

No `sorry`, no new `axiom`.
-/

namespace Hqiv.ProteinResearch

open scoped BigOperators
open Finset
open Hqiv
open Hqiv.QM

variable {n : ℕ}

/-- HQIV site-only term: sum of `latticeFullModeEnergy` (independent of `pos` here). -/
noncomputable def qcSiteEnergy (shell : Fin n → ℕ) : ℝ :=
  Finset.sum Finset.univ fun i : Fin n => latticeFullModeEnergy (shell i)

theorem qcSiteEnergy_nonneg (shell : Fin n → ℕ) : 0 ≤ qcSiteEnergy shell := by
  unfold qcSiteEnergy
  exact Finset.sum_nonneg fun _ _ => latticeFullModeEnergy_nonneg _

/-- Soft quadratic penalty when distance is below threshold `σ` (else 0). -/
noncomputable def softRepulsionFromDist (d σ : ℝ) : ℝ :=
  if d < σ then (σ - d) ^ 2 else 0

theorem softRepulsionFromDist_nonneg (d σ : ℝ) : 0 ≤ softRepulsionFromDist d σ := by
  unfold softRepulsionFromDist
  split_ifs with h
  · nlinarith [sq_nonneg (σ - d)]
  · linarith

/-- Unordered pairs `(i,j)` with `i < j` for finite-site clash sums. -/
def pairFinsetLt (n : ℕ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter fun p : Fin n × Fin n => p.1 < p.2

/-- Sum of soft clash penalties over all distinct site pairs. -/
noncomputable def qcSoftClashEnergy (pos : Fin n → Coord3) (σ : ℝ) : ℝ :=
  Finset.sum (pairFinsetLt n) fun p =>
    softRepulsionFromDist (distanceTerm (pos p.1) (pos p.2)) σ

theorem qcSoftClashEnergy_nonneg (pos : Fin n → Coord3) (σ : ℝ) : 0 ≤ qcSoftClashEnergy pos σ := by
  unfold qcSoftClashEnergy
  refine Finset.sum_nonneg fun p hp => ?_
  exact softRepulsionFromDist_nonneg _ _

/-- **Total QC refinement objective** (implementation reference: post–Cα polish in Python). -/
noncomputable def qcRefinementEnergy (shell : Fin n → ℕ) (pos : Fin n → Coord3) (σ w : ℝ) : ℝ :=
  qcSiteEnergy shell + w * qcSoftClashEnergy pos σ

theorem qcRefinementEnergy_nonneg (shell : Fin n → ℕ) (pos : Fin n → Coord3) (σ : ℝ) {w : ℝ}
    (hw : 0 ≤ w) : 0 ≤ qcRefinementEnergy shell pos σ w := by
  unfold qcRefinementEnergy
  exact add_nonneg (qcSiteEnergy_nonneg shell) (mul_nonneg hw (qcSoftClashEnergy_nonneg pos σ))

/-!
## Gradient-step algebra (per-site steepest descent, “don’t blow up” = small nonnegative step)

Matching `ProteinNaturalFolding.localDescentDisp` / `linearizedDelta`, but with one **field**
`Fin n → Coord3` of partial gradients (e.g. ∂E/∂xᵢ for each site).
-/

/-- Per-site displacement `-step * grad i`. -/
def qcGradientStepDisp (grad : Fin n → Coord3) (step : ℝ) : Fin n → Coord3 :=
  fun i => smul3 (-step) (grad i)

theorem qc_per_site_linearized_descent (grad : Fin n → Coord3) (step : ℝ) (hstep : 0 ≤ step)
    (i : Fin n) : dot3 (grad i) (qcGradientStepDisp grad step i) ≤ 0 := by
  unfold qcGradientStepDisp dot3 smul3
  nlinarith [sq_nonneg (grad i 0), sq_nonneg (grad i 1), sq_nonneg (grad i 2), hstep]

/-- Sum of per-site first-order proxies `⟨∇ᵢE, δxᵢ⟩` along a displacement field. -/
noncomputable def linearizedQcProxy (grad disp : Fin n → Coord3) : ℝ :=
  Finset.sum Finset.univ fun i : Fin n => dot3 (grad i) (disp i)

theorem linearizedQcProxy_gradient_step_nonpos (grad : Fin n → Coord3) (step : ℝ) (hstep : 0 ≤ step) :
    linearizedQcProxy grad (qcGradientStepDisp grad step) ≤ 0 := by
  unfold linearizedQcProxy qcGradientStepDisp
  refine Finset.sum_nonpos ?_
  intro i _
  exact qc_per_site_linearized_descent grad step hstep i

/-- Trust-region style bound: step stays below a user ceiling (Python `step_max`). -/
structure QcRefinementTrust where
  stepMax : ℝ

theorem step_bounded {t : QcRefinementTrust} {step : ℝ} (h : step ≤ t.stepMax) : step ≤ t.stepMax :=
  h

end Hqiv.ProteinResearch
