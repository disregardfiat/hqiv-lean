import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

import Hqiv.Geometry.HQVMetric

namespace Hqiv

open scoped Topology

/-!
# Real analyticity of the ADM / HQVM lapse

The informational-energy axiom fixes `HQVM_lapse Φ φ t = 1 + Φ + φ * t` (`HQVMetric`). As a polynomial
in three real variables, the lapse is **real analytic on all of** `ℝ × ℝ × ℝ`.

When the auxiliary field is tied to the temperature ladder via `phi_of_T Θ = phiTemperatureCoeff / Θ`
(`AuxiliaryField`), the composed lapse
`1 + Φ + phi_of_T Θ * t` is analytic on the open set where `Θ ≠ 0` (same domain as `T(m) = 1/(m+1)` is
positive on shells).

This does not add axioms: it is Mathlib’s `AnalyticAt` API applied to definitions already in the repo.

**Design note (observer-centric vs GR perturbations):** analyticity supports a *local* Taylor /
linear-response story for the lapse and composed `phi_of_T` factors. It is **not** a substitute for
deriving the full linearized Einstein system; see `HQVMPerturbations` for the intentional scope
(lapse and temperature ladder only).
-/

/-- Package `(Φ, φ, t)` as `ℝ × (ℝ × ℝ)` so projections match `HQVM_lapse` arguments. -/
noncomputable def HQVM_lapseTuple (p : ℝ × ℝ × ℝ) : ℝ :=
  HQVM_lapse p.1 p.2.1 p.2.2

theorem HQVM_lapse_eq_tuple (Φ φ t : ℝ) :
    HQVM_lapse Φ φ t = HQVM_lapseTuple (Φ, φ, t) := rfl

/-- **ADM lapse as a joint function of `(Φ, φ, t)` is real analytic everywhere.** -/
theorem analyticAt_HQVM_lapseTuple (z : ℝ × ℝ × ℝ) :
    AnalyticAt ℝ HQVM_lapseTuple z := by
  unfold HQVM_lapseTuple HQVM_lapse
  have hΦ : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) z := analyticAt_fst
  have hφ : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) z := analyticAt_fst.comp analyticAt_snd
  have ht : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) z := analyticAt_snd.comp analyticAt_snd
  simpa [add_assoc] using (analyticAt_const.add hΦ).add (hφ.mul ht)

theorem analyticOnNhd_HQVM_lapseTuple : AnalyticOnNhd ℝ HQVM_lapseTuple Set.univ :=
  fun _ _ => analyticAt_HQVM_lapseTuple _

/-- `phi_of_T` is analytic at every nonzero temperature (rational function `2 / Θ`). -/
theorem analyticAt_phi_of_T {Θ : ℝ} (hΘ : Θ ≠ 0) : AnalyticAt ℝ phi_of_T Θ := by
  unfold phi_of_T
  simpa [div_eq_mul_inv] using
    (analyticAt_const (v := phiTemperatureCoeff)).mul (analyticAt_id.inv hΘ)

/-- Lapse with `φ = phi_of_T Θ` (continuous temperature ladder), as a function of `(Φ, Θ, t)`. -/
noncomputable def HQVM_lapse_phiT (p : ℝ × ℝ × ℝ) : ℝ :=
  HQVM_lapse p.1 (phi_of_T p.2.1) p.2.2

theorem HQVM_lapse_phiT_eq (Φ Θ t : ℝ) :
    HQVM_lapse Φ (phi_of_T Θ) t = HQVM_lapse_phiT (Φ, Θ, t) := rfl

/-- **Analyticity away from `Θ = 0`:** same joint domain on which `phi_of_T` is defined as a smooth
rational function; shell temperatures `T m = 1/(m+1)` lie in this domain. -/
theorem analyticAt_HQVM_lapse_phiT (z : ℝ × ℝ × ℝ) (hΘ : z.2.1 ≠ 0) :
    AnalyticAt ℝ HQVM_lapse_phiT z := by
  unfold HQVM_lapse_phiT HQVM_lapse
  have hΦ : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.1) z := analyticAt_fst
  have hprojΘ : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.1) z := analyticAt_fst.comp analyticAt_snd
  have hphi : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => phi_of_T p.2.1) z :=
    AnalyticAt.comp (analyticAt_phi_of_T hΘ) hprojΘ
  have ht : AnalyticAt ℝ (fun p : ℝ × ℝ × ℝ => p.2.2) z := analyticAt_snd.comp analyticAt_snd
  simpa [add_assoc] using (analyticAt_const.add hΦ).add (hphi.mul ht)

theorem analyticOnNhd_HQVM_lapse_phiT :
    AnalyticOnNhd ℝ HQVM_lapse_phiT {p : ℝ × ℝ × ℝ | p.2.1 ≠ 0} := fun _ hp =>
  analyticAt_HQVM_lapse_phiT _ hp

end Hqiv
