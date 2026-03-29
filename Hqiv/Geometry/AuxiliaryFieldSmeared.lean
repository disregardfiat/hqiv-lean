import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Mul
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic

import Hqiv.Geometry.AuxiliaryField

namespace Hqiv

open scoped BigOperators
open Finset Set

/-!
# Smeared auxiliary field along the discrete relativistic horizon

In continuum QFT, a **smeared** scalar is \(\phi(f)=\int f\,\phi\) with \(f\) a test
function—this **regularizes** pointlike \(\phi(x)\) (IR/UV control).

In HQIV the **past light-cone** is organized by integer shells \(m\in\mathbb{N}\) with
local temperature `T m` (`AuxiliaryField`). The auxiliary field at shell \(m\) is
\(\varphi(m)=\texttt{phi\_of\_shell}\,m=\texttt{phi\_of\_T}(T(m))\).

**Discrete smearing** along shells is the natural analogue:
\[
  \sum_{m\in s} w_m\,\varphi(m),
  \qquad w_m\ge 0,\ \sum_{m\in s} w_m=1,
\]
interpreted as horizon-localized averaging (a convex combination of shell values).

**Regularization lemma (Jensen):** \(\texttt{phi\_of\_T}(t)=2/t\) is **convex** on \(t>0\).
Hence the field evaluated at the **smeared temperature** is **never larger** than the
smeared field values:
\[
  \texttt{phi\_of\_T}\Bigl(\sum_m w_m T(m)\Bigr)\ \le\ \sum_m w_m\,\texttt{phi\_of\_T}(T(m))
  \ =\ \sum_m w_m\,\varphi(m).
\]
So: *first smear temperatures, then apply \(\varphi\)* (left-hand side) is dominated by
*smearing the already-lifted auxiliary field* (right-hand side). This is the precise
convex-analytic sense in which **smearing regularizes the relativistic-horizon ladder**:
multi-shell averaging of \(\varphi\) captures strictly more "response" than evaluating
\(\varphi\) at a single effective temperature, except in the degenerate one-shell case.
-/

noncomputable def smearedTemperature (w : ℕ → ℝ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s, w m * T m

noncomputable def smearedAuxField (w : ℕ → ℝ) (s : Finset ℕ) : ℝ :=
  ∑ m ∈ s, w m * phi_of_shell m

theorem smearedAuxField_eq_smeared_phiOfT (w : ℕ → ℝ) (s : Finset ℕ) :
    smearedAuxField w s = ∑ m ∈ s, w m * phi_of_T (T m) := by
  unfold smearedAuxField
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [phi_of_shell_eq_phi_of_T m]

/-- Sharp localization on a single shell: weight `1` at `m₀`, support `{m₀}`. -/
theorem smearedAuxField_dirac_shell (m₀ : ℕ) :
    smearedAuxField (fun m => if m = m₀ then (1 : ℝ) else 0) {m₀} = phi_of_shell m₀ := by
  simp [smearedAuxField]

theorem smearedTemperature_dirac_shell (m₀ : ℕ) :
    smearedTemperature (fun m => if m = m₀ then (1 : ℝ) else 0) {m₀} = T m₀ := by
  simp [smearedTemperature]

/-- `φ(t) = 2/t` as `2 · t^{-1}` on `t > 0` (for convexity on `Ioi 0`). -/
theorem phi_of_T_eq_two_mul_zpow (t : ℝ) (_ht : 0 < t) :
    phi_of_T t = 2 * t ^ (-1 : ℤ) := by
  unfold phi_of_T phiTemperatureCoeff
  rw [zpow_neg_one, inv_eq_one_div]
  ring

/-- `phi_of_T` is convex on `(0,∞)` (hence Jensen applies to temperature smearings). -/
theorem convexOn_phi_of_T : ConvexOn ℝ (Ioi (0 : ℝ)) phi_of_T := by
  refine (ConvexOn.smul (c := (2 : ℝ)) (by norm_num) (convexOn_zpow (-1 : ℤ))).congr ?_
  intro t _ht
  -- Pointwise agreement on `Ioi 0`: beta-reduce `smul` then `2/t = 2·t^{-1}`.
  simp only [phi_of_T, phiTemperatureCoeff]
  rw [smul_eq_mul, zpow_neg_one, inv_eq_one_div]
  ring

/--
**Jensen / regularization:** evaluating `phi_of_T` at the smeared temperature is bounded
above by the smeared auxiliary field (convex combination of `phi_of_shell` values).
-/
theorem phi_of_smeared_temperature_le_smeared_auxField (s : Finset ℕ) (w : ℕ → ℝ)
    (h₀ : ∀ m ∈ s, 0 ≤ w m) (h₁ : ∑ m ∈ s, w m = 1) :
    phi_of_T (∑ m ∈ s, w m * T m) ≤ ∑ m ∈ s, w m * phi_of_shell m := by
  have hmem : ∀ m ∈ s, T m ∈ Ioi (0 : ℝ) := fun m _ =>
    Set.mem_Ioi.mpr (T_pos m)
  have hj := convexOn_phi_of_T.map_sum_le h₀ h₁ hmem
  -- `map_sum_le` uses `•`; on `ℝ` this is multiplication.
  simpa [smul_eq_mul, phi_of_shell_eq_phi_of_T] using hj

end Hqiv
