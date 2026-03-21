import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Hqiv.Geometry.OctonionicLightCone

namespace Hqiv

open scoped BigOperators Topology
open Finset Set Filter

/-!
# Discrete ↔ continuous bridge (S² spectrum vs light-cone mode ladder)

On `S²`, eigenfunctions of `−Δ` are spherical harmonics `Y_{ℓm}` with eigenvalues
`ℓ(ℓ+1)` and degeneracy `2ℓ+1` per `ℓ`. The total number of independent modes with
`ℓ ≤ L` is `∑_{ℓ=0}^L (2ℓ+1) = (L+1)²` (proved below as `sum_two_mul_add_one_range_succ_sq`).
That is the same **angular** mode bookkeeping as Bohr–Schrödinger hydrogen (fixed `n`, sum over
`ℓ,m`), CMB acoustic peaks (cutoff in `ℓ`), and horizon multipoles in the Regge–Wheeler picture:
one discrete index `ℓ` with cumulative degeneracy `(L+1)²`.

The HQIV shell axiom packages the **stars-and-bars** count on the 3D null lattice with an
octonionic factor: `available_modes m = 4 · (m+2)(m+1)` (`available_modes_eq`), not the
per-shell increment `new_modes` (which satisfies `new_modes (m+1) = 8(m+2)` for `m+1 ≥ 1`).
So the object to compare to `(L+1)²` is **`4 × latticeSimplexCount m`**, i.e. a **quadratic**
in `m` with the **shift** `(m+2)(m+1)` versus `(m+1)²`, and an overall factor `4` from the
`8×` octonion modes per binomial cell (`available_modes_octonion`).

* **Continuum object (no new axioms):** `curvatureDensity : ℝ → ℝ` is continuous on `Ioi 0`
  (`curvatureDensity_continuousOn_Ioi`). Integer shells sample it via
  `shell_shape m = curvatureDensity (m+1)` (`shell_shape_eq_density_succ` in
  `OctonionicLightCone`).

* **Same leading growth / refinement limit:** both mode counts are `Θ(m²)`; moreover
  `available_modes m / (m+1)² → 4` as `m → ∞` (`tendsto_available_modes_div_sphericalHarmonicCumulative`),
  i.e. the discrete horizon capacity matches the spherical-harmonic cumulative degeneracy
  up to the fixed octonion factor `4` in the large-shell limit (lattice / Regge-style
  refinement).

* **64 real dof / one fermion generation (8×8):** the smallest `m` with
  `available_modes m ≥ 64` is `m = 3` (value `80`). This is a **pure capacity** statement
  on the ℝ mode count. It is **not** the τ birth index `m_tau = 274211` in
  `GenerationResonance`, which anchors the lepton ladder via scaled cumulative simplex
  volume and Planck-mass matching.

* **Curvature ladder vs harmonic series:** discrete harmonic partial sums bound the curvature
  integral (`curvature_integral_ge_harmonic`, `curvature_integral_le_harmonic_mul_log` in
  `OctonionicLightCone`). A graph Laplacian on a triangulated `S²` converging to `−Δ_{S²}`
  is not formalized here.
-/

/-- Cumulative spherical-harmonic degeneracy on `S²`: `∑_{ℓ=0}^L (2ℓ+1) = (L+1)²`. -/
theorem sum_two_mul_add_one_range_succ_sq (L : ℕ) :
    ∑ l ∈ range (L + 1), (2 * l + 1) = (L + 1) ^ 2 := by
  induction L with
  | zero =>
    rfl
  | succ L ih =>
    rw [sum_range_succ, ih]
    ring

/-- Cumulative spherical-harmonic degeneracy with cutoff `L = m` as a real scalar: `(m+1)²`. -/
noncomputable abbrev sphericalHarmonicCumulativeCount (m : ℕ) : ℝ :=
  ((m + 1 : ℝ) ^ 2)

/-- **Continuum curvature-imprint field:** `curvatureDensity` is continuous on `ℝ₊`, so each
`shell_shape m` is the value of one fixed continuous function at the sample point `m+1`. -/
theorem curvatureDensity_continuousOn_Ioi : ContinuousOn curvatureDensity (Ioi (0 : ℝ)) := by
  unfold curvatureDensity
  have hsub : (Ioi (0 : ℝ)) ⊆ ({0} : Set ℝ)ᶜ := by
    intro x hx
    simp only [mem_compl_iff, mem_singleton_iff, Set.mem_Ioi] at hx ⊢
    exact ne_of_gt hx
  have hinv : ContinuousOn (fun x : ℝ => x⁻¹) (Ioi (0 : ℝ)) :=
    (continuousOn_inv₀ (G₀ := ℝ)).mono hsub
  have hdiv : ContinuousOn (fun x : ℝ => 1 / x) (Ioi (0 : ℝ)) :=
    hinv.congr fun _x _hx => by simp [div_eq_mul_inv, one_mul]
  refine ContinuousOn.mul hdiv ?_
  refine ContinuousOn.add continuousOn_const ?_
  simpa [alpha] using
    (continuous_const.continuousOn (s := Ioi (0 : ℝ))).mul
      (Real.continuousOn_log.mono fun x hx => ne_of_gt hx)

theorem available_modes_div_sphericalHarmonicCumulative (m : ℕ) :
    available_modes m / sphericalHarmonicCumulativeCount m =
      4 * ((m + 2 : ℝ) / (m + 1 : ℝ)) := by
  unfold sphericalHarmonicCumulativeCount
  rw [available_modes_eq]
  have h : ((m + 1 : ℝ) ^ 2) ≠ 0 := by positivity
  field_simp [h]

/-- Horizon combinatorial capacity divided by the `(L+1)²` spherical-harmonic cumulative count
(with `L = m`) tends to `4` (octonionic factor). Same quadratic degeneracy class as angular
modes on `S²`; discrete ladder matches continuum counting in the refinement limit. -/
theorem tendsto_available_modes_div_sphericalHarmonicCumulative :
    Tendsto (fun m : ℕ => available_modes m / sphericalHarmonicCumulativeCount m) atTop
      (𝓝 (4 : ℝ)) := by
  have hlim : Tendsto (fun k : ℕ => ((k + 2 : ℝ) / (k + 1 : ℝ))) atTop (𝓝 (1 : ℝ)) := by
    simpa [add_comm, add_left_comm, add_assoc] using
      tendsto_add_mul_div_add_mul_atTop_nhds (a := (2 : ℝ)) (b := (1 : ℝ)) (c := (1 : ℝ))
        (d := (1 : ℝ)) (hd := by norm_num)
  simpa [mul_one] using
    (Tendsto.congr (fun m : ℕ => (available_modes_div_sphericalHarmonicCumulative m).symm)
      (Filter.Tendsto.const_mul (4 : ℝ) hlim))

/-- Mode count on `S²` up to degree `5` is `36 = 6²`. -/
theorem spherical_mode_count_upto_degree_five :
    ∑ l ∈ range 6, (2 * l + 1) = 36 := by
  rw [sum_two_mul_add_one_range_succ_sq 5]
  norm_num

/-- Cumulative **new** modes from shell `0` through `M` equals `available_modes M`. -/
theorem sum_new_modes_eq_available_modes (M : ℕ) :
    ∑ i ∈ range (M + 1), new_modes i = available_modes M := by
  induction M with
  | zero =>
    simp [new_modes_zero]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have hnm :
        new_modes (M + 1) = available_modes (M + 1) - available_modes M := by
      simp [new_modes]
    rw [hnm]
    ring

/-- `available_modes 3 = 80 ≥ 64` (8×8 matrix bookkeeping threshold). -/
theorem available_modes_three_ge_sixty_four : (64 : ℝ) ≤ available_modes 3 := by
  rw [available_modes_eq]
  norm_num

/-- Strictly below threshold at `m = 2`. -/
theorem available_modes_two_lt_sixty_four : available_modes 2 < (64 : ℝ) := by
  rw [available_modes_eq]
  norm_num

/-- Smallest shell index whose `available_modes` reaches at least `64`. -/
theorem minimal_shell_ge_sixty_four :
    (64 : ℝ) ≤ available_modes 3 ∧ available_modes 2 < (64 : ℝ) :=
  ⟨available_modes_three_ge_sixty_four, available_modes_two_lt_sixty_four⟩

end Hqiv
