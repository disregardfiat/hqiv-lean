import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Hqiv.Physics.Action
import Hqiv.Physics.SchematicPlasmaCurrent

namespace Hqiv

open BigOperators Finset

/-!
# Action ↔ schematic plasma current

`Action.lean` couples an arbitrary octonion–spacetime current `J_src` to the gauge potential via
`L_O_source_general J_src` and puts the **same** `J_src` into `EL_O_general J_src` as the `-4π J`
Euler–Lagrange term—matching the slot in `emergentMaxwellInhomogeneous_O_general J_src`.

This file proves that **`J_O_plasma j₀ coord`** is a legitimate instance: the **J·A** interaction is
explicit on the EM channel `a = 0`, **linear in `j₀`**, and specializes to the vacuous current at
`j₀ = 0`.

For the same `J_src` together with a continuum φ field on `Fin 4 → ℝ`, use
`Hqiv.Physics.ContinuumOmaxwellClosure` (`action_O_Maxwell_general_coordsField`, `EL_O_general_coordsField`).
If the φ slot should use a metric-raised gradient `g^{νμ} ∂_μ φ` at the basepoint, use the `*_coordsField_metric`
names there (`action_O_Maxwell_general_coordsField_metric`, `EL_O_general_coordsField_metric`, etc.).

Covariant current divergence `∇_μ J^μ` with a position-dependent metric on the chart is in
`Hqiv.Geometry.ContinuumMetricGradient` (`coordCovariantDivergence`, and `coordCovariantDivergence_constDet`
when `g` is constant).
-/

theorem J_O_plasma_add_linear (j₁ j₂ : ℝ) (coord : Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    J_O_plasma (j₁ + j₂) coord a ν = J_O_plasma j₁ coord a ν + J_O_plasma j₂ coord a ν := by
  simp only [J_O_plasma, schematicPlasmaScalar_add]
  split_ifs <;> ring

theorem J_O_plasma_add (j₁ j₂ : ℝ) (coord : Fin 4 → ℝ) :
    J_O_plasma (j₁ + j₂) coord = fun a ν => J_O_plasma j₁ coord a ν + J_O_plasma j₂ coord a ν := by
  funext a ν
  exact J_O_plasma_add_linear j₁ j₂ coord a ν

/-- Only `a = (0 : Fin 8)` carries the plasma scalar; all other octonion indices contribute zero. -/
theorem sum_J_O_plasma_over_octonion (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (ν : Fin 4) :
    (∑ a : Fin 8, J_O_plasma j₀ coord a ν * A a ν) = schematicPlasmaScalar j₀ (coord ν) * A 0 ν := by
  refine Fintype.sum_eq_single (0 : Fin 8) ?_
  intro a ha
  have hav : a.val ≠ 0 := by
    intro h0
    apply ha
    exact Fin.ext h0
  simp [J_O_plasma, hav]

private theorem fintype_sum_sum_comm_fin8_fin4 (f : Fin 8 → Fin 4 → ℝ) :
    (∑ a : Fin 8, ∑ ν : Fin 4, f a ν) = ∑ ν : Fin 4, ∑ a : Fin 8, f a ν := by
  calc
    (∑ a : Fin 8, ∑ ν : Fin 4, f a ν) = ∑ p : Fin 8 × Fin 4, f p.1 p.2 :=
      (Fintype.sum_prod_type' (fun a ν => f a ν)).symm
    _ = ∑ ν : Fin 4, ∑ a : Fin 8, f a ν := Fintype.sum_prod_type_right' _

/-- **J·A** with the plasma current collapses to the EM (`a = 0`) leg and the Debye-weighted scalar. -/
theorem L_O_source_general_J_O_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma j₀ coord) A =
      ∑ ν : Fin 4, schematicPlasmaScalar j₀ (coord ν) * A 0 ν := by
  unfold L_O_source_general
  rw [fintype_sum_sum_comm_fin8_fin4 _]
  refine Finset.sum_congr rfl ?_
  intro ν _
  exact sum_J_O_plasma_over_octonion j₀ coord A ν

/-- Total O-Maxwell action density with plasma source (same φ channel as the default action). -/
noncomputable abbrev action_O_Maxwell_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val : ℝ) : ℝ :=
  action_O_Maxwell_general (J_O_plasma j₀ coord) A φ_val

/-- **Superposition in amplitude `j₀`:** the J·A part adds when two plasma strengths are summed. -/
theorem L_O_source_general_J_O_plasma_add (j₁ j₂ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) :
    L_O_source_general (J_O_plasma (j₁ + j₂) coord) A =
      L_O_source_general (J_O_plasma j₁ coord) A + L_O_source_general (J_O_plasma j₂ coord) A := by
  rw [J_O_plasma_add j₁ j₂ coord]
  exact L_O_source_general_add_J _ _ A

/-- Euler–Lagrange with plasma current: same algebraic `-4π J_plasma` term as in `EL_O_general`. -/
theorem EL_O_plasma_eq_emergent_shape (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (a : Fin 8) (ν : Fin 4) (hφ : φ_val + 1 > 0) :
    EL_O_general (J_O_plasma j₀ coord) A φ_val a ν =
      (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_O_plasma j₀ coord a ν -
        (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) :=
  action_O_Maxwell_EL_eq_emergent_general (J_O_plasma j₀ coord) a ν φ_val hφ A

/-- At `j₀ = 0`, plasma-sourced action and EL coincide with the default `J_O` (all zero). -/
theorem action_O_Maxwell_plasma_j₀_zero (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) :
    action_O_Maxwell_general (J_O_plasma 0 coord) A φ_val = action_O_Maxwell A φ_val := by
  rw [J_O_plasma_zero coord]
  rfl

theorem EL_O_plasma_j₀_zero (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) :
    EL_O_general (J_O_plasma 0 coord) A φ_val a ν = EL_O A φ_val a ν := by
  rw [J_O_plasma_zero coord]
  rfl

/-- **Same `-4π J` slot** as `emergentMaxwellInhomogeneous_O_general` (both definitions use `J_src a ν`). -/
theorem EL_O_general_neg_four_pi_J_eq (J_src : Fin 8 → Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ)
    (a : Fin 8) (ν : Fin 4) :
    EL_O_general J_src A φ_val a ν + 4 * Real.pi * J_src a ν =
      (∑ μ : Fin 4, F_from_A A a μ ν) -
        (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) := by
  unfold EL_O_general
  split_ifs <;> ring

theorem emergent_neg_four_pi_J_eq (J_src : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_general J_src a ν + 4 * Real.pi * J_src a ν =
      -alpha * Real.log (phi_of_T (T ν.val)) * grad_φ ν := by
  unfold emergentMaxwellInhomogeneous_O_general
  simp_rw [show (0.0 : ℝ) = (0 : ℝ) by norm_num]
  ring

noncomputable def action_total_plasma (j₀ : ℝ) (coord : Fin 4 → ℝ) (A : Fin 8 → Fin 4 → ℝ)
    (φ_val rho_m rho_r : ℝ) : ℝ :=
  action_total_general (J_O_plasma j₀ coord) A φ_val rho_m rho_r

end Hqiv
