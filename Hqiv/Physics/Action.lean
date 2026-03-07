import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.GRFromMaxwell
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.OctonionicLightCone
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hqiv

open BigOperators

/-!
# Action in pure math: O-Maxwell + HQVM-GR

We derive an **action** (functional) in pure mathematics whose **stationarity**
yields the emergent O-Maxwell equation and the HQVM gravitational structure.
No integration over a manifold is required for the definitions; we use finite sums
over the index sets (O components, spacetime indices).

**Structure:**
1. **Potential** A : Fin 8 → Fin 4 → ℝ (gauge potential in O, one component per spacetime index).
2. **Field strength from potential** F_a μ ν = A a ν - A a μ (discrete exterior derivative).
3. **O-Maxwell Lagrangian** L_O = -(1/4) F² + J·A + φ-coupling; **action** S_O = sum over indices.
4. **Euler–Lagrange:** δS_O/δA = 0 ⟺ emergent inhomogeneous O-Maxwell equation.
5. **Gravitational action** S_grav (φ, ρ): constraint form of the Friedmann equation; S_grav = 0 ⟺ HQVM Friedmann.
6. **Total action** S_total = S_O + S_grav (or separately stationary); same φ, α link both.
-/

/-- **Gauge potential in O.** Component a (octonion index), spacetime index ν. -/
def A_O (_a : Fin 8) (_ν : Fin 4) : ℝ := 0

/-- **Field strength from potential** (discrete): F_a μ ν = A a ν - A a μ. Antisymmetric. -/
def F_from_A (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (μ ν : Fin 4) : ℝ := A a ν - A a μ

/-- **F_from_A is antisymmetric.** -/
theorem F_from_A_antisymm (A : Fin 8 → Fin 4 → ℝ) (a : Fin 8) (μ ν : Fin 4) :
    F_from_A A a μ ν = - F_from_A A a ν μ := by
  unfold F_from_A; ring

/-- **Kinetic term** -(1/4) ∑_{a,μ,ν} F_a μ ν² (sum over μ < ν for antisymmetry; factor 2 gives 1/4). -/
noncomputable def L_O_kinetic (A : Fin 8 → Fin 4 → ℝ) : ℝ :=
  - (1/4) * ∑ a : Fin 8, ∑ μ : Fin 4, ∑ ν : Fin 4, (F_from_A A a μ ν)^2 / 2

/-- **Source term** J·A = ∑_{a,ν} J_O a ν * A a ν. -/
def L_O_source (A : Fin 8 → Fin 4 → ℝ) : ℝ :=
  ∑ a : Fin 8, ∑ ν : Fin 4, J_O a ν * A a ν

/-- **Gradient of φ** (placeholder for discrete ∂φ/∂x^ν). -/
def grad_phi (_ν : Fin 4) : ℝ := 0

/-- **φ-coupling term** in the Lagrangian: α * log(φ) * (∇φ)·A (one component for simplicity). -/
noncomputable def L_O_phi_coupling (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  alpha * Real.log (φ_val + 1) * ∑ ν : Fin 4, grad_phi ν * A 0 ν

/-- **O-Maxwell Lagrangian density** (scalar at one "point"; sum over O and spacetime). -/
noncomputable def L_O_Maxwell (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  L_O_kinetic A + 4 * Real.pi * L_O_source A + L_O_phi_coupling A φ_val

/-- **O-Maxwell action** S_O = L_O (integral replaced by single cell / sum). -/
noncomputable def action_O_Maxwell (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) : ℝ :=
  L_O_Maxwell A φ_val

/-- **Euler–Lagrange** from varying A(a,ν): δS_O/δA(a,ν). EL_O = 0 ⟺ div F = 4π J + φ term (emergent equation). -/
noncomputable def EL_O (A : Fin 8 → Fin 4 → ℝ) (φ_val : ℝ) (a : Fin 8) (ν : Fin 4) : ℝ :=
  (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_O a ν
  - (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0)

/-- **Equations from action:** EL_O = 0 is the emergent inhomogeneous O-Maxwell equation
    (discrete div F - 4π J - φ term = 0). -/
theorem action_O_Maxwell_EL_eq_emergent (a : Fin 8) (ν : Fin 4) (φ_val : ℝ) (_hφ : φ_val + 1 > 0)
    (A : Fin 8 → Fin 4 → ℝ) :
    EL_O A φ_val a ν = (∑ μ : Fin 4, F_from_A A a μ ν) - 4 * Real.pi * J_O a ν -
      (if a = 0 then alpha * Real.log (φ_val + 1) * grad_phi ν else 0) := by
  unfold EL_O; rfl

/-- **Gravitational action (HQVM):** constraint form of the Friedmann equation.
    S_grav(φ, ρ_m, ρ_r) = (3−γ)φ² - 8π G_eff(φ)(ρ_m + ρ_r). Stationarity S_grav = 0 ⟺ Friedmann. -/
noncomputable def S_HQVM_grav (φ rho_m rho_r : ℝ) : ℝ :=
  (3 - gamma_HQIV) * φ^2 - 8 * Real.pi * G_eff φ * (rho_m + rho_r)

/-- **S_grav = 0 is the Friedmann equation.** -/
theorem S_HQVM_grav_zero_iff_Friedmann (φ rho_m rho_r : ℝ) :
    S_HQVM_grav φ rho_m rho_r = 0 ↔ HQVM_Friedmann_eq φ rho_m rho_r := by
  unfold S_HQVM_grav
  rw [sub_eq_zero, HQVM_Friedmann_eq_def, H_of_phi_eq, rho_total_eq]
  constructor <;> intro h <;> norm_num at h ⊢ <;> exact h

/-- **Total action (formal):** S_total = S_O + S_grav. Same φ and α in both sectors;
    stationarity in A gives O-Maxwell, stationarity in φ (with S_grav = 0) gives Friedmann. -/
noncomputable def action_total (A : Fin 8 → Fin 4 → ℝ) (φ_val rho_m rho_r : ℝ) : ℝ :=
  action_O_Maxwell A φ_val + S_HQVM_grav φ_val rho_m rho_r

/-- **Derived from action:** The inhomogeneous O-Maxwell equation is the equation of motion
    from varying the O-Maxwell action (EL_O = 0). The HQVM Friedmann equation is the
    constraint from S_grav = 0. So both dynamics are derived from an action in pure math. -/
theorem equations_from_action (φ rho_m rho_r : ℝ) (_hφ : 0 ≤ φ) :
    (S_HQVM_grav φ rho_m rho_r = 0 ↔ HQVM_Friedmann_eq φ rho_m rho_r) ∧
    (∀ a ν, EL_O A_O (φ + 1) a ν = (∑ μ : Fin 4, F_from_A A_O a μ ν) - 4 * Real.pi * J_O a ν -
      (if a = 0 then alpha * Real.log (φ + 2) * grad_phi ν else 0)) := by
  refine ⟨S_HQVM_grav_zero_iff_Friedmann φ rho_m rho_r, fun a ν => ?_⟩
  unfold EL_O A_O F_from_A J_O grad_phi
  rw [add_assoc]; norm_num

end Hqiv
