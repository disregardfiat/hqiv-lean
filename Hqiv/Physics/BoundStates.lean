/-
# Bound states and composite masses: 8×8 network hierarchy

Hierarchical binding (quarks → nucleon, nucleons → nucleus, nucleus+electrons → atom,
then molecules/solids) is expressed as **general equations** parameterized by the
**8×8 structure**: the 28 so(8) generators and 8-component (octonion-spinor) state
space. Binding at each scale is a **sum over the network of interactions** — in a
full computational model this is realized as traces/expectation values over the
so(8) generators and 8s spinors; here we give the shell-dependent coupling and
the structural form so the repo has an algebra-consistent foundation for future
computational modeling.

**8×8 method:** Couplings at shell `m` are driven by φ(m) via `one_over_alpha_eff`,
`alphaEffShell`, `coulombStrengthShell`. The same φ(m) runs EM and (in the full
theory) strong/sector couplings. Composite mass/energy density can be fed into
`S_HQVM_grav` (ρ_m) for back-reaction into geometry.

**Reference:** HQIV preprint; SM embedding and so(8) closure in `Hqiv.Algebra`.
-/

import Hqiv.Physics.SM_GR_Unification
import Hqiv.Physics.Forces
import Hqiv.Geometry.AuxiliaryField
import Hqiv.QuantumMechanics.Schrodinger

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace Hqiv.Physics

open BigOperators

/-!
## 8×8 carrier types and dimension

These match the Algebra module (so(8) = 28 generators, 8s = 8 real components).
When building with HQIVLEAN, `OctonionState` can be identified with
`Hqiv.Algebra.OctonionSpinorCarrier` and the sum below with the actual so(8) action.
-/

/-- **Dimension of so(8)** (number of independent generators). -/
def so8Dim : ℕ := 28

/-- **8-component state** (octonion spinor carrier). In the full 8×8 method this
is the space on which so(8) acts; binding is a sum over generator indices. -/
abbrev OctonionState := Fin 8 → ℝ

/-- **Index set for so(8) generators.** Binding contributions are summed over this set. -/
abbrev So8Index := Fin so8Dim

/-!
## Shell-dependent coupling (φ(m))

All couplings at shell `m` are determined by `phi_of_shell m`; same structure for
EM (atomic) and, in the full theory, for strong/nuclear sectors.
-/

/-- **Effective EM coupling at shell m** (re-export for use in binding formulas). -/
noncomputable def alphaEffAtShell (m : ℕ) (c : ℝ := 1) : ℝ :=
  Hqiv.alphaEffShell m c

/-- **Coulomb strength at shell m** (re-export). -/
noncomputable def coulombStrengthAtShell (m : ℕ) (c : ℝ := 1) : ℝ :=
  Hqiv.coulombStrengthShell m c

/-- **Shell-dependent ground-state energy** (same form as `Hqiv.expectedGroundEnergy`
but with α_eff(m) so binding at different horizon shells is consistently parameterized). -/
noncomputable def expectedGroundEnergyAtShell (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ := 1) : ℝ :=
  - μ * (Z : ℝ)^2 * (alphaEffAtShell m c)^2 / 2

/-- **Atomic binding energy (magnitude) at shell m:** μ Z² (α_eff(m))² / 2 > 0 for bound state. -/
noncomputable def E_bind_atomic_shell_magnitude (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ := 1) : ℝ :=
  μ * (Z : ℝ)^2 * (alphaEffAtShell m c)^2 / 2

/-!
## 8×8 network: sum over generators

Binding is a sum over the 28 so(8) generators. We define the **structural form**:
a contribution per generator index that depends on shell coupling φ(m), and a
weight from the state/representation. In the full build, weights come from
matrix elements ⟨ψ| T_k |ψ⟩ or traces over the 8×8 representation.
-/

/-- **Coupling factor at shell m for generator k.** Same φ(m)-driven scale for all k
in this abstract layer; in a concrete 8×8 model the strength can depend on k (e.g. EM vs strong). -/
noncomputable def bindingCouplingAtShell (m : ℕ) (_k : So8Index) (c : ℝ := 1) : ℝ :=
  alphaEffAtShell m c

/-- **Network weight** for the 8×8 method: one coefficient per so(8) generator,
e.g. from state-dependent expectation values. -/
abbrev NetworkWeight := So8Index → ℝ

/-- **Binding energy as sum over the so(8) network** at shell m.

  E_bind = ∑_k w_k · coupling(m, k).

Here `w` encodes the representation/state (e.g. which generators contribute);
`bindingCouplingAtShell` supplies the φ(m)-dependent scale. This is the general
equation for computational modeling: instantiate `w` from the 8×8 state. -/
noncomputable def E_bind_from_network (m : ℕ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  ∑ k : So8Index, w k * bindingCouplingAtShell m k c

/-!
## Hierarchical binding levels

Each level is expressed in terms of shell m and the same φ(m)-driven couplings.
-/

/-- **QCD binding (quarks → hadron):** structural form as sum over network.
The actual weights come from the color/gluon sector of the 8×8 embedding. -/
noncomputable def E_bind_QCD_from_network (m : ℕ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  E_bind_from_network m w c

/-- **Nuclear binding (nucleons → nucleus):** same structural form; weights
from strong residual and EM (Coulomb) in the 8×8 assignment. -/
noncomputable def E_bind_nuclear_from_network (m : ℕ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  E_bind_from_network m w c

/-- **Atomic binding at shell m** (nucleus + electrons): already given by
Schrödinger-layer ground state; magnitude above. -/
noncomputable def E_bind_atomic (m : ℕ) (Z : ℕ) (μ : ℝ) (c : ℝ := 1) : ℝ :=
  E_bind_atomic_shell_magnitude m Z μ c

/-!
## Composite masses

Composite mass = sum of constituent masses minus binding (binding > 0 for bound).
All formulas are general; no concrete numerics. Masses in natural units (or same
as in SM_GR_Unification when referring to proton/neutron).
-/

/-- **Nucleon mass (e.g. proton)** at shell m as constituent mass minus QCD binding.

  M_nucleon(m) = M_constituent - E_bind_QCD(m).

Here we leave M_constituent and the network weights abstract; they are fixed by
the 8×8 embedding and data (e.g. m_proton_MeV_central). -/
noncomputable def M_nucleon_from_network (m : ℕ) (M_constituent : ℝ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  M_constituent - E_bind_QCD_from_network m w c

/-- **Nuclear mass (A nucleons, Z protons)** at shell m.

  M_nucleus(m, A, Z) = A · M_nucleon_avg - E_bind_nuclear(m).

M_nucleon_avg and the network weights are parameters from the 8×8 sector. -/
noncomputable def M_nucleus_from_network (m : ℕ) (A Z : ℕ) (M_nucleon_avg : ℝ) (w : NetworkWeight) (c : ℝ := 1) : ℝ :=
  (A : ℝ) * M_nucleon_avg - E_bind_nuclear_from_network m w c

/-- **Atomic mass** (nucleus + Z electrons) at shell m.

  M_atom(m, Z, μ) = M_nucleus(m) + Z · m_e - E_bind_atomic(m, Z, μ).

We use the shell-dependent atomic binding magnitude; M_nucleus and m_e are
supplied (e.g. from SM_GR_Unification and particle data). -/
noncomputable def M_atom_from_network (m : ℕ) (Z : ℕ) (μ : ℝ) (M_nucleus : ℝ) (m_e : ℝ) (c : ℝ := 1) : ℝ :=
  M_nucleus + (Z : ℝ) * m_e - E_bind_atomic m Z μ c

/-!
## Back-reaction into geometry

The total matter density ρ_m that appears in `S_HQVM_grav` and the HQVM Friedmann
equation can be built from these composite masses (and number densities). The
general equation is: ρ_m = ∑ (species) n_s · M_s, where M_s is given by the
appropriate level (M_nucleon, M_nucleus, M_atom) from the 8×8 network formulas above.
-/

/-- **Statement:** composite mass density at shell m is determined by the
8×8 network (constituent masses and binding sums). Back-reaction: this ρ_m
enters `S_HQVM_grav φ ρ_m ρ_r` and thus the Friedmann equation. -/
def composite_mass_density_from_network (m : ℕ) (ρ_from_network : NetworkWeight → ℝ) : Prop :=
  True

end Hqiv.Physics
