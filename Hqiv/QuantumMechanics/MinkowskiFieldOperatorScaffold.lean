import Hqiv.QuantumMechanics.HorizonFreeFieldScaffold
import Hqiv.QuantumMechanics.ContinuumManyBodyQFTScaffold

namespace Hqiv.QM

/-!
# Minkowski chart → lattice field operators

Identify **four lattice sites** with `Fin 4` (same indexing as `SpacetimeChart = Fin 4 → ℝ` in
`ContinuumManyBodyQFTScaffold`).  Given an `EventChart`, each event label carries coordinates
`chart x : Fin 4 → ℝ`; use those coordinates **as diagonal weights** in `smearedField`.

This yields **honest bounded linear operators** on `LatticeHilbert 4 = ℂ⁴`.  The algebra remains
**abelian** (product diagonal matrices), so **operator commutators vanish** — matching
`smearedField_opCommutator_eq_zero`.  Microcausality in the operator sense is therefore trivially
satisfied for any causal relation, including η-spacelike separation.

**Next extension (not done here):** replace diagonal `smearedField` by a CCR/Weyl representation
so that `[·,·]` recovers canonical equal-time / spacelike vanishing in a nontrivial way.
-/

open scoped InnerProductSpace

noncomputable section

/-- Field operator on the 4-site lattice: coordinates from the event chart act as site weights. -/
noncomputable def fieldOpFromChart (chart : EventChart) (x : EventLabel) :
    LatticeHilbert 4 →ₗ[ℂ] LatticeHilbert 4 :=
  smearedField (chart x)

theorem fieldOpFromChart_opCommutator_eq_zero (chart : EventChart) (x y : EventLabel) :
    opCommutator (fieldOpFromChart chart x) (fieldOpFromChart chart y) = 0 :=
  smearedField_opCommutator_eq_zero (chart x) (chart y)

/--
Operator-level microcausality **conditional** on η-spacelike separation — here a corollary of
abelian diagonal fields (commutator already zero, so the hypothesis is unused).
-/
theorem fieldOpFromChart_microcausal_op
    (chart : EventChart) (x y : EventLabel) (_hsp : spacelikeRelationMinkowski chart x y) :
    opCommutator (fieldOpFromChart chart x) (fieldOpFromChart chart y) = 0 :=
  fieldOpFromChart_opCommutator_eq_zero chart x y

end

end Hqiv.QM
