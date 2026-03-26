/-
Digital quantum states as pure combinatorial data on the HQIV angular-mode ladder:
no Hilbert-space axioms, only the discrete null-lattice bookkeeping (via the spherical-harmonic
degeneracy bridge in `Hqiv.Geometry.SphericalHarmonicsBridge`) and the rational shadow
`φ_rat(ℓ) = 2(ℓ+1)` of `phi_of_shell` from `Hqiv.Geometry.AuxiliaryField`.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Hqiv.Algebra.OctonionBasics
import Hqiv.Geometry.SphericalHarmonicsBridge
import Hqiv.Geometry.AuxiliaryField

namespace Hqiv.QuantumComputing

open scoped BigOperators
open Finset
open Hqiv.Algebra

/-- Rational HQIV temperature weight (shadow of `phi_of_shell m = 2(m+1)` as ℝ). -/
def phiRat (m : ℕ) : ℚ :=
  2 * ((m : ℚ) + 1)

@[simp] theorem phiRat_zero : phiRat 0 = 2 := by simp [phiRat]

/-- Matches `phi_of_shell_closed_form` after casting `ℕ → ℚ → ℝ`. -/
theorem phiRat_coe_eq_phi_of_shell (m : ℕ) :
    (phiRat m : ℝ) = phi_of_shell m := by
  simp [phiRat, phi_of_shell_closed_form, phiTemperatureCoeff]

/-- Octonionic triality order (`Hqiv.Algebra.Triality`): per-shell occupancy cap is `3`. -/
def trialityMultiplicityCap : ℕ :=
  3

/-- Computational binary sector carried by a single angular slot (lifts to triality-typed modes). -/
abbrev DiscreteQubit : Type :=
  Bool

/-- Occupancy at one shell: `0…3` quanta, bounded by triality. -/
abbrev ShellOccupancy : Type :=
  Fin 4

theorem shellOccupancy_le_triality (o : ShellOccupancy) : (o : ℕ) ≤ trialityMultiplicityCap := by
  fin_cases o <;> decide

/-- Indexed angular modes with `ℓ ≤ L`, the same bookkeeping as `Y_{ℓm}` (`2ℓ+1` per `ℓ`). -/
def HarmonicIndex (L : ℕ) : Type :=
  Σ ℓ : Fin (L + 1), Fin (2 * ℓ.val + 1)

instance (L : ℕ) : Fintype (HarmonicIndex L) :=
  Sigma.instFintype

/-- Finite configuration on shells `0…L` with triality-bounded multiplicity. -/
structure DiscreteShellConfig (L : ℕ) where
  occ : Fin (L + 1) → Fin 4

/-- Amplitudes on the `(L+1)²` angular digital basis at cutoff `L`. -/
abbrev DiscreteState (L : ℕ) : Type :=
  HarmonicIndex L → OctonionVec

private lemma sum_fin_twice_add_one (L : ℕ) :
    (∑ i : Fin (L + 1), (2 * (i : ℕ) + 1)) = (L + 1) ^ 2 := by
  have h := Fin.sum_univ_eq_sum_range (fun k => 2 * k + 1) (L + 1)
  calc
    (∑ i : Fin (L + 1), (2 * (i : ℕ) + 1)) = ∑ l ∈ range (L + 1), (2 * l + 1) := h
    _ = (L + 1) ^ 2 := sum_two_mul_add_one_range_succ_sq L

/-- **Dimension:** cardinality of the digital angular basis equals `(L+1)²`
(`Hqiv.sum_two_mul_add_one_range_succ_sq` / spherical-harmonic cumulative degeneracy). -/
theorem Fintype.card_harmonicIndex (L : ℕ) :
    Fintype.card (HarmonicIndex L) = (L + 1) ^ 2 := by
  classical
  dsimp [HarmonicIndex]
  simp_rw [Fintype.card_sigma, Fintype.card_fin]
  simpa using sum_fin_twice_add_one L

/-- Discrete informational inner product (unweighted).

We sum the octonion Euclidean inner product over all ladder basis slots.

This unweighted choice is what allows QFT-style finite transforms to be
proved unitary when they mix basis slots with different `fst` (shell) labels.
-/
def discreteIp {L : ℕ} (f g : DiscreteState L) : ℝ :=
  ∑ ij : HarmonicIndex L, octonionInner (f ij) (g ij)

def discreteNormSq {L : ℕ} (f : DiscreteState L) : ℝ :=
  discreteIp f f

/-- Nonnegativity of the informational-energy norm induced by `octonionInner`. -/
theorem discreteNormSq_nonneg {L : ℕ} (f : DiscreteState L) : 0 ≤ discreteNormSq f := by
  simp_rw [discreteNormSq, discreteIp]
  refine Finset.sum_nonneg fun ij _ => ?_
  -- `octonionInner (x) (x)` is the Euclidean sum of squares of components.
  have hsq : 0 ≤ octonionInner (f ij) (f ij) := by
    simp [octonionInner]
    refine Finset.sum_nonneg fun k _ => by
      simpa using mul_self_nonneg (f ij k)
  exact hsq

/-- Rational normalisation in the informational inner product. -/
def IsNormalized {L : ℕ} (f : DiscreteState L) : Prop :=
  discreteNormSq f = 1

#print phiRat_coe_eq_phi_of_shell
#print Fintype.card_harmonicIndex
#print discreteIp
#print discreteNormSq_nonneg

#check phiRat_coe_eq_phi_of_shell
#check Fintype.card_harmonicIndex
#check discreteIp
#check discreteNormSq_nonneg

end Hqiv.QuantumComputing
