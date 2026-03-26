/-
Discrete entanglement bookkeeping on the HQIV ladder: shell-index **difference rationals** proxy
pairwise tangles; CKW/monogamy and φ-augmented inequalities reuse
`Hqiv.QuantumMechanics.MonogamyTangles` / `MonogamyTanglesPhiConditions`.
-/

import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Hqiv.QuantumMechanics.MonogamyTangles
import Hqiv.QuantumMechanics.MonogamyTanglesPhiConditions
import Hqiv.QuantumComputing.DiscreteQuantumState

namespace Hqiv.QuantumComputing

/-- Rational pairwise tangle proxy from shell separation (digital, no square roots). -/
def discTangle (m n : ℕ) : ℚ :=
  (|(m : ℤ) - n| : ℚ) / (1 + (m : ℚ) + n)

@[simp] theorem discTangle_self (m : ℕ) : discTangle m m = 0 := by
  simp [discTangle]

theorem discTangle_nonneg (m n : ℕ) : 0 ≤ discTangle m n := by
  unfold discTangle
  refine div_nonneg ?_ (le_of_lt (by positivity : 0 < 1 + (m : ℚ) + n))
  norm_cast
  exact abs_nonneg _

theorem discTangle_symm (m n : ℕ) : discTangle m n = discTangle n m := by
  unfold discTangle
  congr 1
  · have hℤ : |(m : ℤ) - n| = |(n : ℤ) - m| := by
      rw [show (n : ℤ) - m = -((m : ℤ) - n) by ring]
      rw [abs_neg]
    exact_mod_cast hℤ
  · ring

/-- Concurrence-style square on the rational proxy. -/
def discConcurrenceSq (m n : ℕ) : ℚ :=
  discTangle m n ^ 2

theorem discConcurrenceSq_nonneg (m n : ℕ) : 0 ≤ discConcurrenceSq m n := by
  unfold discConcurrenceSq
  exact sq_nonneg _

/-- Lift: standard CKW implies φ-augmented HQIV CKW at any shell. -/
theorem disc_phi_ckw_of_ckw (m : ℕ) {τAB τAC τA_BC : ℝ}
    (hckw : Hqiv.QM.ckwMonogamy τAB τAC τA_BC) :
    Hqiv.QM.correctedCkwMonogamyPhi m τAB τAC τA_BC :=
  Hqiv.QM.corrected_monogamy_of_ckw_phi m hckw

#print discTangle
#print disc_phi_ckw_of_ckw

#check discTangle_nonneg
#check discConcurrenceSq_nonneg
#check disc_phi_ckw_of_ckw
#check discTangle_symm

end Hqiv.QuantumComputing
