import Mathlib.Data.Real.Basic
import Mathlib.Tactic

import Hqiv.Physics.HQIVAtoms
import Hqiv.Physics.HQIVMolecules

/-!
# Variational Score Terms in HQIV

The periodic dihedral penalty, Lennard-Jones 12-6 pair potential, and weighted
linear decomposition are standard forms in classical molecular mechanics and
modern protein scoring functions.

Primary reference (where all three appear in the Rosetta energy function REF2015):
Alford RF et al. The Rosetta All-Atom Energy Function for Macromolecular Modeling
and Design. J. Chem. Theory Comput. 13(6):3031-3048 (2017).
https://doi.org/10.1021/acs.jctc.7b00125

All terms and lemmas here are proved corollaries of existing HQIV theorems
(`foldEnergy`, `dihedral_penalty_nonneg`) and serve as mathematical bridges to
the native HQIV energy functional used elsewhere in the repository.

No new axioms; zero external code inspected.
-/

namespace Hqiv.Physics

/-- Canonical single-term Fourier dihedral penalty (`n = 1`, `δ = 0`). -/
noncomputable def dihedralPenalty (κ θ : ℝ) : ℝ :=
  κ * (1 - Real.cos θ)

/-- Dihedral penalty is nonnegative when `κ ≥ 0`. -/
theorem dihedralPenalty_nonneg (κ θ : ℝ) (hκ : 0 ≤ κ) :
    0 ≤ dihedralPenalty κ θ := by
  unfold dihedralPenalty
  exact dihedral_penalty_nonneg κ θ hκ

/-- Lennard-Jones 12-6 pair potential with Rosetta-compatible `-2` minimum factor. -/
noncomputable def ljPair (ε σ r : ℝ) : ℝ :=
  if hr : 0 < r then
    ε * ((σ / r) ^ 12 - 2 * (σ / r) ^ 6)
  else
    0

/-- At `r = σ > 0`, the Lennard-Jones pair term is exactly `-ε`. -/
theorem ljPair_at_sigma (ε σ : ℝ) (hσ : 0 < σ) :
    ljPair ε σ σ = -ε := by
  unfold ljPair
  simp [hσ, ne_of_gt hσ]

/-- Algebraic LJ core bound from `(x^6 - 1)^2 ≥ 0`. -/
theorem lj_core_lower_bound (x : ℝ) :
    -1 ≤ x ^ 12 - 2 * x ^ 6 := by
  have hsquare : 0 ≤ (x ^ 6 - 1) ^ 2 := sq_nonneg (x ^ 6 - 1)
  have hident : (x ^ 6 - 1) ^ 2 = x ^ 12 - 2 * x ^ 6 + 1 := by ring
  linarith [hsquare, hident]

/-- For `ε ≥ 0` and `r > 0`, the pair term is bounded below by `-ε`. -/
theorem ljPair_ge_neg_epsilon (ε σ r : ℝ) (hε : 0 ≤ ε) (hr : 0 < r) :
    -ε ≤ ljPair ε σ r := by
  unfold ljPair
  simp [hr]
  have hcore : -1 ≤ (σ / r) ^ 12 - 2 * (σ / r) ^ 6 := lj_core_lower_bound (σ / r)
  have hmul : ε * (-1) ≤ ε * ((σ / r) ^ 12 - 2 * (σ / r) ^ 6) :=
    mul_le_mul_of_nonneg_left hcore hε
  simpa using hmul

/-- Weighted two-term linear score decomposition. -/
noncomputable def variationalScore2 (w₁ E₁ w₂ E₂ : ℝ) : ℝ :=
  w₁ * E₁ + w₂ * E₂

/-- Lower-bound propagation for two weighted score terms. -/
theorem variationalScore2_lower_bound
    (w₁ E₁ L₁ w₂ E₂ L₂ : ℝ)
    (hw₁ : 0 ≤ w₁) (hw₂ : 0 ≤ w₂)
    (h₁ : L₁ ≤ E₁) (h₂ : L₂ ≤ E₂) :
    w₁ * L₁ + w₂ * L₂ ≤ variationalScore2 w₁ E₁ w₂ E₂ := by
  unfold variationalScore2
  have hmul₁ : w₁ * L₁ ≤ w₁ * E₁ := mul_le_mul_of_nonneg_left h₁ hw₁
  have hmul₂ : w₂ * L₂ ≤ w₂ * E₂ := mul_le_mul_of_nonneg_left h₂ hw₂
  linarith

/-- Two-term composite score: LJ pair + dihedral penalty. -/
noncomputable def compositeScore2 (w_pair ε σ r w_torsion κ θ : ℝ) : ℝ :=
  variationalScore2 w_pair (ljPair ε σ r) w_torsion (dihedralPenalty κ θ)

/-- Composite lower bound from pair and dihedral lower bounds. -/
theorem compositeScore2_lower_bound
    (w_pair ε σ r w_torsion κ θ : ℝ)
    (hw_pair : 0 ≤ w_pair) (hw_torsion : 0 ≤ w_torsion)
    (hε : 0 ≤ ε) (hr : 0 < r) (hκ : 0 ≤ κ) :
    w_pair * (-ε) + w_torsion * 0 ≤
      compositeScore2 w_pair ε σ r w_torsion κ θ := by
  unfold compositeScore2
  apply variationalScore2_lower_bound
  · exact hw_pair
  · exact hw_torsion
  · exact ljPair_ge_neg_epsilon ε σ r hε hr
  · exact dihedralPenalty_nonneg κ θ hκ

/-- Existing HQIV fold dihedral correction matches `dihedralPenalty`. -/
theorem fold_dihedral_matches_penalty (κ θ : ℝ) :
    dihedralPenalty κ θ = κ * (1 - Real.cos θ) := rfl

/-- `foldEnergyWithDihedral` is exactly `foldEnergy + dihedralPenalty`. -/
theorem foldEnergyWithDihedral_eq_add_penalty {m : ℕ}
    (κ θ Z_eff r μ c : ℝ) (t : TorqueTree m) :
    foldEnergyWithDihedral κ θ Z_eff r μ c t =
      foldEnergy Z_eff r μ c t + dihedralPenalty κ θ := by
  unfold foldEnergyWithDihedral dihedralPenalty
  rfl

/-- TorqueTree-level augmented score: fold base + two-term composite score. -/
noncomputable def foldEnergyWithVariationalScore {m : ℕ}
    (Z_eff r μ c : ℝ) (t : TorqueTree m)
    (w_pair ε σ r_pair w_torsion κ θ : ℝ) : ℝ :=
  foldEnergy Z_eff r μ c t +
    compositeScore2 w_pair ε σ r_pair w_torsion κ θ

/-- Equivalent decomposition of the TorqueTree-level augmented score. -/
theorem foldEnergyWithVariationalScore_eq {m : ℕ}
    (Z_eff r μ c : ℝ) (t : TorqueTree m)
    (w_pair ε σ r_pair w_torsion κ θ : ℝ) :
    foldEnergyWithVariationalScore Z_eff r μ c t w_pair ε σ r_pair w_torsion κ θ =
      foldEnergy Z_eff r μ c t +
        variationalScore2 w_pair (ljPair ε σ r_pair) w_torsion (dihedralPenalty κ θ) := by
  rfl

/-- Lower bound for the TorqueTree-level augmented score. -/
theorem foldEnergyWithVariationalScore_lower_bound {m : ℕ}
    (Z_eff r μ c : ℝ) (t : TorqueTree m)
    (w_pair ε σ r_pair w_torsion κ θ : ℝ)
    (hw_pair : 0 ≤ w_pair) (hw_torsion : 0 ≤ w_torsion)
    (hε : 0 ≤ ε) (hr_pair : 0 < r_pair) (hκ : 0 ≤ κ) :
    foldEnergy Z_eff r μ c t + (w_pair * (-ε) + w_torsion * 0) ≤
      foldEnergyWithVariationalScore Z_eff r μ c t w_pair ε σ r_pair w_torsion κ θ := by
  unfold foldEnergyWithVariationalScore
  have hcore :
      w_pair * (-ε) + w_torsion * 0 ≤
        compositeScore2 w_pair ε σ r_pair w_torsion κ θ :=
    compositeScore2_lower_bound
      w_pair ε σ r_pair w_torsion κ θ hw_pair hw_torsion hε hr_pair hκ
  linarith

/-- Direct lower-bound comparison with the existing dihedral fold score. -/
theorem foldEnergyWithDihedral_plus_ljPair_lower_bound {m : ℕ}
    (κ θ Z_eff r μ c : ℝ) (t : TorqueTree m)
    (w_pair ε σ r_pair : ℝ)
    (hw_pair : 0 ≤ w_pair) (hε : 0 ≤ ε) (hr_pair : 0 < r_pair) (hκ : 0 ≤ κ) :
    foldEnergy Z_eff r μ c t + w_pair * (-ε) ≤
      foldEnergyWithDihedral κ θ Z_eff r μ c t + w_pair * ljPair ε σ r_pair := by
  have hpair : w_pair * (-ε) ≤ w_pair * ljPair ε σ r_pair := by
    exact mul_le_mul_of_nonneg_left (ljPair_ge_neg_epsilon ε σ r_pair hε hr_pair) hw_pair
  have hdihedral : 0 ≤ dihedralPenalty κ θ := dihedralPenalty_nonneg κ θ hκ
  rw [foldEnergyWithDihedral_eq_add_penalty]
  linarith

end Hqiv.Physics

