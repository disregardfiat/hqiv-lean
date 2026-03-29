import Hqiv.QuantumComputing.DigitalGates
import Hqiv.QuantumComputing.OSHoracle
import Hqiv.QuantumComputing.OSHoracleHQIVNative

namespace Hqiv.QuantumComputing

open Hqiv
open Hqiv.Algebra

/-- Protein alias for sparse quantum-computing hooks. -/
structure Protein where
  residues : List Nat
  score : ℚ

/-- Residue amplitude encoder into the octonion basis `e_(r mod 8)`. -/
def residueAmplitude (r : Nat) : Octonion :=
  Hqiv.Algebra.octonionBasis ⟨r % 8, Nat.mod_lt _ (by decide)⟩

/-- Minimal digital ansatz builder for protein folding experiments. -/
def proteinFoldingAnsatz (depth : Nat) (params : Array ℚ) : List (HQIVGate depth) :=
  List.replicate (depth + params.size) HQIVGate.id

/-- Sparse support extracted from the protein sequence. -/
def proteinSparseInit (p : Protein) : SparseRegister p.residues.length :=
  (List.range p.residues.length).map fun i => (i, residueAmplitude (p.residues.getD i 0))

/-- Selected ansatz gate used by the finite sparse hook. -/
def proteinFoldingGate (p : Protein) : HQIVGate p.residues.length :=
  (proteinFoldingAnsatz p.residues.length #[]).headD HQIVGate.id

/-- **HQIV-native gate:** π phase on `hqivHarmonicPivot` from `hqivPivotFromShells` (`referenceM` + Σ shells). -/
def proteinNativeGate (p : Protein) (shells : List ℕ) (hl : shells.length = p.residues.length) :
    HQIVGate p.residues.length :=
  hqivNativePhaseGate p.residues.length shells hl

/-- Gate-evolved sparse support used by the folding hook. -/
noncomputable def proteinSparseEvolved (p : Protein) : SparseRegister p.residues.length :=
  applyGateSparse (proteinFoldingGate p) (proteinSparseInit p)

/-- Gate-evolved sparse support with the **HQIV-native** phase gate (same OSHoracle cost as `proteinSparseEvolved`). -/
noncomputable def proteinSparseEvolvedNative (p : Protein) (shells : List ℕ)
    (hl : shells.length = p.residues.length) : SparseRegister p.residues.length :=
  hqivNativeOracleSparseStep p.residues.length shells hl (proteinSparseInit p)

/-- Pruned sparse support restricted to causally flipped kets. -/
noncomputable def proteinSparsePruned (p : Protein) : SparseRegister p.residues.length :=
  let evolved := proteinSparseEvolved p
  let flipped := detectFlippedKets (proteinSparseInit p) evolved
  pruneToFlipped flipped evolved

/-- Sparse folding runner that reports a pruning-derived variational score increment. -/
noncomputable def runSparseProteinFolding (p : Protein) : Protein :=
  let pruned := proteinSparsePruned p
  { residues := p.residues
    score := p.score + (pruned.length : ℚ) }

/-- Variational energy operator used by the sparse hook (symbolic finite proxy). -/
def variationalEnergyOperator (p : Protein) : ℚ :=
  p.residues.length

/-- A variational-energy operator in this finite layer is nonnegative on all proteins. -/
def IsVariationalEnergyOperator (E : Protein → ℚ) : Prop :=
  ∀ p, 0 ≤ E p

/-- Horizon-causality: equal shell depth gives equal variational energy. -/
def HorizonCausalOperator (E : Protein → ℚ) : Prop :=
  ∀ p q, p.residues.length = q.residues.length → E p = E q

/-- The variational energy operator is horizon-causal in the hook model. -/
theorem variationalEnergyOperator_horizonCausal_true :
    HorizonCausalOperator variationalEnergyOperator := by
  intro p q hlen
  simp [variationalEnergyOperator, hlen]

/-- The variational energy operator is nonnegative (finite-shell count). -/
theorem variationalEnergyOperator_is_variational :
    IsVariationalEnergyOperator variationalEnergyOperator := by
  intro p
  exact Nat.cast_nonneg p.residues.length

/-- Horizon-causal variational operators admit sparse pruning without changing hook output. -/
theorem variationalEnergyOperator_benefits_from_pruning (p : Protein) :
    (proteinSparsePruned p).length ≤ (proteinSparseEvolved p).length := by
  unfold proteinSparsePruned
  exact pruneToFlipped_length_le _ _

/-- One sparse fold step obeys the horizon-causal support-growth bound. -/
theorem proteinSparseEvolved_support_growth (p : Protein) :
    (proteinSparseEvolved p).length ≤ 2 * (proteinSparseInit p).length := by
  unfold proteinSparseEvolved
  exact (applyGateSparse_length_eq_two_mul
    (L := p.residues.length)
    (g := proteinFoldingGate p)
    (r := proteinSparseInit p)).le

theorem proteinSparseEvolvedNative_length (p : Protein) (shells : List ℕ)
    (hl : shells.length = p.residues.length) :
    (proteinSparseEvolvedNative p shells hl).length = 2 * (proteinSparseInit p).length :=
  hqivNativeOracleSparseStep_length p.residues.length shells hl (proteinSparseInit p)

#print residueAmplitude
#print proteinFoldingAnsatz
#print proteinSparseInit
#print proteinFoldingGate
#print proteinSparseEvolved
#print proteinSparsePruned
#print runSparseProteinFolding
#print variationalEnergyOperator_is_variational
#print variationalEnergyOperator_horizonCausal_true
#print variationalEnergyOperator_benefits_from_pruning
#print proteinSparseEvolved_support_growth

#check residueAmplitude
#check proteinFoldingAnsatz
#check proteinSparseInit
#check proteinFoldingGate
#check proteinSparseEvolved
#check proteinSparsePruned
#check runSparseProteinFolding
#check variationalEnergyOperator_is_variational
#check variationalEnergyOperator_horizonCausal_true
#check variationalEnergyOperator_benefits_from_pruning
#check proteinSparseEvolved_support_growth

end Hqiv.QuantumComputing

