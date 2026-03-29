import Mathlib.Data.Sigma.Basic
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.QuantumComputing.DigitalGates
import Hqiv.QuantumComputing.DiscreteQuantumState
import Hqiv.QuantumComputing.OSHoracle

namespace Hqiv.QuantumComputing

open Hqiv

/-- `HarmonicIndex L` is a `Σ`-type over `Fin`; needed for `phaseGate` (`DecidableEq`). -/
instance (L : ℕ) : DecidableEq (HarmonicIndex L) := by
  unfold HarmonicIndex
  infer_instance

/-!
# HQIV-native gate choice for OSHoracle (sparse, fast path)

This module **commits an algorithm** (not a parameter): which `HQIVGate L` to apply in
`applyGateSparse` before pruning.

**Pivot rule (HQIV data only):**

* Cutoff `L` matches the chain length (one digital shell index per residue site).
* Aggregate horizon shells along the chain: `shells.foldl (· + ·) 0`.
* Add the discrete **`referenceM`** anchor from `OctonionicLightCone` (same object as SM/baryon
  stories) and reduce mod `(L + 1)` to select **`ℓ` ∈ Fin (L+1)`** on the angular ladder.
* Use azimuthal index **`m = 0`** in `Fin (2ℓ+1)` — minimal representative; deterministic and cheap.

**Gate:** `phaseGate` on that `HarmonicIndex L` — π phase on one angular slot, **exact** preservation
of `discreteIp` / `discreteNormSq` (`HQIVGate`).

**Sparse pipeline:** unchanged OSHoracle flow — `causalExpandSupport` → dense gate → sparse map;
length **2 × support** (`applyGateSparse_length_eq_two_mul`).

Downstream Python should pass `shells` parallel to the sparse register sites (same convention as
`Hqiv.ProteinResearch.sparseRegisterOfShells`).
-/

variable {L : ℕ}

/-- Map an integer pivot to a canonical `HarmonicIndex L`: `ℓ = pivot mod (L+1)`, `m = 0`. -/
def hqivHarmonicPivot (L pivot : ℕ) : HarmonicIndex L :=
  let ℓ : Fin (L + 1) :=
    ⟨pivot % (L + 1), Nat.mod_lt _ (Nat.succ_pos L)⟩
  have hm : 0 < 2 * ℓ.val + 1 := by
    omega
  ⟨ℓ, ⟨0, hm⟩⟩

theorem hqivHarmonicPivot_ell_val (L pivot : ℕ) :
    (hqivHarmonicPivot L pivot).fst.val = pivot % (L + 1) := by
  rfl

/-- HQIV pivot: Σ shells + `referenceM` (mod `L+1`). Proof slot enforces `|shells| = L` (chain match). -/
def hqivPivotFromShells (L : ℕ) (shells : List ℕ) (_ : shells.length = L) : ℕ :=
  let s := shells.foldl (· + ·) 0
  (s + referenceM) % (L + 1)

theorem hqivPivotFromShells_lt (L : ℕ) (shells : List ℕ) (hl : shells.length = L) :
    hqivPivotFromShells L shells hl < L + 1 := by
  unfold hqivPivotFromShells
  exact Nat.mod_lt _ (Nat.succ_pos L)

/-- The π-phase gate on the pivot slot: **the** HQIV-native digital gate for this layer. -/
def hqivNativePhaseGate (L : ℕ) (shells : List ℕ) (hl : shells.length = L) : HQIVGate L :=
  phaseGate (hqivHarmonicPivot L (hqivPivotFromShells L shells hl))

/-- Sparse OSHoracle step using `hqivNativePhaseGate` (same cost model as any `HQIVGate`). -/
noncomputable def hqivNativeOracleSparseStep (L : ℕ) (shells : List ℕ) (hl : shells.length = L)
    (r : SparseRegister L) : SparseRegister L :=
  applyGateSparse (hqivNativePhaseGate L shells hl) r

theorem hqivNativeOracleSparseStep_length (L : ℕ) (shells : List ℕ) (hl : shells.length = L)
    (r : SparseRegister L) :
    (hqivNativeOracleSparseStep L shells hl r).length = 2 * r.length :=
  applyGateSparse_length_eq_two_mul _ _

theorem hqivNativePhaseGate_preserves_normSq (L : ℕ) (shells : List ℕ) (hl : shells.length = L)
    (f : DiscreteState L) :
    discreteNormSq ((hqivNativePhaseGate L shells hl).toEquiv f) = discreteNormSq f :=
  HQIVGate.preserves_normSq (hqivNativePhaseGate L shells hl) f

/-- Same shell list yields the same gate (Python/Lean reproducibility). -/
theorem hqivNativePhaseGate_congr_shells
    (L : ℕ) (shells₁ shells₂ : List ℕ) (h₁ : shells₁.length = L) (h₂ : shells₂.length = L)
    (hs : shells₁ = shells₂) :
    hqivNativePhaseGate L shells₁ h₁ = hqivNativePhaseGate L shells₂ h₂ := by
  subst hs
  simp [hqivNativePhaseGate]

#print hqivHarmonicPivot
#print hqivPivotFromShells
#print hqivNativePhaseGate
#print hqivNativeOracleSparseStep

end Hqiv.QuantumComputing
