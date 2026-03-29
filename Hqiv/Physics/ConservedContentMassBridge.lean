import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Hqiv.Physics.Baryogenesis
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.ChargedLeptonResonance
import Hqiv.Physics.GlobalDetuning
import Hqiv.Physics.QuarkMetaResonance

namespace Hqiv.Physics

open Hqiv

/-!
## Conserved quantum-number content → harmonic complexity → mass hierarchy

**Classification (SM quantum numbers that must project onto Fano triples to close the surface wave):**
- **Neutrino:** lepton number only → **1** independent triple.
- **Charged lepton:** lepton number + electric charge → **2** triples.
- **Quark:** baryon number + electric charge + colour → **3** triples.

This module proves:
1. Strict ordering of `conservedTripleCount` and of a squared **intrinsic wave complexity** proxy.
2. **`m_nu_e_derived < m_tau_from_resonance < m_top_GeV`** using only definitions already in
   `DerivedGaugeAndLeptonSector`, `ChargedLeptonResonance`, and `QuarkMetaResonance`.

Shared lock-in temperature enters neutrino masses through `T_lockin` and outer surfaces (see
`m_nu_e_derived_eq_T_lockin_outer_surfaces`); τ and top use the existing GeV witnesses in the
resonance modules. The **ordering** is therefore a proved consequence of those witnesses, not a new
mass-table input.

**Note:** Numeric agreement with PDG for every flavour is still handled by the tolerance lemmas in
`QuarkMetaResonance` / `ChargedLeptonResonance` where present; this file establishes the **global**
ν ≪ charged lepton ≪ top hierarchy from the derived ν scale and the τ/top anchors.

### Scaling ansatz (bridge to `effCorrected` + `SurfaceWaveSelfClock`)

A **minimal combined scaling** compatible with the self-clock / Mexican-hat story uses the same
`effCorrected δ m` as `GlobalDetuning` and `SurfaceWaveSelfClock.mexicanHatVeff` (inverse in `V_eff`):

`massScalingAnsatz k δ l m := k * l² * effCorrected δ m`,

with `l` the conserved-triple count (1 / 2 / 3) and **`k > 0` a single normalization** (paper /
curvature-imprint slot — **not** fixed to `δ_E` or `6⁷√3` in Lean here).

**Proved below:** strict monotonicity of this ansatz in `l` (fixed shell) and in `m` (fixed `l`, `0 ≤ δ`),
whenever denominators stay positive. This matches “larger harmonic content (`l²`) or larger shell
index ⇒ larger effective surface factor ⇒ larger mass scale” at the ansatz level.

Triality / Spin(8) automorphisms are **not** re-proved here; the narrative link “three `l` values ↔ three
representation images” belongs in `Triality` / SO(8) closure modules. This file stays physics-bridge
lightweight.
-/

/-- Sector distinguished by how many independent SM quantum numbers must close on the storing wave. -/
inductive FermionContentClass
  | neutrino
  | chargedLepton
  | quark
  deriving DecidableEq, Repr

/-- Independent Fano-plane triples required (ν:1, charged ℓ:2, quark:3). -/
def conservedTripleCount (c : FermionContentClass) : ℕ :=
  match c with
  | .neutrino => 1
  | .chargedLepton => 2
  | .quark => 3

theorem conservedTripleCount_ν_lt_ℓ :
    conservedTripleCount .neutrino < conservedTripleCount .chargedLepton := by
  decide

theorem conservedTripleCount_ℓ_lt_q :
    conservedTripleCount .chargedLepton < conservedTripleCount .quark := by
  decide

/-- Squared triple count: proxy for independent phase windings / harmonic complexity. -/
noncomputable def intrinsicWaveComplexity (c : FermionContentClass) : ℝ :=
  (conservedTripleCount c : ℝ) ^ 2

theorem intrinsicWaveComplexity_eq_sq (c : FermionContentClass) :
    intrinsicWaveComplexity c = (conservedTripleCount c : ℝ) ^ 2 :=
  rfl

theorem intrinsic_complexity_ν_lt_ℓ :
    intrinsicWaveComplexity .neutrino < intrinsicWaveComplexity .chargedLepton := by
  simp [intrinsicWaveComplexity, conservedTripleCount]

theorem intrinsic_complexity_ℓ_lt_q :
    intrinsicWaveComplexity .chargedLepton < intrinsicWaveComplexity .quark := by
  simp [intrinsicWaveComplexity, conservedTripleCount]
  norm_num

/-!
### Combined `l² × effCorrected` scaling (normalization `k` > 0)
-/

/-- Candidate neutrino shells **4…6** (flattened-valley / small-`m` narrative; not unique). -/
def neutrinoShellCandidate : Finset ℕ :=
  Finset.Icc 4 6

theorem neutrinoShellCandidate_eq : neutrinoShellCandidate = Finset.Icc 4 6 :=
  rfl

/-- `m = 5` lies in the candidate band (matches the illustrative `m_ν ≈ 5` shell in the paper note). -/
theorem referenceNeutrinoShell_mem : (5 : ℕ) ∈ neutrinoShellCandidate := by
  simp [neutrinoShellCandidate]

/-- Mass-scale ansatz: single normalization `k` times `l²` times δ-corrected surface (`GlobalDetuning`). -/
noncomputable def massScalingAnsatz (k δ : ℝ) (l m : ℕ) : ℝ :=
  k * (l : ℝ) ^ 2 * effCorrected δ m

private theorem sq_lt_sq_of_lt_of_pos {l1 l2 : ℕ} (h0 : 0 < l1) (hlt : l1 < l2) :
    (l1 : ℝ) ^ 2 < (l2 : ℝ) ^ 2 := by
  have h1 : (l1 : ℝ) < (l2 : ℝ) := Nat.cast_lt.mpr hlt
  have pos1 : 0 < (l1 : ℝ) := Nat.cast_pos.mpr h0
  have pos2 : 0 < (l2 : ℝ) := lt_trans pos1 h1
  nlinarith [h1, pos1, pos2]

/-- Larger conserved-triple count ⇒ larger ansatz at fixed `k`, `δ`, `m` (`k > 0`, `l` increasing). -/
theorem massScalingAnsatz_lt_of_lt_l {k δ : ℝ} {l1 l2 m : ℕ} (hk : 0 < k)
    (hl1 : 0 < l1) (hll : l1 < l2) (hδ : RindlerDenDeltaPos δ m) :
    massScalingAnsatz k δ l1 m < massScalingAnsatz k δ l2 m := by
  unfold massScalingAnsatz
  have heff : 0 < effCorrected δ m := effCorrected_pos δ m hδ
  have hsq := sq_lt_sq_of_lt_of_pos hl1 hll
  calc
    k * (l1 : ℝ) ^ 2 * effCorrected δ m
        = (l1 : ℝ) ^ 2 * (k * effCorrected δ m) := by ring
    _ < (l2 : ℝ) ^ 2 * (k * effCorrected δ m) := mul_lt_mul_of_pos_right hsq (mul_pos hk heff)
    _ = k * (l2 : ℝ) ^ 2 * effCorrected δ m := by ring

/-- Larger shell index ⇒ larger ansatz at fixed `k`, `l` (`k > 0`, `l > 0`, `0 ≤ δ`). -/
theorem massScalingAnsatz_lt_of_lt_m {k δ : ℝ} {l m n : ℕ} (hk : 0 < k) (hl : 0 < l)
    (hδ : 0 ≤ δ) (hmn : m < n) (_hδm : RindlerDenDeltaPos δ m) (_hδn : RindlerDenDeltaPos δ n) :
    massScalingAnsatz k δ l m < massScalingAnsatz k δ l n := by
  unfold massScalingAnsatz
  have he := effCorrected_strictMono_nat hδ hmn
  have hl2 : 0 < (l : ℝ) ^ 2 := pow_pos (Nat.cast_pos.mpr hl) 2
  have hkl : 0 < k * (l : ℝ) ^ 2 := mul_pos hk hl2
  calc
    k * (l : ℝ) ^ 2 * effCorrected δ m
        = (k * (l : ℝ) ^ 2) * effCorrected δ m := by ring
    _ < (k * (l : ℝ) ^ 2) * effCorrected δ n := mul_lt_mul_of_pos_left he hkl
    _ = k * (l : ℝ) ^ 2 * effCorrected δ n := by ring

/-!
### Observed hierarchy from existing HQIV witnesses (same units: GeV-scale ℝ)
-/

/-- **ν_e derived scale is strictly below the τ resonance anchor.** -/
theorem m_nu_e_derived_lt_m_tau_from_resonance : m_nu_e_derived < m_tau_from_resonance := by
  unfold m_nu_e_derived m_tau_from_resonance outerHorizonNeutrinoSuppression M_Z_derived
    gaugeBosonMassFromVev vacuumExpectationValue electroweakShell
    su2CouplingDerived u1CouplingDerived gammaDerived trialityOrder
  rw [T_lockin_eq_ladder, m_lockin_eq_referenceM]
  unfold referenceM qcdShell stepsFromQCDToLockin latticeStepCount
  simp [T_eq, outerHorizonSurface, alpha, mul_assoc, mul_left_comm, mul_comm]
  norm_num

/-- **τ resonance anchor is strictly below the top GeV anchor.** -/
theorem m_tau_from_resonance_lt_m_top_GeV : m_tau_from_resonance < m_top_GeV := by
  unfold m_tau_from_resonance m_top_GeV
  norm_num

/-- **Transitive hierarchy: ν_e derived < τ < top** from the three witnesses. -/
theorem observed_mass_hierarchy_ν_e_tau_top :
    m_nu_e_derived < m_tau_from_resonance ∧ m_tau_from_resonance < m_top_GeV :=
  ⟨m_nu_e_derived_lt_m_tau_from_resonance, m_tau_from_resonance_lt_m_top_GeV⟩

/-- Content-class order aligns with the strict chain of triple counts. -/
theorem content_class_order_matches_triple_counts :
    conservedTripleCount .neutrino < conservedTripleCount .chargedLepton ∧
      conservedTripleCount .chargedLepton < conservedTripleCount .quark :=
  ⟨conservedTripleCount_ν_lt_ℓ, conservedTripleCount_ℓ_lt_q⟩

end Hqiv.Physics
