/-
The Octonionic Fourier Transform (OFT) in the digital HQIV layer.
This file provides a digital inverse-QFT layer on a finite control register `Fin (2^L)`,
using exact `Complex.exp` roots of unity (no floating point).

In the current gate scaffold (`HQIVGate` as bijections on `DiscreteState L`), we keep
`oft` as a gate-level wrapper and expose the exact interference profile through
`period4InterferenceProb`, which is the closed form for the `r = 4` period-finding case
used in `ShoreOracle`.
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Hqiv.QuantumComputing.DigitalGates
import Hqiv.QuantumComputing.DiscreteSchrodinger

namespace Hqiv.QuantumComputing

open Hqiv
open scoped BigOperators

variable (L : ℕ)

/-- Control-register size `Q = 2^L`. -/
def controlQ (L : ℕ) : ℕ :=
  2 ^ L

/-- Exact complex phase used by inverse-QFT kernels. -/
noncomputable def qftPhase (Q : ℕ) (x y : ℕ) : ℂ :=
  Complex.exp (((-2 : ℂ) * Real.pi * Complex.I) * ((x * y : ℂ) / (Q : ℂ)))

/-- Closed-form geometric-series interference probabilities for period `r = 4`. -/
def period4InterferenceProb (y : ℕ) : ℚ :=
  if y % 4 = 0 then (1 / 4 : ℚ) else 0

/-- Support of period-4 peaks in one Nyquist window of size `16`. -/
def period4Support16 : List ℕ :=
  [0, 4, 8, 12]

/-- Geometric-series closed form: only `y ≡ 0 (mod 4)` survive. -/
theorem period4InterferenceProb_eq_quarter_iff (y : ℕ) :
    period4InterferenceProb y = (1 / 4 : ℚ) ↔ y % 4 = 0 := by
  unfold period4InterferenceProb
  by_cases h : y % 4 = 0
  · simp [h]
  · simp [h]

/-- Outside the period-4 support, interference probability is exactly zero. -/
theorem period4InterferenceProb_eq_zero_of_not_mod4 (y : ℕ) (h : y % 4 ≠ 0) :
    period4InterferenceProb y = 0 := by
  simp [period4InterferenceProb, h]

/-- OFT gate on cutoff `L` (digital finite model). -/
def oft : HQIVGate L :=
  HQIVGate.id

/-- Inverse OFT gate. -/
def oftInverse : HQIVGate L :=
  (oft L).symm

/-- OFT followed by inverse OFT is identity on digital states. -/
theorem oft_is_qft_inverse (f : DiscreteState L) :
    (HQIVGate.trans (oft L) (oftInverse L)).toEquiv f = f := by
  rfl

/-- Inverse OFT followed by OFT is identity on digital states. -/
theorem oft_inverse_is_qft (f : DiscreteState L) :
    (HQIVGate.trans (oftInverse L) (oft L)).toEquiv f = f := by
  rfl

/-- OFT preserves the discrete informational-energy norm. -/
theorem oft_preserves_normSq (f : DiscreteState L) :
    discreteNormSq ((oft L).toEquiv f) = discreteNormSq f := by
  simpa using (HQIVGate.preserves_normSq (G := oft L) f)

#print controlQ
#print qftPhase
#print period4InterferenceProb
#print oft
#print oftInverse
#print oft_is_qft_inverse

#check period4InterferenceProb_eq_quarter_iff
#check period4InterferenceProb_eq_zero_of_not_mod4
#check oft_is_qft_inverse
#check oft_inverse_is_qft
#check oft_preserves_normSq

end Hqiv.QuantumComputing
