import Mathlib.Data.Real.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.Module.Pi

/-!
# Octonion spinor carrier (8s) — dependency-light alias

Real 8-vectors `Fin 8 → ℝ` model the 8s spinor carrier. This module is intentionally **minimal**
(no `So8CoordMatrix`, no Lie closure) so that consumers such as `Hqiv.Physics.SpinStatistics`
can discharge spin–statistics without pulling the heavy SO(8) generator closure.

The Standard Model embedding layer (`Hqiv.Algebra.SMEmbedding`) imports the same carrier and
adds so(8) action, SU(2)_L, hypercharge, etc.
-/

namespace Hqiv.Algebra

/-- **Carrier of the 8s representation:** ℝ⁸ as the space of real octonion spinors. -/
abbrev OctonionSpinorCarrier := Fin 8 → ℝ

instance : AddCommGroup OctonionSpinorCarrier := Pi.addCommGroup
instance : Module ℝ OctonionSpinorCarrier := Pi.module _ _ _

/-- **Basis index set for 8s has cardinality 8.** -/
theorem octonionSpinorCarrier_dim : Fintype.card (Fin 8) = 8 := Fintype.card_fin 8

end Hqiv.Algebra
