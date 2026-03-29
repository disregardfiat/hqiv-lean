import Mathlib.Algebra.Group.Pi.Basic
import Hqiv.Geometry.AuxFieldRapidityNullBridge

/-!
# 1+1 Minkowski slice inside `Fin 4 → ℝ`

`AuxFieldRapidityNullBridge` fixes indices `0` (time-like) and `1` (first spatial) for the flat
`diag(-1,1)` story. The same two axes are the natural embedding into the four-component spacetime
coordinates used by `Hqiv.Physics.Action` and `Hqiv.Physics.ModifiedMaxwell`.

**Definitions**
* `minkowskiSq4` — `−x₀² + x₁² + x₂² + x₃²` on `Fin 4 → ℝ`.
* `lift11ToFin4` — `Pi.single 0 (v 0) + Pi.single 1 (v 1)`; pads `2,3` with `0`.

**Main lemma:** `minkowskiSq4 (lift11ToFin4 v) = minkowskiSq11 v`, so null cones agree on the
embedded plane (no claim about boosts acting on all four components).
-/

namespace Hqiv.Geometry

/-- Flat Minkowski quadratic form on four HQIV spacetime components (`c = 1`). -/
noncomputable def minkowskiSq4 (x : Fin 4 → ℝ) : ℝ :=
  -(x 0) ^ 2 + (x 1) ^ 2 + (x 2) ^ 2 + (x 3) ^ 2

/-- Embed `1+1` into `(t, x¹, 0, 0)`; indices `2,3` unused. -/
def lift11ToFin4 (v : Fin 2 → ℝ) : Fin 4 → ℝ :=
  Pi.single (0 : Fin 4) (v 0) + Pi.single (1 : Fin 4) (v 1)

theorem minkowskiSq4_lift11_eq_minkowskiSq11 (v : Fin 2 → ℝ) :
    minkowskiSq4 (lift11ToFin4 v) = minkowskiSq11 v := by
  simp [minkowskiSq4, minkowskiSq11, lift11ToFin4, Pi.add_apply]

/-- Forward null `(1,1)` in `1+1` embeds to `(1,1,0,0)` with `minkowskiSq4 = 0`. -/
theorem minkowskiSq4_lift_null_forward :
    minkowskiSq4 (lift11ToFin4 (fun _ : Fin 2 => (1 : ℝ))) = 0 := by
  rw [minkowskiSq4_lift11_eq_minkowskiSq11]
  simp [minkowskiSq11]

end Hqiv.Geometry
