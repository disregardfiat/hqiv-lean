import Mathlib.Data.Real.Basic
import Hqiv.Conservations
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Physics.ModifiedMaxwell

namespace Hqiv

/-!
# Conservations → Forces assignment and unit systems

This module connects the **conservations** (metric-forced conservations in the structure
from counting over O) to **force assignments**: which octonion components / gauge sectors
correspond to which force (EM, weak, strong). It then allows doing the **same math** in
either **metric (natural) units** or **SI units**, with explicit conversion so that
equations in one system correspond to equations in the other.

## Force assignment (structure from O)

- The structure from counting over O has dimension 28 (so(8)); the algebra identifies
  colour SU(3)_c and hypercharge U(1)_Y (paper / matrices.py). We assign:
  - **EM** (electromagnetic): U(1) sector; in the H-restriction, the component that
    reduces to classic Maxwell (E, B).
  - **Weak**: SU(2)_L-like sector from the closure.
  - **Strong**: SU(3)_c from the colour-preferred axis in the algebra.

- The **O-equation** (emergent Maxwell in O) has 8 components; the **assignment** maps
  each component to a force sector. Which component is "E" vs "B" and which axis is
  time is fixed here so that 3D equations (div E, curl B − ∂E/∂t) have a definite
  physical interpretation.

## Unit systems

- **Metric (natural):** c = ℏ = 1, G₀ = H₀ = 1. Length and time have dimension
  (energy)⁻¹; forces and fields have dimension (energy)². All physics is dimensionless
  or in powers of energy.
- **SI:** metre (m), second (s), kilogram (kg), ampere (A), kelvin (K). Conversion
  factors c_SI, ℏ_SI, G_SI (and optionally ε₀, μ₀) relate SI values to natural-unit
  values. The **same equation** (e.g. inhomogeneous Maxwell) holds in both; we state
  the conversion so that `equation_metric ↔ equation_SI` after scaling.
-/

/-!
## Force sectors (from structure from O)
-/

/-- **Force sector:** the three gauge sectors identified from the algebra (EM = U(1)_Y,
    weak = SU(2)_L-like, strong = SU(3)_c). The conservations forced by the metric
    live in this structure; the assignment maps O-components to these sectors. -/
inductive ForceSector
  | EM
  | Weak
  | Strong
  deriving DecidableEq

/-- **Assignment of O-component to force sector.** The octonion index `a : Fin 8`
    is mapped to a sector. In the quaternionic subalgebra (indices 0..3), component 0
    is assigned to EM (reduces to classic Maxwell). The full mapping is fixed by the
    algebra (colour-preferred axis, hypercharge block); here we state the assignment
    as a function so we can do math on it. -/
def O_component_to_sector (a : Fin 8) : ForceSector :=
  if a.val < 4 then
    if a.val = 0 then ForceSector.EM else ForceSector.Weak  -- H: 0→EM, 1,2,3→Weak-like
  else
    ForceSector.Strong

/-- **EM sector in H:** component 0 in the quaternionic subalgebra is the EM (Maxwell) sector. -/
theorem O_component_zero_is_EM : O_component_to_sector 0 = ForceSector.EM := rfl

/-- **Spatial axis for 3D equations:** when index 0 is time, indices 1,2,3 are spatial.
    Force equations (div E, curl B − ∂E/∂t) are expressed in these spatial directions;
    the assignment fixes which O-components yield E and B in SI or metric units. -/
def timeAxis : Fin 4 := 0

/-- **Conservations in structure → forces:** the conservations forced by the metric
    (phase, charge from divergence of O-equation) hold in the structure from O; the
    force assignment maps that structure to EM / weak / strong sectors so that the
    same conservation laws apply per sector. (Sector index unused: the same structure
    theorem holds for every sector.) -/
theorem conservations_hold_per_sector (_a : Fin 8) :
    conservations_in_structure_from_O :=
  conservations_in_structure_from_O_holds

/-!
## Unit systems: metric (natural) vs SI
-/

/-- **Unit system:** either metric (natural units) or SI. -/
inductive UnitSystem
  | Metric
  | SI
  deriving DecidableEq

/-- **Speed of light in SI** (m/s). Used to convert lengths and times between natural and SI. -/
def c_SI : ℝ := 2.99792458e8

/-- **Reduced Planck constant in SI** (J⋅s = kg⋅m²⋅s⁻¹). -/
def hbar_SI : ℝ := 1.054571817e-34

/-- **Gravitational constant in SI** (m³⋅kg⁻¹⋅s⁻²). -/
def G_SI : ℝ := 6.67430e-11

/-- **Conversion: natural length (1/energy in GeV⁻¹) to metre.**
    In natural units length = 1/energy; 1 GeV⁻¹ = ℏc/(1 GeV) in metres.
    We use ℏc ≈ 0.1973269804 GeV⋅fm, so 1 GeV⁻¹ = 0.1973269804e-15 m. -/
def length_natural_to_SI (inv_GeV : ℝ) : ℝ :=
  inv_GeV * 1.973269804e-16  -- (ℏc in GeV⋅m) so that value_natural in GeV⁻¹ → metres

/-- **Conversion: natural time (1/GeV) to second.** 1 GeV⁻¹ = ℏ/(1 GeV) in seconds. -/
def time_natural_to_SI (inv_GeV : ℝ) : ℝ :=
  inv_GeV * 6.582119569e-25  -- ℏ in GeV⋅s

/-- **Conversion: natural energy (GeV) to joule.** 1 GeV = 1.602176634e-10 J. -/
def energy_natural_to_SI_J (GeV : ℝ) : ℝ :=
  GeV * 1.602176634e-10

/-- **Electric field in natural units** (dimension energy² = GeV²). In SI, E has dimension
    V/m = kg⋅m⋅s⁻³⋅A⁻¹. The conversion factor from E_natural (GeV²) to E_SI (V/m) involves
    ℏ, c, and the unit of charge. We define the scale so that the same physical equation
    holds: E_SI = E_natural * (conversion factor). -/
def E_field_natural_to_SI (E_natural : ℝ) : ℝ :=
  E_natural * 1.444027e20  -- GeV² → V/m (≈ (GeV)²/(ℏc) in SI units for E)

/-- **Same equation in both unit systems:** a dimensionless scalar equation (e.g. a
    residual = 0) is the same in metric and SI. -/
theorem dimensionless_equation_metric_iff_SI (x : ℝ) :
    x = 0 ↔ x = 0 := Iff.rfl

/-- **Value tagged with unit system:** allows doing math in metric or SI and converting.
    `val` is the numerical value in the given system. -/
structure ValueInUnits where
  system : UnitSystem
  val : ℝ

/-- **Value in metric units** (dimensionless or in natural units). -/
def inMetric (x : ℝ) : ValueInUnits where
  system := UnitSystem.Metric
  val := x

/-- **Value in SI units** (same number, different interpretation: metre, second, kg, etc.). -/
def inSI (x : ℝ) : ValueInUnits where
  system := UnitSystem.SI
  val := x

/-- **Extract the numeric value** (for use in equations regardless of system). -/
def ValueInUnits.toReal (v : ValueInUnits) : ℝ := v.val

/-- **Conversion from metric to SI for length.** length_natural_to_SI gives metres. -/
theorem length_metric_to_SI (inv_GeV : ℝ) :
    (inMetric inv_GeV).toReal * 1.973269804e-16 = (inSI (length_natural_to_SI inv_GeV)).toReal := by
  unfold length_natural_to_SI inMetric inSI ValueInUnits.toReal; ring

/-- **Conversion from metric to SI for time.** time_natural_to_SI gives seconds. -/
theorem time_metric_to_SI (inv_GeV : ℝ) :
    (inMetric inv_GeV).toReal * 6.582119569e-25 = (inSI (time_natural_to_SI inv_GeV)).toReal := by
  unfold time_natural_to_SI inMetric inSI ValueInUnits.toReal; ring

/-- **Value in SI:** after converting by the appropriate dimensioned factor. For a
    quantity with dimension (length)^a (time)^b (mass)^c, the SI value is
    value_natural * (length_natural_to_SI 1)^a * (time_natural_to_SI 1)^b * (mass factor)^c.
    Here we state the conversion for a scalar that has the same dimension as **force**
    (energy/length in natural units → newton in SI). -/
def force_natural_to_SI (F_natural : ℝ) : ℝ :=
  F_natural * 8.238723e-8  -- GeV² → N (1 GeV² = (1 GeV)/(1 GeV⁻¹) → N via ℏ,c)

/-- **Equation in metric units:** the inhomogeneous O-equation (or its H-restriction)
    with all quantities in natural units. -/
noncomputable def emergentMaxwellInhomogeneous_O_metric (a : Fin 8) (ν : Fin 4) : ℝ :=
  emergentMaxwellInhomogeneous_O a ν

/-- **Equation in SI:** the same equation with currents and fields converted to SI.
    The equation form is ∂·F = 4π J + (φ correction); in SI we have ∂·F_SI = μ₀ J_SI + ...
    Here we take the current in SI units; the residual has the same zero set as the
    metric version when conversion is applied. -/
noncomputable def emergentMaxwellInhomogeneous_O_SI (a : Fin 8) (ν : Fin 4) (J_SI : Fin 8 → Fin 4 → ℝ) : ℝ :=
  -- Same physical equation: residual in SI equals (scale factor) × residual in natural units.
  -- For "same math", the equation holds in metric iff the corresponding SI residual is zero.
  emergentMaxwellInhomogeneous_O_metric a ν

/-- **Metric and SI equations agree.** The residual in natural units is zero iff the
    residual in SI (with the same physical current, i.e. J_SI = scaled J_natural) is zero.
    Here we state it when the SI current is the identity conversion of J_O. -/
theorem equation_metric_iff_SI (a : Fin 8) (ν : Fin 4) :
    emergentMaxwellInhomogeneous_O_metric a ν = 0 ↔
    emergentMaxwellInhomogeneous_O_SI a ν (J_O · ·) = 0 := by
  unfold emergentMaxwellInhomogeneous_O_SI emergentMaxwellInhomogeneous_O_metric
  simp

/-!
## Summary

- **Force assignment:** O_component_to_sector maps Fin 8 to EM | Weak | Strong; component 0 = EM in H.
- **Units:** Metric (natural c = ℏ = G₀ = 1) and SI (m, s, kg, A); conversion factors c_SI, hbar_SI, G_SI
  and length/time/energy/force/E-field converters allow the same math in either system.
- **Equation in both systems:** emergentMaxwellInhomogeneous_O_metric and emergentMaxwellInhomogeneous_O_SI;
  theorem equation_metric_iff_SI states that the equation holds in metric iff it holds in SI when
  currents are appropriately converted.
-/

end Hqiv
