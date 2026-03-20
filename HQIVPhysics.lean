-- Physics/geometry build: no generator stack (avoids GeneratorsLieClosureData stack overflow).
-- Use: lake build HQIVPhysics
import Hqiv.Geometry.OctonionicLightCone
import Hqiv.Geometry.AuxiliaryField
import Hqiv.Geometry.HQVMetric
import Hqiv.Geometry.Now
import Hqiv.Conservations
import Hqiv.Physics.Baryogenesis
import Hqiv.Physics.ModifiedMaxwell
import Hqiv.Physics.GRFromMaxwell
import Hqiv.Physics.Forces
import Hqiv.Physics.BoundStates
import Hqiv.Physics.DerivedGaugeAndLeptonSector
import Hqiv.Physics.NuclearAndAtomicSpectra
import Hqiv.QuantumMechanics.Schrodinger
