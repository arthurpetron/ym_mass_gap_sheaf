/-
M3i -- BF4/Faraut exact-rate handoff from a geometric normalized-loss bound.

`BF4FarautExactLossPersistence` deliberately accepts a general constructive
summability certificate.  The geometric adapter proved in
`GeometricMassNormalizedLossPersistence` makes that input concrete: a local
pointwise bound

  rateLoss k <= C * (1/2)^k

and the explicit anchor inequality `2*C < mass 0` construct the persistence
witness automatically.  This file wires that result to the producer's same
exact physical separator and its independent renormalized heat-kernel ceiling.

The local bound, the anchor inequality, the BF4 same-object producer, and the
renormalized comparison remain analytic inputs.  No continuum or Clay claim is
made.
-/

import YMGap.Continuum.BF4FarautExactLossPersistence
import YMGap.Continuum.GeometricMassNormalizedLossPersistence

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.ExactLogMassNormalizedLossPersistence
open YMGap.Continuum.GeometricMassNormalizedLossPersistence
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

namespace BF4FarautExactLossFlow

/-- The geometric pointwise estimate and anchor inequality construct the
general persistence witness consumed by the exact-log handoff. -/
def geometricPersistence
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0) :
    MassNormalizedLossPersistence flow.rationalFlow :=
  control.persistence anchorDominates

@[simp] theorem geometricPersistence_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0) :
    (flow.geometricPersistence control anchorDominates).floorWitness =
      flow.rationalFlow.mass 0 + -geoTail control.coefficient 0 := rfl

theorem geometricPersistence_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0) :
    (0 : Q') <
      (flow.geometricPersistence control anchorDominates).floorWitness :=
  control.persistent_floor_pos anchorDominates

/-- A geometric normalized-loss estimate supplies the exact lower floor on
the producer's own logarithmic physical-rate family. -/
def uniformExactFloorOfGeometricLoss
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  flow.uniformExactFloor
    (flow.geometricPersistence control anchorDominates)

@[simp] theorem uniformExactFloorOfGeometricLoss_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0) :
    (flow.uniformExactFloorOfGeometricLoss control anchorDominates).floor =
      flow.rationalFlow.mass 0 + -geoTail control.coefficient 0 := rfl

/-- **Geometric-loss same-object hybrid.**  The pointwise geometric loss bound
constructs the exact lower floor, while the renormalized BF4/HK route supplies
the exact upper ceiling on the definitionally identical rate family. -/
def fullRangeExactCertificateOfGeometricLossRenormalizedHK
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  flow.fullRangeExactCertificateOfLossRenormalizedHK
    (flow.geometricPersistence control anchorDominates)
    C trajectory comparison bare

@[simp] theorem fullRangeExactCertificateOfGeometricLossRenormalizedHK_separator
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfGeometricLossRenormalizedHK
      control anchorDominates C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfGeometricLossRenormalizedHK_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfGeometricLossRenormalizedHK
      control anchorDominates C trajectory comparison bare).uniformFloor.floor =
        flow.rationalFlow.mass 0 + -geoTail control.coefficient 0 := rfl

theorem fullRangeExactCertificateOfGeometricLossRenormalizedHK_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : GeometricRateLossControl flow.rationalFlow)
    (anchorDominates :
      geoTail control.coefficient 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : Q') <
      (flow.fullRangeExactCertificateOfGeometricLossRenormalizedHK
        control anchorDominates C trajectory comparison bare).uniformFloor.floor :=
  control.persistent_floor_pos anchorDominates

end BF4FarautExactLossFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.geometricPersistence
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.uniformExactFloorOfGeometricLoss
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfGeometricLossRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfGeometricLossRenormalizedHK_floor_pos
