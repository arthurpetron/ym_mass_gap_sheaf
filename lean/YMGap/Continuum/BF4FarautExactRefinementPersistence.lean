/-
M3d -- a same-family handoff between AF-oriented RG persistence and the
BF4/Faraut exact physical-rate band.

The M2 producer has one canonical exact logarithmic rate family.  The M3
refinement algebra can protect a rational lower certificate for that family,
while the renormalized heat-kernel comparison supplies its independent finite
upper ceiling.  This file prevents those two arguments from silently referring
to different separators or spacings.

No analytic input is constructed: the exact BF4 same-object producer, AF
trajectory, rational refinement step, summable loss budget, renormalized
comparison, and renormalized bare bound all remain explicit data.
-/

import YMGap.Continuum.BF4FarautFullLogPrefixTailCertificate
import YMGap.Continuum.ExactLogMassNormalizedRefinementPersistence

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.ExactLogMassNormalizedRefinementPersistence
open YMGap.Continuum.MassNormalizedRefinementPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogComparison

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

/-- A rational refinement flow certified below the producer's own exact
physical logarithmic rate family. -/
structure BF4FarautExactRefinementFlow
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type 1 where
  rationalFlow : MassNormalizedRefinementFlow
  spacing_identification : forall k : Nat,
    (rationalFlow.spacing k).eqv
      (producer.fullRangeRateFamily.physicalSpacing.spacing k)
  mass_certificate : forall k : Nat,
    CReal.leEv (CReal.ofQ' (rationalFlow.mass k))
      (producer.fullRangeRateFamily.rate k)

namespace BF4FarautExactRefinementFlow

/-- Forget the BF4/Faraut specialization while retaining the exact family
definitionally. -/
def toExactLogRefinementFlow
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer) :
    ExactLogMassNormalizedRefinementFlow P where
  exactRate := producer.fullRangeRateFamily
  rationalFlow := flow.rationalFlow
  spacing_identification := flow.spacing_identification
  mass_certificate := flow.mass_certificate

/-- A persistent rational flow gives a uniform exact lower floor for the very
same rate family used by the BF4/Faraut producer. -/
def uniformExactFloor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  flow.toExactLogRefinementFlow.uniformExactFloor persistence

@[simp] theorem uniformExactFloor_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow) :
    (flow.uniformExactFloor persistence).floor =
      persistence.floorWitness := rfl

theorem uniformExactFloor_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow) :
    (0 : Q') < (flow.uniformExactFloor persistence).floor :=
  persistence.floorWitness_pos

/-- **Hybrid exact physical-rate band on one object.**  The persistent
refinement flow supplies the lower floor.  The renormalized HK/BF4 route
supplies the independent upper ceiling.  Both are definitionally attached to
the producer's exact separator and spacing family. -/
def fullRangeExactCertificateOfRefinementRenormalizedHK
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  let upper :=
    producer.fullRangeExactCertificateOfAFTrajectoryRenormalizedHK
      C trajectory comparison bare
  flow.toExactLogRefinementFlow.exactPhysicalSeparatorCertificate
    persistence upper.finiteCeiling

@[simp] theorem fullRangeExactCertificateOfRefinementRenormalizedHK_separator
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfRefinementRenormalizedHK
      persistence C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfRefinementRenormalizedHK_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfRefinementRenormalizedHK
      persistence C trajectory comparison bare).uniformFloor.floor =
        persistence.floorWitness := rfl

theorem fullRangeExactCertificateOfRefinementRenormalizedHK_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactRefinementFlow producer)
    (persistence :
      MassNormalizedRefinementPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : Q') <
      (flow.fullRangeExactCertificateOfRefinementRenormalizedHK
        persistence C trajectory comparison bare).uniformFloor.floor :=
  persistence.floorWitness_pos

end BF4FarautExactRefinementFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactRefinementFlow.toExactLogRefinementFlow
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactRefinementFlow.uniformExactFloor
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactRefinementFlow.fullRangeExactCertificateOfRefinementRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactRefinementFlow.fullRangeExactCertificateOfRefinementRenormalizedHK_floor_pos
