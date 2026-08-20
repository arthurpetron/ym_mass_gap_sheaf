/-
M3g -- preferred same-family handoff from normalized RG loss to the
BF4/Faraut exact physical-rate band.

The lower floor and renormalized upper ceiling are attached definitionally to
the producer's one exact separator and spacing family.  The lower interface is
direction-neutral: it does not require an exact integer ratio between adjacent
AF spacings.

No analytic input is constructed.  The exact BF4 same-object producer,
rational one-step estimate, summable normalized loss, renormalized comparison,
and renormalized bare bound remain explicit data.
-/

import YMGap.Continuum.BF4FarautFullLogPrefixTailCertificate
import YMGap.Continuum.ExactLogMassNormalizedLossPersistence

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.ExactLogMassNormalizedLossPersistence
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

/-- A direction-neutral rational loss flow certified below the producer's own
exact physical logarithmic rate family. -/
structure BF4FarautExactLossFlow
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type 1 where
  rationalFlow : MassNormalizedLossFlow
  spacing_identification : forall k : Nat,
    (rationalFlow.spacing k).eqv
      (producer.fullRangeRateFamily.physicalSpacing.spacing k)
  mass_certificate : forall k : Nat,
    CReal.leEv (CReal.ofQ' (rationalFlow.mass k))
      (producer.fullRangeRateFamily.rate k)

namespace BF4FarautExactLossFlow

/-- Forget the BF4/Faraut specialization while retaining the exact rate family
definitionally. -/
def toExactLogLossFlow
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer) :
    ExactLogMassNormalizedLossFlow P where
  exactRate := producer.fullRangeRateFamily
  rationalFlow := flow.rationalFlow
  spacing_identification := flow.spacing_identification
  mass_certificate := flow.mass_certificate

/-- Persistent normalized-loss data supplies the lower floor on the producer's
own exact family. -/
def uniformExactFloor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  flow.toExactLogLossFlow.uniformExactFloor persistence

@[simp] theorem uniformExactFloor_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow) :
    (flow.uniformExactFloor persistence).floor =
      persistence.floorWitness := rfl

theorem uniformExactFloor_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow) :
    (0 : Q') < (flow.uniformExactFloor persistence).floor :=
  persistence.floorWitness_pos

/-- **Preferred one-object hybrid physical-rate band.**  The normalized-loss
persistence gives the exact lower floor; the renormalized BF4/HK route gives
the exact upper ceiling, with no block-factor premise in the lower path. -/
def fullRangeExactCertificateOfLossRenormalizedHK
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  let upper :=
    producer.fullRangeExactCertificateOfAFTrajectoryRenormalizedHK
      C trajectory comparison bare
  flow.toExactLogLossFlow.exactPhysicalSeparatorCertificate
    persistence upper.finiteCeiling

@[simp] theorem fullRangeExactCertificateOfLossRenormalizedHK_separator
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfLossRenormalizedHK
      persistence C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfLossRenormalizedHK_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfLossRenormalizedHK
      persistence C trajectory comparison bare).uniformFloor.floor =
        persistence.floorWitness := rfl

theorem fullRangeExactCertificateOfLossRenormalizedHK_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (persistence : MassNormalizedLossPersistence flow.rationalFlow)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : Q') <
      (flow.fullRangeExactCertificateOfLossRenormalizedHK
        persistence C trajectory comparison bare).uniformFloor.floor :=
  persistence.floorWitness_pos

end BF4FarautExactLossFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.toExactLogLossFlow
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.uniformExactFloor
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfLossRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfLossRenormalizedHK_floor_pos
