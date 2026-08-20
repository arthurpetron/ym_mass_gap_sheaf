/-
M2l -- full-range exact logarithmic certificate from the AF/Faraut BF4
fixed-distance producer.

The AF/Faraut adapter fixes the Perron depth to `46 * bits + 3` and proves
that this depth occupies a uniformly bounded physical cylinder.  Once its
explicit same-object field identifies that grouped contraction with powers of
the physical correlator separator, the generic fixed-distance theorem now
gives a uniform exact lower bound for `-log(q_j) / a_j` on the whole interval
`0 < q_j < 1`.

No half-window is needed here.  A finite upper bound for the exact logarithmic
rate remains an independent analytic input; this file names and packages that
obligation rather than deriving it from BF4.
-/

import YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
import YMGap.Continuum.FixedDistanceFullLogCertificate

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.FixedDistancePhysicalSeparator

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> YMGap.Constructive.Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

/-- The canonical full-range exact logarithmic rate family on the same
physical separator and AF spacing trajectory as the BF4 certificate. -/
def fullRangeRateFamily
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    FullRangeExactPhysicalLogRateFamily P :=
  producer.toBF4QuarterPhysicalSeparatorProducer.fixedDistance
    |>.fullRangeRateFamily

/-- **AF/Faraut BF4 full-range floor.**  The explicit positive BF4 physical
floor bounds the exact logarithmic mass rate at every scale, without a
half-window assumption. -/
def fullRangeExactFloor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  producer.toBF4QuarterPhysicalSeparatorProducer.fixedDistance
    |>.fullRangeExactFloor

/-- The independent exact upper-rate obligation for this AF/Faraut BF4
family. -/
abbrev FullRangeExactCeiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type :=
  FixedDistanceContraction.FullRangeExactCeiling
    producer.toBF4QuarterPhysicalSeparatorProducer.fixedDistance

/-- Package the AF/Faraut BF4 lower producer and an independent finite exact
upper rate into the complete full-range separator certificate. -/
def fullRangeExactCertificate
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (U : producer.FullRangeExactCeiling) :
    FullRangeExactPhysicalSeparatorCertificate :=
  producer.toBF4QuarterPhysicalSeparatorProducer.fixedDistance
    |>.fullRangeExactCertificate U

@[simp] theorem fullRangeExactFloor_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    producer.fullRangeExactFloor.floor =
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate := rfl

theorem fullRangeExactFloor_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) :
    (0 : YMGap.Constructive.Q') < producer.fullRangeExactFloor.floor :=
  producer.physicalFloorRate_pos

@[simp] theorem fullRangeExactCertificate_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (U : producer.FullRangeExactCeiling) :
    (producer.fullRangeExactCertificate U).separator = P := rfl

@[simp] theorem fullRangeExactCertificate_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (U : producer.FullRangeExactCeiling) :
    (producer.fullRangeExactCertificate U).uniformFloor.floor =
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate := rfl

@[simp] theorem fullRangeExactCertificate_ceiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (U : producer.FullRangeExactCeiling) :
    (producer.fullRangeExactCertificate U).finiteCeiling.ceiling =
      U.ceiling := rfl

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactFloor
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactFloor_floor_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificate
