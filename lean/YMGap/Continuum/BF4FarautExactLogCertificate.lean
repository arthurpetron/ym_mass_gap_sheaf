/-
M2g -- the complete conditional route from the AF/Faraut BF4 producer to the
exact physical logarithmic separator certificate.

The preceding reductions separately provide:

* a BF4 quarter contraction whose exact `46 * bits + 3` depth occupies a
  uniformly bounded physical cylinder;
* a fixed-distance lower bound for the rational margin rate `(1 - q_j)/a_j`;
* a constructive direct logarithm window whenever `q_j >= 1/2`;
* transport of a two-sided rational margin band to the exact rate
  `-log(q_j)/a_j`.

This file composes those reductions.  It does not construct any of their
analytic inputs.  In particular, the same-object field identifying the BF4
macro contraction with powers of the physical correlator separator, the
uniform half-window, and the independent finite upper rate remain explicit
obligations.
-/

import YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
import YMGap.Continuum.PhysicalSeparatorHalfWindow

namespace YMGap.Continuum.BF4FarautExactLogCertificate

open YMGap.Continuum
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.BF4FarautPhysicalSeparatorProducer
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.PhysicalSeparatorHalfWindow

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> YMGap.Constructive.Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

/-- The finite upper-rate input for the AF/Faraut-reduced producer.  Keeping
this as a named type makes clear that BF4 fixed-distance contraction supplies
the lower bound, not this independent finiteness estimate. -/
abbrev MarginRateCeiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type :=
  producer.toBF4QuarterPhysicalSeparatorProducer.MarginRateCeiling

/-- Exact `-log(q_j)/a_j` certificate obtained from the AF/Faraut BF4
fixed-distance reduction, the simple half-window, and an independent upper
margin-rate ceiling. -/
def exactCertificateOfHalfWindow
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (H : SeparatorHalfWindow P)
    (U : MarginRateCeiling producer) :
    ExactPhysicalSeparatorCertificate :=
  producer.toBF4QuarterPhysicalSeparatorProducer
    |>.exactPhysicalSeparatorCertificate H.toPhysicalLogWindow U

/-- The exact certificate is built on the same physical separator `P`; it is
not a synthetic separator introduced after the BF4 estimate. -/
@[simp] theorem exactCertificateOfHalfWindow_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (H : SeparatorHalfWindow P)
    (U : MarginRateCeiling producer) :
    (exactCertificateOfHalfWindow producer H U).separator = P :=
  rfl

/-- The lower exact logarithmic rate is the explicit BF4 fixed-distance
floor `(1 - 1/4) / lengthCeiling`. -/
@[simp] theorem exactCertificateOfHalfWindow_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (H : SeparatorHalfWindow P)
    (U : MarginRateCeiling producer) :
    (exactCertificateOfHalfWindow producer H U).uniformBand.floor =
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate :=
  rfl

/-- The exact logarithmic upper rate is the supplied rational ceiling times
the constructive direct-window constant `9/4`. -/
@[simp] theorem exactCertificateOfHalfWindow_ceiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (H : SeparatorHalfWindow P)
    (U : MarginRateCeiling producer) :
    (exactCertificateOfHalfWindow producer H U).uniformBand.ceiling =
      EffMassConvergence.c94 * U.ceiling :=
  rfl

/-- The composed exact certificate retains the constructive strict positivity
of the AF/Faraut-derived physical floor. -/
theorem exactCertificateOfHalfWindow_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (H : SeparatorHalfWindow P)
    (U : MarginRateCeiling producer) :
    (0 : YMGap.Constructive.Q') <
      (exactCertificateOfHalfWindow producer H U).uniformBand.floor :=
  producer.physicalFloorRate_pos

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautExactLogCertificate

#print axioms YMGap.Continuum.BF4FarautExactLogCertificate.BF4FarautQuarterPhysicalSeparatorProducer.exactCertificateOfHalfWindow
#print axioms YMGap.Continuum.BF4FarautExactLogCertificate.BF4FarautQuarterPhysicalSeparatorProducer.exactCertificateOfHalfWindow_separator
#print axioms YMGap.Continuum.BF4FarautExactLogCertificate.BF4FarautQuarterPhysicalSeparatorProducer.exactCertificateOfHalfWindow_floor
#print axioms YMGap.Continuum.BF4FarautExactLogCertificate.BF4FarautQuarterPhysicalSeparatorProducer.exactCertificateOfHalfWindow_ceiling
#print axioms YMGap.Continuum.BF4FarautExactLogCertificate.BF4FarautQuarterPhysicalSeparatorProducer.exactCertificateOfHalfWindow_floor_pos
