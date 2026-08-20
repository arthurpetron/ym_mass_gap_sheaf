/-
M2o -- the AF/Faraut BF4 full-range certificate from finite-prefix and
eventual-tail upper data.

The AF/Faraut BF4 producer supplies the exact positive lower rate once its
explicit same-object field is inhabited.  The upper-rate route is now split
into three independently auditable inputs on that very same rate family:

* one finite-prefix exact ceiling;
* an eventual half-window for the same physical separator;
* a rational margin-rate ceiling on that tail.

The generic half-window comparison turns the last two into an exact tail
ceiling, the prefix/tail maximum gives a global exact ceiling, and the earlier
BF4/Faraut constructor packages the full certificate.  This file performs
only that composition; it does not manufacture any of the analytic inputs.
-/

import YMGap.Continuum.BF4FarautFullLogCertificate
import YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
import YMGap.Continuum.FinitePrefixFullLogRateCeiling
import YMGap.Continuum.PhysicalSeparatorLinearTail
import YMGap.Continuum.BF4AFPhysicalSpacingToZero
import YMGap.Continuum.HKPhysicalLinearMarginTail
import YMGap.Continuum.RenormalizedHKPhysicalComparison

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.RGTransport
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.PhysicalSeparatorFullLogHalfWindow
open YMGap.Continuum.FinitePrefixFullLogRateCeiling
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.BF4AFPhysicalSpacingToZero
open YMGap.Continuum.HKPhysicalLinearMarginTail
open YMGap.Continuum.RenormalizedHKPhysicalComparison

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> YMGap.Constructive.Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

/-- Finite-prefix exact upper data for the canonical AF/Faraut full-range rate
family. -/
abbrev PrefixExactCeiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) (start : Nat) : Type :=
  PrefixFullRangeLogRateCeiling producer.fullRangeRateFamily start

/-- Eventual direct half-window data for the same physical separator. -/
abbrev EventualHalfWindow
    (_producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) (start : Nat) : Type :=
  EventualSeparatorHalfWindow P start

/-- Rational margin-rate upper data on the AF/Faraut spacing tail. -/
abbrev TailMarginCeiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) (start : Nat) : Type :=
  TailMarginRateCeiling P
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing start

/-- The finite-prefix and eventual-tail inputs construct the independent exact
upper-rate obligation of the BF4/Faraut full-range certificate. -/
def fullRangeExactCeilingOfPrefixTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (pre : producer.PrefixExactCeiling start)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    producer.FullRangeExactCeiling :=
  globalExactCeilingOfPrefixEventualHalfWindow P
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing
    start pre H U

/-- **Conditional full BF4/Faraut exact separator certificate.**  Its lower
rate is produced by the fixed-distance BF4 contraction; its upper rate is the
maximum of the supplied finite-prefix ceiling and `9/4` times the supplied
tail margin ceiling. -/
def fullRangeExactCertificateOfPrefixTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (pre : producer.PrefixExactCeiling start)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    FullRangeExactPhysicalSeparatorCertificate :=
  producer.fullRangeExactCertificate
    (producer.fullRangeExactCeilingOfPrefixTail start pre H U)

@[simp] theorem fullRangeExactCertificateOfPrefixTail_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (pre : producer.PrefixExactCeiling start)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    (producer.fullRangeExactCertificateOfPrefixTail start pre H U).separator =
      P := rfl

@[simp] theorem fullRangeExactCertificateOfPrefixTail_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (pre : producer.PrefixExactCeiling start)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    (producer.fullRangeExactCertificateOfPrefixTail start pre H U).uniformFloor.floor =
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate := rfl

@[simp] theorem fullRangeExactCertificateOfPrefixTail_ceiling
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (pre : producer.PrefixExactCeiling start)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    (producer.fullRangeExactCertificateOfPrefixTail start pre H U).finiteCeiling.ceiling =
      YMGap.Constructive.Q'.max' pre.ceiling
        (EffMassConvergence.c94 * U.ceiling) := rfl

theorem fullRangeExactCertificateOfPrefixTail_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (pre : producer.PrefixExactCeiling start)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    (0 : YMGap.Constructive.Q') <
      (producer.fullRangeExactCertificateOfPrefixTail start pre H U).uniformFloor.floor :=
  producer.physicalFloorRate_pos

/-! ## The finite prefix is automatic -/

/-- Once a tail start is chosen, the finite-prefix input is computed directly
from the exact separator and spacing data.  Only the genuinely asymptotic
half-window and margin-rate ceiling remain as inputs. -/
def fullRangeExactCeilingOfEventualTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    producer.FullRangeExactCeiling :=
  producer.fullRangeExactCeilingOfPrefixTail start
    (computedPrefixCeiling producer.fullRangeRateFamily start) H U

/-- **BF4/Faraut full exact certificate with no finite-prefix hypothesis.**
The only upper-rate inputs are the eventual half-window and the uniform
rational margin-rate ceiling on that tail. -/
def fullRangeExactCertificateOfEventualTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    FullRangeExactPhysicalSeparatorCertificate :=
  producer.fullRangeExactCertificate
    (producer.fullRangeExactCeilingOfEventualTail start H U)

@[simp] theorem fullRangeExactCertificateOfEventualTail_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    (producer.fullRangeExactCertificateOfEventualTail start H U).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfEventualTail_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    (producer.fullRangeExactCertificateOfEventualTail start H U).uniformFloor.floor =
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate := rfl

theorem fullRangeExactCertificateOfEventualTail_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (start : Nat)
    (H : producer.EventualHalfWindow start)
    (U : producer.TailMarginCeiling start) :
    (0 : YMGap.Constructive.Q') <
      (producer.fullRangeExactCertificateOfEventualTail start H U).uniformFloor.floor :=
  producer.physicalFloorRate_pos

/-! ## Reduction to the Gibbs-shaped linear margin tail -/

/-- The remaining upper-rate input in its cross-multiplied, Gibbs-shaped form:
`1 - sep_j <= M * a_j` eventually on the producer's own spacing. -/
abbrev LinearPhysicalMarginTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type :=
  LinearMarginTail P
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing

/-- An explicit vanishing modulus for the same physical AF spacing. -/
abbrev PhysicalSpacingToZero
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type :=
  SpacingToZero
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing

/-- **BF4/Faraut exact separator certificate from one linear margin estimate.**
The spacing modulus computes the half-window start; the same estimate gives the
tail margin-rate ceiling; the finite prefix is computed automatically. -/
def fullRangeExactCertificateOfLinearTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (L : producer.LinearPhysicalMarginTail)
    (Z : producer.PhysicalSpacingToZero) :
    FullRangeExactPhysicalSeparatorCertificate :=
  producer.fullRangeExactCertificateOfEventualTail
    (L.eventualStart Z)
    (L.toEventualHalfWindow Z)
    (L.toTailMarginRateCeiling Z)

@[simp] theorem fullRangeExactCertificateOfLinearTail_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (L : producer.LinearPhysicalMarginTail)
    (Z : producer.PhysicalSpacingToZero) :
    (producer.fullRangeExactCertificateOfLinearTail L Z).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfLinearTail_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (L : producer.LinearPhysicalMarginTail)
    (Z : producer.PhysicalSpacingToZero) :
    (producer.fullRangeExactCertificateOfLinearTail L Z).uniformFloor.floor =
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate := rfl

theorem fullRangeExactCertificateOfLinearTail_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (L : producer.LinearPhysicalMarginTail)
    (Z : producer.PhysicalSpacingToZero) :
    (0 : YMGap.Constructive.Q') <
    (producer.fullRangeExactCertificateOfLinearTail L Z).uniformFloor.floor :=
  producer.physicalFloorRate_pos

/-! ## AF trajectory closes the spacing input -/

/-- **BF4/Faraut exact separator certificate from one remaining physical
margin estimate.**  Once the producer's coupling is identified with a proved
two-loop AF trajectory, the quadratic physical-spacing envelope constructs
the spacing modulus automatically.  Thus the sole additional upper-rate datum
at this layer is the same-object estimate `1 - sep_j <= M * a_j` eventually. -/
def fullRangeExactCertificateOfAFTrajectoryLinearTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (H : producer.ShiftedAFCoupling C)
    (L : producer.LinearPhysicalMarginTail) :
    FullRangeExactPhysicalSeparatorCertificate :=
  producer.fullRangeExactCertificateOfLinearTail L
    (producer.physicalSpacingToZeroOfAFTrajectory C H)

@[simp] theorem fullRangeExactCertificateOfAFTrajectoryLinearTail_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (H : producer.ShiftedAFCoupling C)
    (L : producer.LinearPhysicalMarginTail) :
    (producer.fullRangeExactCertificateOfAFTrajectoryLinearTail C H L).separator =
      P := rfl

@[simp] theorem fullRangeExactCertificateOfAFTrajectoryLinearTail_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (H : producer.ShiftedAFCoupling C)
    (L : producer.LinearPhysicalMarginTail) :
    (producer.fullRangeExactCertificateOfAFTrajectoryLinearTail C H L).uniformFloor.floor =
      producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate := rfl

theorem fullRangeExactCertificateOfAFTrajectoryLinearTail_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (H : producer.ShiftedAFCoupling C)
    (L : producer.LinearPhysicalMarginTail) :
    (0 : YMGap.Constructive.Q') <
      (producer.fullRangeExactCertificateOfAFTrajectoryLinearTail C H L).uniformFloor.floor :=
  producer.physicalFloorRate_pos

/-! ## Bare-to-physical comparison closes the residual part of the tail -/

/-- A bare-to-physical comparison on exactly the producer's separator and
spacing trajectory. -/
abbrev HKComparison
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type :=
  HKPhysicalComparison P
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing.spacing

/-- The remaining bare heat-kernel `O(a)` estimate after the comparison's own
residual bound has been consumed. -/
abbrev BareHeatKernelLinearTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (comparison : producer.HKComparison) : Type :=
  BareHeatKernelLinearMarginTail
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing comparison

/-- **BF4/Faraut exact band from the existing physical comparison split.**
The comparison contributes its already-named `O(a)` residual automatically;
the only extra upper input here is the bare heat-kernel margin bound. -/
def fullRangeExactCertificateOfAFTrajectoryHKComparison
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.HKComparison)
    (bare : producer.BareHeatKernelLinearTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  producer.fullRangeExactCertificateOfAFTrajectoryLinearTail C trajectory
    bare.toLinearMarginTail

@[simp] theorem fullRangeExactCertificateOfAFTrajectoryHKComparison_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.HKComparison)
    (bare : producer.BareHeatKernelLinearTail comparison) :
    (producer.fullRangeExactCertificateOfAFTrajectoryHKComparison
      C trajectory comparison bare).separator = P := rfl

theorem fullRangeExactCertificateOfAFTrajectoryHKComparison_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.HKComparison)
    (bare : producer.BareHeatKernelLinearTail comparison) :
    (0 : YMGap.Constructive.Q') <
      (producer.fullRangeExactCertificateOfAFTrajectoryHKComparison
        C trajectory comparison bare).uniformFloor.floor :=
  producer.physicalFloorRate_pos

/-! ## Renormalized bare-to-physical comparison

The preceding additive comparison is deliberately retained as a diagnostic:
an `O(a)` two-sided residual makes finiteness of the physical and bare rates
equivalent.  The following route is the physically useful open interface.  Its
scale-dependent factor `Z_j` may carry the nonperturbative RG suppression, and
only the renormalized bare margin `Z_j * (1-w_j^3)` must be `O(a)`.
-/

/-- A renormalized bare-to-physical upper comparison on exactly the producer's
physical separator and spacing trajectory. -/
abbrev RenormalizedPhysicalComparison
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type :=
  RenormalizedHKComparison P
    producer.toBF4QuarterPhysicalSeparatorProducer.physicalSpacing

/-- The same-object `O(a)` estimate after multiplication by the comparison's
nonperturbative scale factor. -/
abbrev RenormalizedBareTail
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (comparison : producer.RenormalizedPhysicalComparison) : Type :=
  RenormalizedBareLinearTail comparison

/-- **BF4/Faraut exact band from the renormalized physical comparison.**
The AF trajectory supplies spacing-to-zero.  The renormalized bare estimate
and the comparison residual jointly supply the sole physical upper seam
`1 - sep_j <= M * a_j`; the fixed-distance BF4 producer supplies the positive
lower rate on that same separator. -/
def fullRangeExactCertificateOfAFTrajectoryRenormalizedHK
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  producer.fullRangeExactCertificateOfAFTrajectoryLinearTail C trajectory
    bare.toPhysicalLinearMarginTail

@[simp] theorem fullRangeExactCertificateOfAFTrajectoryRenormalizedHK_separator
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (producer.fullRangeExactCertificateOfAFTrajectoryRenormalizedHK
      C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfAFTrajectoryRenormalizedHK_floor
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (producer.fullRangeExactCertificateOfAFTrajectoryRenormalizedHK
      C trajectory comparison bare).uniformFloor.floor =
        producer.toBF4QuarterPhysicalSeparatorProducer.physicalFloorRate := rfl

theorem fullRangeExactCertificateOfAFTrajectoryRenormalizedHK_floor_pos
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : YMGap.Constructive.Q') <
      (producer.fullRangeExactCertificateOfAFTrajectoryRenormalizedHK
        C trajectory comparison bare).uniformFloor.floor :=
  producer.physicalFloorRate_pos

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCeilingOfPrefixTail
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfPrefixTail
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfPrefixTail_floor_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCeilingOfEventualTail
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfEventualTail
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfEventualTail_floor_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfLinearTail
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfLinearTail_floor_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfAFTrajectoryLinearTail
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfAFTrajectoryLinearTail_floor_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfAFTrajectoryHKComparison
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfAFTrajectoryHKComparison_floor_pos
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfAFTrajectoryRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.fullRangeExactCertificateOfAFTrajectoryRenormalizedHK_floor_pos
