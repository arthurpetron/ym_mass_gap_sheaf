/-
M3l -- same-family BF4/Faraut handoff from an AF quadratic RG defect.

This is the preferred AF-shaped lower-floor route.  It composes:

  exact BF4/Faraut loss flow
    + same-flow comparison `rateLoss <= fullModeDefect`
    + quadratic AF full-mode defect
    + explicit anchor dominance

into a uniform lower floor on the producer's own exact physical log-rate
family.  An independent renormalized BF4/heat-kernel comparison supplies the
upper ceiling on that definitionally identical family.

The genuine four-dimensional full-mode defect, same-flow comparison, anchor
inequality, producer, and renormalized upper comparison remain analytic data.
-/

import YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence
import YMGap.Continuum.BF4FarautExactLossPersistence

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFQuadraticMassNormalizedLossPersistence
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.ExactLogMassNormalizedLossPersistence
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.SummableInverseSquare

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

namespace BF4FarautExactLossFlow

/-- The AF quadratic full-mode comparison constructs the persistence witness
for the BF4 producer's rational loss flow. -/
def afQuadraticPersistence
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0) :
    MassNormalizedLossPersistence flow.rationalFlow :=
  control.persistence anchorDominates

@[simp] theorem afQuadraticPersistence_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0) :
    (flow.afQuadraticPersistence control anchorDominates).floorWitness =
      flow.rationalFlow.mass 0 +
        -(fmAconst control.afRate control.defect * pot 2 (by decide) 0) := rfl

theorem afQuadraticPersistence_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0) :
    (0 : Q') <
      (flow.afQuadraticPersistence control anchorDominates).floorWitness :=
  control.persistent_floor_pos anchorDominates

/-- The constructed AF quadratic persistence supplies a lower floor on the
producer's exact rate family. -/
def uniformExactFloorOfAFQuadraticLoss
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  flow.uniformExactFloor
    (flow.afQuadraticPersistence control anchorDominates)

/-- **Preferred AF quadratic same-object hybrid.**  The lower exact floor is
derived from the AF full-mode inverse-square budget; the upper exact ceiling is
the producer's independent renormalized heat-kernel comparison. -/
def fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  flow.fullRangeExactCertificateOfLossRenormalizedHK
    (flow.afQuadraticPersistence control anchorDominates)
    C trajectory comparison bare

@[simp] theorem fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK_separator
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK
      control anchorDominates C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK
      control anchorDominates C trajectory comparison bare).uniformFloor.floor =
      flow.rationalFlow.mass 0 +
        -(fmAconst control.afRate control.defect * pot 2 (by decide) 0) := rfl

theorem fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : AFQuadraticRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate control.defect * pot 2 (by decide) 0 <
        flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : Q') <
      (flow.fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK
        control anchorDominates C trajectory comparison bare).uniformFloor.floor :=
  control.persistent_floor_pos anchorDominates

end BF4FarautExactLossFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.afQuadraticPersistence
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.uniformExactFloorOfAFQuadraticLoss
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfAFQuadraticLossRenormalizedHK_floor_pos
