/-
M3n -- BF4/Faraut exact physical certificate from spectral localization.

This is the concrete composition of the exact BF4/Faraut physical rate family
with the inverse-Casimir-graded spectral-localization route.  The lower floor
uses the producer's own normalized logarithmic loss flow; the upper ceiling
uses an independent renormalized heat-kernel comparison on the definitionally
same exact rate family.

The producer, spectral-localization inhabitant, same-object rate-loss bridge,
anchor dominance, and renormalized upper comparison remain analytic inputs.
-/

import YMGap.Continuum.BF4FarautAFQuadraticExactLossPersistence
import YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.ExactLogMassNormalizedLossPersistence
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget
open YMGap.Continuum.MassNormalizedLossPersistence
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.SpectralLocalizedMassNormalizedLossPersistence
open YMGap.Continuum.SummableInverseSquare

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

namespace BF4FarautExactLossFlow

/-- Spectral localization and its same-object loss comparison construct the
BF4 producer's physical mass-persistence witness. -/
def spectralLocalizedPersistence
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : SpectralLocalizedRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.rationalFlow.mass 0) :
    MassNormalizedLossPersistence flow.rationalFlow :=
  control.persistence anchorDominates

/-- The localized persistence witness gives a lower floor on the producer's
definitionally exact physical log-rate family. -/
def uniformExactFloorOfSpectralLocalizedLoss
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : SpectralLocalizedRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.rationalFlow.mass 0) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  flow.uniformExactFloor
    (flow.spectralLocalizedPersistence control anchorDominates)

/-- **Spectral-localized same-object hybrid.**  The exact lower floor is
derived from the graded localized defect; the exact upper ceiling comes from
the independent renormalized heat-kernel comparison. -/
def fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : SpectralLocalizedRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  flow.fullRangeExactCertificateOfLossRenormalizedHK
    (flow.spectralLocalizedPersistence control anchorDominates)
    C trajectory comparison bare

@[simp] theorem fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK_separator
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : SpectralLocalizedRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK
      control anchorDominates C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : SpectralLocalizedRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK
      control anchorDominates C trajectory comparison bare).uniformFloor.floor =
      flow.rationalFlow.mass 0 +
        -(fmAconst control.afRate
            (spectralLocalization_defect
              control.afRate control.modeCutoff control.localization) *
          pot 2 (by decide) 0) := rfl

theorem fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautExactLossFlow producer)
    (control : SpectralLocalizedRateLossControl flow.rationalFlow)
    (anchorDominates :
      fmAconst control.afRate
          (spectralLocalization_defect
            control.afRate control.modeCutoff control.localization) *
        pot 2 (by decide) 0 < flow.rationalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : Q') <
      (flow.fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK
        control anchorDominates C trajectory comparison bare).uniformFloor.floor :=
  control.persistent_floor_pos anchorDominates

end BF4FarautExactLossFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.spectralLocalizedPersistence
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.uniformExactFloorOfSpectralLocalizedLoss
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautExactLossFlow.fullRangeExactCertificateOfSpectralLocalizedLossRenormalizedHK_floor_pos
