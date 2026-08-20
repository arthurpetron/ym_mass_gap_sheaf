/-
M3p -- unit-correct BF4/Faraut exact certificate from a localized physical
margin recursion.

The preceding generic conversion defines the normalized physical loss as

  gapDefect k * physicalMass k,

derives its additive step from the multiplicative spectral recursion, and
bounds it by `massCeiling * gapDefect k`.  This file identifies that rational
physical mass sequence with the BF4/Faraut producer's own exact log-rate
family and composes the resulting lower floor with the independent
renormalized heat-kernel ceiling.

No producer or four-dimensional analytic estimate is constructed here.  The
same-family spacing and mass identifications remain explicit fields.
-/

import YMGap.Continuum.BF4FarautExactLossPersistence
import YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss

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
open YMGap.Continuum.SpectralLocalizedPhysicalMarginLoss
open YMGap.Continuum.SummableInverseSquare

namespace BF4FarautQuarterPhysicalSeparatorProducer

variable {family : MatchedBlockFamily}
    {law : CubicMarginLaw family}
    {spacing : PhysicalSpacingEnvelope law.g₁}
    {coupling : Nat -> Q'}
    {bits : Nat -> Nat}
    {P : PhysicalSeparator}

/-- A localized physical-margin flow certified below the BF4/Faraut producer's
definitionally exact physical log-rate family. -/
structure BF4FarautSpectralLocalizedPhysicalMarginFlow
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P) : Type 1 where
  physicalFlow : SpectralLocalizedPhysicalMarginFlow
  spacing_identification : forall k : Nat,
    (physicalFlow.spacing k).eqv
      (producer.fullRangeRateFamily.physicalSpacing.spacing k)
  mass_certificate : forall k : Nat,
    CReal.leEv (CReal.ofQ' (physicalFlow.mass k))
      (producer.fullRangeRateFamily.rate k)

namespace BF4FarautSpectralLocalizedPhysicalMarginFlow

/-- Install the canonically derived additive normalized-loss flow in the
existing same-family BF4/Faraut handoff. -/
def toExactLossFlow
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralLocalizedPhysicalMarginFlow producer) :
    BF4FarautExactLossFlow producer where
  rationalFlow := flow.physicalFlow.toMassNormalizedLossFlow
  spacing_identification := flow.spacing_identification
  mass_certificate := flow.mass_certificate

/-- The localized multiplicative recursion constructs the exact rational
physical mass persistence witness with ceiling-scaled inverse-square cap. -/
def persistence
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralLocalizedPhysicalMarginFlow producer)
    (anchorDominates :
      (flow.physicalFlow.massCeiling *
          fmAconst flow.physicalFlow.afRate
            (spectralLocalization_defect
              flow.physicalFlow.afRate flow.physicalFlow.modeCutoff
                flow.physicalFlow.localization)) *
        pot 2 (by decide) 0 < flow.physicalFlow.mass 0) :
    MassNormalizedLossPersistence
      flow.toExactLossFlow.rationalFlow :=
  flow.physicalFlow.persistence anchorDominates

/-- The resulting persistence supplies a lower floor on the producer's exact
physical rate family. -/
def uniformExactFloor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralLocalizedPhysicalMarginFlow producer)
    (anchorDominates :
      (flow.physicalFlow.massCeiling *
          fmAconst flow.physicalFlow.afRate
            (spectralLocalization_defect
              flow.physicalFlow.afRate flow.physicalFlow.modeCutoff
                flow.physicalFlow.localization)) *
        pot 2 (by decide) 0 < flow.physicalFlow.mass 0) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  flow.toExactLossFlow.uniformExactFloor
    (flow.persistence anchorDominates)

/-- **Unit-correct localized exact physical-rate band.**  The lower floor uses
the ceiling-scaled additive loss derived from the multiplicative recursion;
the upper ceiling is the independent renormalized heat-kernel comparison on
the same exact BF4/Faraut rate family. -/
def fullRangeExactCertificateOfPhysicalMarginRenormalizedHK
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralLocalizedPhysicalMarginFlow producer)
    (anchorDominates :
      (flow.physicalFlow.massCeiling *
          fmAconst flow.physicalFlow.afRate
            (spectralLocalization_defect
              flow.physicalFlow.afRate flow.physicalFlow.modeCutoff
                flow.physicalFlow.localization)) *
        pot 2 (by decide) 0 < flow.physicalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  flow.toExactLossFlow.fullRangeExactCertificateOfLossRenormalizedHK
    (flow.persistence anchorDominates) C trajectory comparison bare

@[simp] theorem fullRangeExactCertificateOfPhysicalMarginRenormalizedHK_separator
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralLocalizedPhysicalMarginFlow producer)
    (anchorDominates :
      (flow.physicalFlow.massCeiling *
          fmAconst flow.physicalFlow.afRate
            (spectralLocalization_defect
              flow.physicalFlow.afRate flow.physicalFlow.modeCutoff
                flow.physicalFlow.localization)) *
        pot 2 (by decide) 0 < flow.physicalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfPhysicalMarginRenormalizedHK
      anchorDominates C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfPhysicalMarginRenormalizedHK_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralLocalizedPhysicalMarginFlow producer)
    (anchorDominates :
      (flow.physicalFlow.massCeiling *
          fmAconst flow.physicalFlow.afRate
            (spectralLocalization_defect
              flow.physicalFlow.afRate flow.physicalFlow.modeCutoff
                flow.physicalFlow.localization)) *
        pot 2 (by decide) 0 < flow.physicalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfPhysicalMarginRenormalizedHK
      anchorDominates C trajectory comparison bare).uniformFloor.floor =
      flow.physicalFlow.mass 0 +
        -((flow.physicalFlow.massCeiling *
            fmAconst flow.physicalFlow.afRate
              (spectralLocalization_defect
                flow.physicalFlow.afRate flow.physicalFlow.modeCutoff
                  flow.physicalFlow.localization)) *
          pot 2 (by decide) 0) := rfl

theorem fullRangeExactCertificateOfPhysicalMarginRenormalizedHK_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    (flow : BF4FarautSpectralLocalizedPhysicalMarginFlow producer)
    (anchorDominates :
      (flow.physicalFlow.massCeiling *
          fmAconst flow.physicalFlow.afRate
            (spectralLocalization_defect
              flow.physicalFlow.afRate flow.physicalFlow.modeCutoff
                flow.physicalFlow.localization)) *
        pot 2 (by decide) 0 < flow.physicalFlow.mass 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : Q') <
      (flow.fullRangeExactCertificateOfPhysicalMarginRenormalizedHK
        anchorDominates C trajectory comparison bare).uniformFloor.floor :=
  flow.physicalFlow.persistent_floor_pos anchorDominates

end BF4FarautSpectralLocalizedPhysicalMarginFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralLocalizedPhysicalMarginFlow.toExactLossFlow
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralLocalizedPhysicalMarginFlow.persistence
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralLocalizedPhysicalMarginFlow.uniformExactFloor
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralLocalizedPhysicalMarginFlow.fullRangeExactCertificateOfPhysicalMarginRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralLocalizedPhysicalMarginFlow.fullRangeExactCertificateOfPhysicalMarginRenormalizedHK_floor_pos
