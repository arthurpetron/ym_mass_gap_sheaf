/-
M3r -- exact BF4/Faraut certificate from the repository's wired
`SpectralMarginInput`.

`SpectralMarginInputMassNormalizedLoss` proves that the existing spectral
margin package already determines a constructive additive physical-loss flow,
with inverse-square coefficient `ceilConst * fmAconst` and the correct shifted
offset.  This file states only the remaining exact-family identifications and
then composes the resulting lower floor with the BF4/Faraut renormalized
heat-kernel ceiling.

The input is still conditional: no four-dimensional `SpectralMarginInput`,
BF4/Faraut producer, or exact mass comparison is constructed here.
-/

import YMGap.Continuum.BF4FarautExactLossPersistence
import YMGap.Continuum.SpectralMarginInputMassNormalizedLoss

namespace YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.AFRateCalibration
open YMGap.Continuum.AFTrajectoryCertificate
open YMGap.Continuum.AsymptoticSpectralLoc
open YMGap.Continuum.BF4MatchedPhysicalAFBridge
open YMGap.Continuum.BF4PhysicalSeparatorProducer
open YMGap.Continuum.ExactLogMassNormalizedLossPersistence
open YMGap.Continuum.FullModeAssembly
open YMGap.Continuum.GradedBondMovingBudget
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

/-- The existing wired spectral-margin input, identified with the producer's
own exact physical spacing and log-rate family. -/
structure BF4FarautSpectralMarginInputExactFlow
    (producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P)
    (b : Nat) (afr : AFRateModulus) (N₀ : Nat) : Type 1 where
  input : SpectralMarginInput b afr N₀
  spacing_identification : forall k : Nat,
    (input.spacing k).eqv
      (producer.fullRangeRateFamily.physicalSpacing.spacing k)
  mass_certificate : forall k : Nat,
    CReal.leEv (CReal.ofQ' (input.g k))
      (producer.fullRangeRateFamily.rate k)

namespace BF4FarautSpectralMarginInputExactFlow

/-- Install the additive normalized-loss flow constructed from
`SpectralMarginInput` into the exact BF4/Faraut handoff. -/
def toExactLossFlow
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀) :
    BF4FarautExactLossFlow producer where
  rationalFlow := flow.input.toMassNormalizedLossFlow
  spacing_identification := flow.spacing_identification
  mass_certificate := flow.mass_certificate

/-- The shifted localized defect budget gives the exact rational physical-mass
persistence witness. -/
def persistence
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N₀ flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0) :
    MassNormalizedLossPersistence flow.toExactLossFlow.rationalFlow :=
  flow.input.persistence anchorDominates

/-- The wired input supplies a lower floor on the producer's exact rate
family. -/
def uniformExactFloor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N₀ flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0) :
    UniformFullRangeLogRateFloor producer.fullRangeRateFamily :=
  flow.toExactLossFlow.uniformExactFloor (flow.persistence anchorDominates)

/-- **Wired spectral-margin same-family certificate.**  The exact lower floor
comes from the existing `SpectralMarginInput`; the upper ceiling comes from the
independent renormalized heat-kernel comparison on the same BF4/Faraut family. -/
def fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N₀ flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    FullRangeExactPhysicalSeparatorCertificate :=
  flow.toExactLossFlow.fullRangeExactCertificateOfLossRenormalizedHK
    (flow.persistence anchorDominates) C trajectory comparison bare

@[simp] theorem fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK_separator
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N₀ flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK
      anchorDominates C trajectory comparison bare).separator = P := rfl

@[simp] theorem fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK_floor
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N₀ flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (flow.fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK
      anchorDominates C trajectory comparison bare).uniformFloor.floor =
      flow.input.g 0 +
        -((flow.input.ceilConst *
            fmAconst afr
              (spectralLocalization_defect afr N₀ flow.input.sl)) *
          pot
            (fmCutoff afr
                (spectralLocalization_defect afr N₀ flow.input.sl) + 2)
            (by omega) 0) := rfl

theorem fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK_floor_pos
    {producer : BF4FarautQuarterPhysicalSeparatorProducer
      family law spacing coupling bits P}
    {b : Nat} {afr : AFRateModulus} {N₀ : Nat}
    (flow : BF4FarautSpectralMarginInputExactFlow producer b afr N₀)
    (anchorDominates :
      (flow.input.ceilConst *
          fmAconst afr (spectralLocalization_defect afr N₀ flow.input.sl)) *
        pot
          (fmCutoff afr
              (spectralLocalization_defect afr N₀ flow.input.sl) + 2)
          (by omega) 0 < flow.input.g 0)
    (C : AFTrajectoryCertificate)
    (trajectory : producer.ShiftedAFCoupling C)
    (comparison : producer.RenormalizedPhysicalComparison)
    (bare : producer.RenormalizedBareTail comparison) :
    (0 : Q') <
      (flow.fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK
        anchorDominates C trajectory comparison bare).uniformFloor.floor :=
  flow.input.persistent_floor_pos anchorDominates

end BF4FarautSpectralMarginInputExactFlow

end BF4FarautQuarterPhysicalSeparatorProducer

end YMGap.Continuum.BF4FarautPhysicalSeparatorProducer

#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.toExactLossFlow
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.persistence
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.uniformExactFloor
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK
#print axioms YMGap.Continuum.BF4FarautPhysicalSeparatorProducer.BF4FarautQuarterPhysicalSeparatorProducer.BF4FarautSpectralMarginInputExactFlow.fullRangeExactCertificateOfSpectralMarginInputRenormalizedHK_floor_pos
