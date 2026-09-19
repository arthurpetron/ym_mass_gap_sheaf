/-
# Primitive variation compiler for the completed physical gap

The dynamic completed-family path defines

  `physicalGap = latticeMargin / transferSpacing`.

This module compiles explicit primitive variation witnesses into the exact
same-family `SummableRationalStepVariation family.physicalGap`: one witness
for the dimensionless lattice margin and one for the reciprocal spacing.  A
finite-regulator shortcut can build the reciprocal witness from positive
spacing variation and a fixed floor, but a continuum spacing tends to zero, so
the direct reciprocal witness is the honest continuum-facing interface.  The
product step is generic and the final pointwise equality is only the
definition of `Q'.divPos`.

The result is a backward-facing mass-calibration interface.  It does not
construct either primitive variation stream, the physical rate band, a
continuum measure, or the Clay mass gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
`noncomputable` declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
import YMGap.Continuum.SummableRationalReciprocalStepVariation
import YMGap.Continuum.SummableRationalStepVariationAlgebra

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin

local infix:50 " ≈ " => Q'.eqv
open YMGap.Continuum.SummableRationalReciprocalStepVariation
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.SummableRationalStepVariationAlgebra

/-! ## 1. Exact same-family variation -/

/-- Margin variation and direct reciprocal-spacing variation meet at the exact
completed-family physical gap.  This is the continuum-compatible interface:
it does not assume a positive lower floor for a spacing stream that tends to
zero. -/
def physicalGapVariationOfMarginAndReciprocalSpacing
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (marginVariation :
      SummableRationalStepVariation family.latticeMargin)
    (reciprocalSpacingVariation :
      SummableRationalStepVariation
        (fun scale =>
          Q'.recipPos
            (family.transferSpacing.spacing scale)
            (family.transferSpacing.spacing_pos scale))) :
    SummableRationalStepVariation family.physicalGap := by
  let productVariation := mul marginVariation reciprocalSpacingVariation
    (fun scale => Q'.le_of_lt (family.latticeMargin_pos scale))
    (fun scale =>
      Q'.le_of_lt
        (Q'.recipPos_pos
          (family.transferSpacing.spacing scale)
          (family.transferSpacing.spacing_pos scale)))
  exact ofPointwiseEqv productVariation (fun scale => by
    change family.latticeMargin scale *
        Q'.recipPos
          (family.transferSpacing.spacing scale)
          (family.transferSpacing.spacing_pos scale) ≈
      family.physicalGap scale
    unfold DynamicVacuumSectorCompletedFamily.physicalGap
    exact Q'.eqv_refl _)

/-- Margin variation and positive-spacing variation meet at the exact
completed-family physical gap.  The positive spacing floor is the explicit
noncollapse witness needed by the reciprocal compiler. -/
def physicalGapVariationOfPrimitiveComponents
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (marginVariation :
      SummableRationalStepVariation family.latticeMargin)
    (spacingVariation :
      SummableRationalStepVariation
        (fun scale => family.transferSpacing.spacing scale))
    (spacingFloor : Q')
    (spacingFloor_pos : (0 : Q') < spacingFloor)
    (spacingFloor_le :
      ∀ scale, spacingFloor ≤ family.transferSpacing.spacing scale) :
    SummableRationalStepVariation family.physicalGap := by
  let reciprocalSpacingVariation := reciprocal
    (fun scale => family.transferSpacing.spacing_pos scale)
    spacingVariation spacingFloor spacingFloor_pos spacingFloor_le
  exact physicalGapVariationOfMarginAndReciprocalSpacing
    family marginVariation reciprocalSpacingVariation

/-! ## 2. Explicit join to the exact-log backward target -/

/-- The continuum-compatible reciprocal-spacing compiler feeds the existing
exact-log Cauchy compiler without changing the completed family, observable
pin, or spacing tail. -/
def exactLogRateCauchy_of_marginAndReciprocalSpacing
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (marginVariation :
      SummableRationalStepVariation family.latticeMargin)
    (reciprocalSpacingVariation :
      SummableRationalStepVariation
        (fun scale =>
          Q'.recipPos
            (family.transferSpacing.spacing scale)
            (family.transferSpacing.spacing_pos scale)))
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) :=
  DynamicVacuumSectorObservablePin.exactLogRateCauchy
    pin band
    (physicalGapVariationOfMarginAndReciprocalSpacing
      family marginVariation reciprocalSpacingVariation)
    spacingTail

/-- The primitive variation inputs can be inserted into the existing
continuum handoff without changing its same-theory observable, OS/GNS, or
reconstruction fields.  Those semantic fields remain explicit arguments. -/
def DynamicVacuumSectorContinuumHandoff.ofMarginAndReciprocalSpacing
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling (fullRangeRateFamily pin)}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (marginVariation :
      SummableRationalStepVariation family.latticeMargin)
    (reciprocalSpacingVariation :
      SummableRationalStepVariation
        (fun scale =>
          Q'.recipPos
            (family.transferSpacing.spacing scale)
            (family.transferSpacing.spacing_pos scale)))
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0)
    (projectiveOS : ProjectiveOSCorrelationHandoff pin.toPhysicalSeparator
      existence osGNS pin.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (exactCertificate pin band ceiling) osGNS.reconstruction) :
    DynamicVacuumSectorContinuumHandoff
      pin band ceiling existence osGNS :=
  DynamicVacuumSectorContinuumHandoff.ofExactLogVariations
    (physicalGapVariationOfMarginAndReciprocalSpacing
      family marginVariation reciprocalSpacingVariation)
    spacingTail projectiveOS spectralChannel exactRate

/-- The primitive variation compiler feeds the existing exact-log Cauchy
compiler without changing the completed family, observable pin, or spacing
tail. -/
def exactLogRateCauchy_of_primitiveComponents
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (marginVariation :
      SummableRationalStepVariation family.latticeMargin)
    (spacingVariation :
      SummableRationalStepVariation
        (fun scale => family.transferSpacing.spacing scale))
    (spacingFloor : Q')
    (spacingFloor_pos : (0 : Q') < spacingFloor)
    (spacingFloor_le :
      ∀ scale, spacingFloor ≤ family.transferSpacing.spacing scale)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) :=
  DynamicVacuumSectorObservablePin.exactLogRateCauchy
    pin band
    (physicalGapVariationOfPrimitiveComponents
      family marginVariation spacingVariation spacingFloor
      spacingFloor_pos spacingFloor_le)
    spacingTail

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler.physicalGapVariationOfPrimitiveComponents
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler.physicalGapVariationOfMarginAndReciprocalSpacing
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler.exactLogRateCauchy_of_marginAndReciprocalSpacing
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler.DynamicVacuumSectorContinuumHandoff.ofMarginAndReciprocalSpacing
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorPhysicalGapVariationCompiler.exactLogRateCauchy_of_primitiveComponents
