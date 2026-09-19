/-
# Exact-log cutoff removal from two explicit dynamic BF4 variation branches

The same-object dynamic BF4 continuum handoff previously retained a free
`rateCauchy` field for the exact physical logarithmic rates

    -log(q_j) / a_j.

This file replaces that opaque analytic field by two independently provable
inputs on the definitionally same completed family:

* summable two-sided rational step variation of the physical margin rate
  `(1-q_j)/a_j`; and
* an inverse-square tail for the physical spacing `a_j`.

The physical rate band supplies the eventual direct-log half-window.  The
first input controls the linear proxy; the second controls the quadratic
remainder `3(1-q_j)^2/a_j`.  The two branches rejoin in the existing
constructive-real proxy compiler, producing a global `ModCauchyEv` for the
full range-reduced exact logarithmic rate.  Spacing-to-zero then gives the
standard exact-rate cutoff removal, and a constructor injects the result into
the existing same-object continuum handoff.

This is not a proof that rational scheduled powers converge to the resulting
physical exponential.  It also does not inhabit an observable pin, either
variation input, the exact full-log ceiling, a projective measure, an OS
reconstruction, continuum Yang--Mills theory, or the Clay conclusion.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
import YMGap.Continuum.DirectLogQuadraticRemainder
import YMGap.Continuum.EventualCRealRationalProxyTracking
import YMGap.Continuum.FullLogRateInnerRegularity
import YMGap.Continuum.QuadraticRateErrorTailControl
import YMGap.Continuum.SummableRationalPositiveRatioDebtVariation
import YMGap.Continuum.SummableRationalStepVariation

namespace YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorContinuumRealization.DynamicVacuumSectorObservablePin
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorObservablePath
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.DirectLogQuadraticRemainder
open YMGap.Continuum.EventualCRealRationalProxyTracking
open YMGap.Continuum.ExactRateReconstructionHandoff
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.FullLogRateInnerRegularity
open YMGap.Continuum.MeasureLinkedOSReconstruction
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorFullLogComparison
open YMGap.Continuum.PhysicalSeparatorFullLogRate
open YMGap.Continuum.PhysicalSeparatorLinearTail
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.QuadraticRateErrorTailControl
open YMGap.Continuum.SummableRationalPositiveRatioDebtVariation
open YMGap.Continuum.SummableRationalStepVariation

local infix:50 " ≈ " => Q'.eqv

namespace DynamicVacuumSectorObservablePin

/-! ## 0. Forward primitive budgets meet the backward physical-gap input -/

/-- Primitive variation data for the exact physical gap of one completed
family.  The numerator and denominator budgets are deliberately independent;
the explicit positive spacing floor is the only noncollapse input needed by
the ratio compiler. -/
structure PhysicalGapPrimitiveVariationInput
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  spacingFloor : Q'
  spacingFloor_pos : (0 : Q') < spacingFloor
  spacingFloor_le : ∀ scale,
    spacingFloor ≤ family.transferSpacing.spacing scale
  marginVariation :
    SummableRationalStepVariation family.latticeMargin
  spacingVariation :
    SummableRationalStepVariation family.transferSpacing.spacing

namespace PhysicalGapPrimitiveVariationInput

/-- The two primitive step budgets compile to the exact same-family physical
gap stream.  No auxiliary rate or spacing schedule is introduced. -/
def toPhysicalGapVariation
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (input : PhysicalGapPrimitiveVariationInput family) :
    SummableRationalStepVariation family.physicalGap :=
  positiveRatioVariationOfPrimitiveComponents
    family.latticeMargin
    family.transferSpacing.spacing
    (fun scale => Q'.le_of_lt (family.latticeMargin_pos scale))
    family.transferSpacing.spacing_pos
    input.spacingVariation
    input.marginVariation
    input.spacingFloor
    input.spacingFloor_pos
    input.spacingFloor_le

end PhysicalGapPrimitiveVariationInput

/-! ## 1. Same-family logarithmic tail data -/

/-- The upper half of the physical rate band is exactly the linear margin
tail needed by the direct-log remainder estimate. -/
def exactLogLinearMarginTail
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family) :
    LinearMarginTail pin.toPhysicalSeparator family.transferSpacing where
  start := 0
  ceiling := band.ceiling
  margin_le := by
    intro scale _hscale
    change family.latticeMargin scale <=
      band.ceiling * family.transferSpacing.spacing scale
    exact band.upperRate scale

/-- The computed cutoff after which the same completed separator lies in the
direct logarithm half-window. -/
def exactLogRateStart
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family) : Nat :=
  (exactLogLinearMarginTail pin band).eventualStart
    family.transferSpacingToZero

/-- The rational margin proxy of the pinned physical separator is the exact
physical gap of the same completed transfer family. -/
theorem marginRate_eqv_physicalGap
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (scale : Nat) :
    (PhysicalSeparatorLogRate.marginRate pin.toPhysicalSeparator
      family.transferSpacing scale).eqv (family.physicalGap scale) := by
  change (family.physicalGap scale).eqv (family.physicalGap scale)
  exact Q'.eqv_refl _

/-! ## 2. Join the two analytic branches -/

/-- Summable physical-gap variation and inverse-square spacing variation
construct the exact full-log physical-rate Cauchy modulus.

The gap and spacing inputs can be proved independently, but both remain
indexed by `family`; their join cannot silently switch to an auxiliary rate or
spacing schedule. -/
def exactLogRateCauchy
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) := by
  let linear := exactLogLinearMarginTail pin band
  let start := exactLogRateStart pin band
  let approximation := eventualFullMassRateMarginProxyApproximation
    pin.toPhysicalSeparator family.transferSpacing start
    (linear.toEventualHalfWindow family.transferSpacingToZero)
  let gapApproximation := approximation.proxyEqv
    (fun scale _hscale => marginRate_eqv_physicalGap pin scale)
  let gapStep : RationalTwoSidedTailStep
      family.physicalGap gapVariation.variation start :=
    { step := fun scale _hscale => gapVariation.stepBound scale }
  let shiftedSpacing := spacingTail.shifted start
  let errorControl :=
    QuadraticRateErrorTailControl.LinearMarginTail.quadraticRateErrorTailControl
      linear start (by
        unfold start exactLogRateStart
        exact Nat.le_max_left _ _)
      (by simpa only [Nat.zero_add] using shiftedSpacing)
  exact gapApproximation.toModCauchyEv
    (fun scale => fullMassRateInnerRegularity
      pin.toPhysicalSeparator family.transferSpacing scale)
    gapStep
    gapVariation.variation_nonnegative
    (fun scale => quadraticRateError_nonneg
      pin.toPhysicalSeparator family.transferSpacing scale)
    (shiftedTailControl gapVariation.tailControl start)
    errorControl

/-- The constructive exact physical mass selected by the joined variation
data. -/
def exactLogRateLimit
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) : CReal :=
  CReal.completeLimitCauchy (fullRangeRateFamily pin).rate
    (exactLogRateCauchy pin band gapVariation spacingTail)

/-- The exact full-log cutoff rates converge to the constructed physical mass
with an explicit modulus. -/
theorem exactLogRateConverges
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ConvergesTo (fullRangeRateFamily pin).rate
      (exactLogRateLimit pin band gapVariation spacingTail) :=
  CReal.convergesTo_completeLimitCauchy (fullRangeRateFamily pin).rate
    (exactLogRateCauchy pin band gapVariation spacingTail)

/-! ## 3. Discharge the analytic field in the same-object continuum path -/

/-- With the independent finite exact-log ceiling supplied, the two variation
branches construct the entire exact-rate cutoff-removal record.  The positive
floor and finite ceiling then survive by the existing limit-order compiler. -/
def exactRateCutoffRemovalOfVariations
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (ceiling : FullRangeLogRateCeiling (fullRangeRateFamily pin))
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    ExactRateCutoffRemoval (exactCertificate pin band ceiling) :=
  (ExactRateLimitData.ofRateCauchy
    (exactLogRateCauchy pin band gapVariation spacingTail)).withSpacing
      family.transferSpacingToZero

/-- Constructor for the existing observable-connected continuum handoff with
its formerly opaque exact-rate Cauchy field derived from the two explicit
variation branches.  The projective/OS and reconstruction identifications
remain honest independent semantic inputs. -/
def DynamicVacuumSectorContinuumHandoff.ofExactLogVariations
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    {pin : DynamicVacuumSectorObservablePin family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {ceiling : FullRangeLogRateCeiling (fullRangeRateFamily pin)}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {existence : ContinuumYMExistence mu}
    {osGNS : MeasureLinkedOSGNSData existence}
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0)
    (projectiveOS : ProjectiveOSCorrelationHandoff pin.toPhysicalSeparator
      existence osGNS pin.physicalSampling)
    (spectralChannel :
      ProjectiveOSCorrelationHandoff.ReconstructionSpectralChannelHandoff
        projectiveOS osGNS.reconstruction)
    (exactRate : ExactRateReconstructionHandoff
      (exactCertificate pin band ceiling) osGNS.reconstruction) :
    DynamicVacuumSectorContinuumHandoff
      pin band ceiling existence osGNS where
  rateCauchy := exactLogRateCauchy pin band gapVariation spacingTail
  projectiveOS := projectiveOS
  spectralChannel := spectralChannel
  exactRate := exactRate

end DynamicVacuumSectorObservablePin

end YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.PhysicalGapPrimitiveVariationInput.toPhysicalGapVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogLinearMarginTail
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.marginRate_eqv_physicalGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogRateCauchy
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogRateConverges
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactRateCutoffRemovalOfVariations
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff.ofExactLogVariations
