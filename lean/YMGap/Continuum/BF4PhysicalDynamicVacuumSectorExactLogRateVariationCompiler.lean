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
import YMGap.Continuum.SummableRationalReciprocalSpacingNoGo
import YMGap.Continuum.SummableRationalReciprocalStepVariation
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
open YMGap.Continuum.SummableRationalReciprocalSpacingNoGo
open YMGap.Continuum.SummableRationalReciprocalStepVariation
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

/-- The positive-floor primitive package is incompatible with the completed
family's spacing-to-zero modulus.  It is therefore a finite-regulator
interface only, not a possible continuum producer. -/
theorem noPhysicalGapPrimitiveVariationInput
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half)
    (input : PhysicalGapPrimitiveVariationInput family) :
    False := by
  exact noSummableReciprocalSpacingVariation
    family.transferSpacing family.transferSpacingToZero
    (reciprocal
      family.transferSpacing.spacing_pos
      input.spacingVariation
      input.spacingFloor
      input.spacingFloor_pos
      input.spacingFloor_le)

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

/-! ## 1a. A compatible minimal mass-calibration certificate -/

/-- A same-family physical mass calibration that is compatible with
spacing-to-zero: the rational physical gap is pointwise equivalent to one
fixed value.  This is deliberately weaker than a primitive reciprocal-spacing
floor (which the spacing-to-zero no-go rules out), but strong enough to supply
the exact summable variation needed by the logarithmic compiler. -/
structure ConstantPhysicalGapCalibration
    {half : Nat}
    (family : DynamicVacuumSectorCompletedFamily half) : Type 1 where
  value : Q'
  physicalGap_eqv : ∀ scale, family.physicalGap scale ≈ value

theorem ConstantPhysicalGapCalibration.value_pos
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (calibration : ConstantPhysicalGapCalibration family) :
    (0 : Q') < calibration.value := by
  have hmargin : (0 : Q') < family.latticeMargin 0 :=
    family.latticeMargin_pos 0
  have hspacing : (0 : Q') < family.transferSpacing.spacing 0 :=
    family.transferSpacing.spacing_pos 0
  have hgap : (0 : Q') < family.physicalGap 0 := by
    unfold DynamicVacuumSectorCompletedFamily.physicalGap
    exact Q'.divPos_pos _ _ hspacing hmargin
  exact Q'.pos_of_lt_of_le hgap
    (Q'.le_of_eqv (calibration.physicalGap_eqv 0))

/-- A constant physical-gap calibration carries zero same-family step
variation, using the canonical rational constant-stream compiler. -/
def ConstantPhysicalGapCalibration.toVariation
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (calibration : ConstantPhysicalGapCalibration family) :
    SummableRationalStepVariation family.physicalGap :=
  SummableRationalStepVariation.ofPointwiseEqvConstant
    family.physicalGap calibration.value calibration.physicalGap_eqv

/- A constant physical gap is already a two-sided physical-rate calibration:
   multiply its pointwise equality by the positive spacing and use the exact
   reciprocal presentation of `family.physicalGap`. -/
def ConstantPhysicalGapCalibration.toPhysicalRateBand
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (calibration : ConstantPhysicalGapCalibration family) :
    DynamicVacuumSectorPhysicalRateBand family where
  floor := calibration.value
  floor_pos := calibration.value_pos
  ceiling := calibration.value
  ceiling_pos := calibration.value_pos
  lowerRate := by
    intro scale
    have hgap : calibration.value ≤ family.physicalGap scale :=
      Q'.le_of_eqv (Q'.eqv_symm (calibration.physicalGap_eqv scale))
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      calibration.value (family.physicalGap scale)
      (family.transferSpacing.spacing scale) hgap
      (Q'.le_of_lt (family.transferSpacing.spacing_pos scale))
    have hcollapse : family.physicalGap scale *
        family.transferSpacing.spacing scale ≈ family.latticeMargin scale := by
      unfold DynamicVacuumSectorCompletedFamily.physicalGap
      exact Q'.divPos_mul_eqv _ _ _
    exact Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hcollapse)
  upperRate := by
    intro scale
    have hgap : family.physicalGap scale ≤ calibration.value :=
      Q'.le_of_eqv (calibration.physicalGap_eqv scale)
    have hscaled := Q'.mul_le_mul_of_nonneg_right
      (family.physicalGap scale) calibration.value
      (family.transferSpacing.spacing scale) hgap
      (Q'.le_of_lt (family.transferSpacing.spacing_pos scale))
    have hcollapse : family.latticeMargin scale ≈
        family.physicalGap scale * family.transferSpacing.spacing scale := by
      unfold DynamicVacuumSectorCompletedFamily.physicalGap
      exact Q'.eqv_symm (Q'.divPos_mul_eqv _ _ _)
    exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hcollapse) hscaled

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

/-- A constant same-family physical gap removes the last variation input from
the exact-log cutoff compiler.  The spacing tail remains explicit, and the
observable, physical-rate band, and completed carrier are unchanged. -/
def exactLogRateCauchyOfConstantPhysicalGap
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (calibration : ConstantPhysicalGapCalibration family)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) :=
  exactLogRateCauchy pin band calibration.toVariation spacingTail

namespace PhysicalGapPrimitiveVariationInput

/-! ## 2a. Primitive package to exact-log consumer -/

/-- The primitive same-family package feeds the exact-log Cauchy consumer
without changing the observable pin, rate band, or spacing tail. -/
def toExactLogRateCauchy
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (input : PhysicalGapPrimitiveVariationInput family)
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    CReal.ModCauchyEv ((fullRangeRateFamily pin).rate) :=
  exactLogRateCauchy pin band input.toPhysicalGapVariation spacingTail

end PhysicalGapPrimitiveVariationInput

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

/-- The constant-gap calibration compiles directly to exact cutoff removal on
the same completed physical family. -/
def exactRateCutoffRemovalOfConstantPhysicalGap
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (ceiling : FullRangeLogRateCeiling (fullRangeRateFamily pin))
    (calibration : ConstantPhysicalGapCalibration family)
    (spacingTail : InverseSquareSpacingTail family.transferSpacing 0) :
    ExactRateCutoffRemoval (exactCertificate pin band ceiling) :=
  exactRateCutoffRemovalOfVariations pin band ceiling
    calibration.toVariation spacingTail

/-! ## 3a. Backward direct-rate interface -/

/-- The backward-facing exact-rate interface for the same completed family.

This constructor deliberately accepts the missing analytic datum directly:
an eventual constructive-real Cauchy modulus for the exact full-log rate.
It discharges only the already-proved finite rate band and the independently
named spacing-to-zero modulus.  In particular, it does not manufacture a
physical-gap variation certificate, a projective measure, an OS
reconstruction, or a continuum mass gap.  The forward variation compiler
above remains the route that can eliminate this input once a genuine
same-family gap estimate is supplied. -/
def exactRateCutoffRemovalOfRateCauchy
    {half : Nat}
    {family : DynamicVacuumSectorCompletedFamily half}
    (pin : DynamicVacuumSectorObservablePin family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (ceiling : FullRangeLogRateCeiling (fullRangeRateFamily pin))
    (rateCauchy : CReal.ModCauchyEv ((fullRangeRateFamily pin).rate)) :
    ExactRateCutoffRemoval (exactCertificate pin band ceiling) :=
  (ExactRateLimitData.ofRateCauchy rateCauchy).withSpacing
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
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.noPhysicalGapPrimitiveVariationInput
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.PhysicalGapPrimitiveVariationInput.toExactLogRateCauchy
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogLinearMarginTail
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.marginRate_eqv_physicalGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration.toVariation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration.value_pos
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.ConstantPhysicalGapCalibration.toPhysicalRateBand
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogRateCauchyOfConstantPhysicalGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactRateCutoffRemovalOfConstantPhysicalGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogRateCauchy
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactLogRateConverges
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactRateCutoffRemovalOfVariations
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.exactRateCutoffRemovalOfRateCauchy
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicVacuumSectorExactLogRateVariationCompiler.DynamicVacuumSectorObservablePin.DynamicVacuumSectorContinuumHandoff.ofExactLogVariations
