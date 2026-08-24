/-
# Exact-log Euler evaluation for the adaptive Wilson rate

The dynamic scalar path already proves two separate facts about one cutoff
family.  First, its physical-gap stream converges to the exact logarithm of
the separator selected by the Wilson reconstruction.  Second, the scheduled
one-time rate powers and their upper Euler exponentials converge to one common
constructive limit.  The remaining analytic statement is the corresponding
logarithm/exponential evaluation: that the upper Euler exponential converges
to the square of that same rational separator.

This module isolates exactly that statement as
`DynamicVacuumSectorWilsonExactLogEulerEvaluation`.  The record is indexed by
the same family, gap variation, Wilson datum, and exact-rate handoff, so it
cannot be paired with an unrelated logarithm or separator.  All surrounding
work is compiled here:

* the upper rational exponents converge to the exact Wilson logarithmic
  exponent at every physical time;
* one upper-endpoint evaluation at time one identifies the already-constructed
  scheduled-power limit by uniqueness; and
* the literal scheduled finite rate stream consequently converges to the
  selected separator square required by the all-vector graph-norm compiler.

The Euler evaluation record is deliberately not inhabited.  In particular,
this file does not pretend that the repository already contains a general
constructive `exp (-log q) = q` theorem.  No adaptive family, evaluation,
graph-norm approximation, projective measure, continuum Yang--Mills theory,
or Clay conclusion is constructed here.  No `Classical.*`, choice,
`native_decide`, `sorry`, custom axiom, or noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerEulerCorridor
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerExponentLimitCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. The exact logarithmic exponent already selected by Wilson data -/

/-- The physical-time exponent obtained by replacing the dynamic gap limit by
the exact logarithm of the separator selected by the same Wilson datum. -/
def selectedWilsonExactPhysicalTimeExponent
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (positiveGapBound : PositiveTransferGapBound D.reconstruction)
    (time : Nat) : CReal :=
  CReal.mul
    (CReal.mul
      (exactLogGap D.reconstruction positiveGapBound)
      (CReal.add CReal.cone CReal.cone))
    (CReal.ofQ' (Q'.ofNat time))

/-- The actual upper Euler exponent stream converges to the exact Wilson
logarithmic exponent.  This is fully derived from the same-stream exact-rate
handoff; the exponential evaluation itself is the next, separate frontier. -/
theorem scheduledSquaredRateUpperExponent_converges_selectedWilsonExact
    (family : DynamicVacuumSectorCompletedFamily 0)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D)
    (time : Nat) :
    CReal.ConvergesTo
      (fun scale => CReal.ofQ'
        (scheduledSquaredRateUpperExponent family scale time))
      (selectedWilsonExactPhysicalTimeExponent
        D exactRate.positiveGapBound time) := by
  have hgap := exactRate.physicalGapLimit_equiv_exactLog
  have hinner : CReal.Equiv
      (CReal.mul gapVariation.limit (CReal.add CReal.cone CReal.cone))
      (CReal.mul
        (exactLogGap D.reconstruction exactRate.positiveGapBound)
        (CReal.add CReal.cone CReal.cone)) :=
    CReal.mul_congr_left hgap
  have hexponent : CReal.Equiv
      (scheduledSquaredRatePhysicalExponentLimit gapVariation time)
      (selectedWilsonExactPhysicalTimeExponent
        D exactRate.positiveGapBound time) :=
    CReal.mul_congr_left hinner
  exact CReal.convergesTo_limit_congr
    (scheduledSquaredRateUpperExponent_converges
      family band gapVariation time)
    hexponent

/-! ## 2. The one remaining exact-log Euler evaluation -/

/-- The minimal scalar analytic frontier: the upper Euler exponential built
from this exact-rate family converges at one physical-time unit to the square
of the separator selected by the same Wilson reconstruction.

The preceding theorem proves that the generating exponents converge to twice
the selected exact logarithmic gap.  Thus this field is the construction-
specific `exp (-2 * (-log sep)) = sep^2` evaluation, stated with an explicit
cutoff stream and convergence modulus rather than a free completed equality. -/
structure DynamicVacuumSectorWilsonExactLogEulerEvaluation
    (family : DynamicVacuumSectorCompletedFamily 0)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    (D : WilsonSelectedOSGNSData H)
    (_exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D) : Type 2 where
  upperEulerExponentialConverges : CReal.ConvergesTo
    (fun scale => scheduledSquaredRateUpperExponential family scale 1)
    (CReal.ofQ'
      (D.selectedSpectralData.gap.sep * D.selectedSpectralData.gap.sep))

namespace DynamicVacuumSectorWilsonExactLogEulerEvaluation

/-- An upper-endpoint identification compiles the exact-log Euler evaluation
to convergence of the literal scheduled finite one-time rate stream. -/
def toPhysicalTimeRateConvergence
    {family : DynamicVacuumSectorCompletedFamily 0}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family gapVariation D exactRate)
    (upperIdentification : CReal.ConvergesTo
      (fun scale => scheduledSquaredRateUpperExponential family scale 1)
      (ratePower.limitRepresentative 1)) :
    DynamicVacuumSectorWilsonPhysicalTimeRateConvergence
      family ratePower D where
  scheduledRateConverges :=
    CReal.convergesTo_limit_congr
      (ratePower.converges 1)
      (CReal.Equiv_of_limit_of_equal
        (fun scale => CReal.Equiv.refl
          (scheduledSquaredRateUpperExponential family scale 1))
        upperIdentification evaluation.upperEulerExponentialConverges)

/-- The same compiler followed by same-stream uniqueness gives the scalar pin
consumed by the three-way all-vector graph-norm join. -/
def toPhysicalTimeRateLimitPin
    {family : DynamicVacuumSectorCompletedFamily 0}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family gapVariation D exactRate)
    (upperIdentification : CReal.ConvergesTo
      (fun scale => scheduledSquaredRateUpperExponential family scale 1)
      (ratePower.limitRepresentative 1)) :
    DynamicVacuumSectorWilsonPhysicalTimeRateLimitPin
      family ratePower D :=
  DynamicVacuumSectorWilsonPhysicalTimeRateLimitPin.ofScheduledRateConvergence
    (evaluation.toPhysicalTimeRateConvergence upperIdentification)

end DynamicVacuumSectorWilsonExactLogEulerEvaluation

/-! ## 3. Specialize to the adaptive physical-exponential producer -/

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-- For the adaptive producer, the existing physical-exponential endpoint
identification supplies every input around the single exact-log Euler
evaluation. -/
def wilsonPhysicalTimeRateConvergenceOfExactLogEulerEvaluation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family.toCompletedFamily gapVariation D exactRate) :
    DynamicVacuumSectorWilsonPhysicalTimeRateConvergence
      family.toCompletedFamily
      (physicalExponentialLimit family positiveRatePower) D :=
  evaluation.toPhysicalTimeRateConvergence
    (physicalExponentialLimit_identification family
      band gapVariation positiveRatePower 1).1

/-- Rejoin the compiled scalar evaluation with the two independent all-vector
branches: a representative lift of the selected transfer and finite
graph-norm approximation through that lift. -/
def wilsonPhysicalTimeGraphNormLimitOfExactLogEulerEvaluation
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {D : WilsonSelectedOSGNSData H}
    {exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation D}
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family.toCompletedFamily gapVariation D exactRate)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift D)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily D transfer) :
    DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family.toCompletedFamily
      (physicalExponentialLimit family positiveRatePower) D :=
  DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.ofParallelConvergenceCompilers
    (wilsonPhysicalTimeRateConvergenceOfExactLogEulerEvaluation
      family band gapVariation positiveRatePower evaluation)
    transfer finite

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.scheduledSquaredRateUpperExponent_converges_selectedWilsonExact
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicVacuumSectorWilsonExactLogEulerEvaluation.toPhysicalTimeRateConvergence
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicVacuumSectorWilsonExactLogEulerEvaluation.toPhysicalTimeRateLimitPin
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeRateConvergenceOfExactLogEulerEvaluation
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.wilsonPhysicalTimeGraphNormLimitOfExactLogEulerEvaluation
