/-
# One observable-connected dynamic BF4 to Wilson mass-gap path

The analytic compilers for the dynamic BF4 family can be built independently,
but their contraction is meaningful only when every branch remains attached
to one completed family, one projective measure thread, one Wilson
reconstruction, and one transfer operator.  This module records precisely
that connected path for a raw moving-cube observable, then specializes it to
the off-ray adaptive producer.

The generic record is parameterized by one scheduled-rate limit.  In the
adaptive specialization that parameter is definitionally the exact
`physicalExponentialLimit` used by the raw continuum decay theorem.  The
projective/OS handoff consumes the selected Wilson datum's own `measureLinked`
field.  Independently, convergence of the same physical-gap stream to the
reconstruction logarithm and graph-norm convergence of every vacuum vector
compile to the all-vector bounded gap.  Vacuum stationarity allows iteration,
after which the raw observable inherits decay.

The causal direction is deliberate: the all-vector finite contraction and
graph-norm limit prove the operator gap; the connected observable is a
nontrivial downstream realization.  Its decay is not promoted backwards into
a gap for arbitrary vectors.

No adaptive family, variation certificate, projective/OS pin, Wilson GNS
datum, exact-rate convergence, graph-norm approximation, stationarity pin,
continuum Yang--Mills theory, or Clay conclusion is inhabited here.  No
`Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.RCStrictPositivity
open YMGap.Continuum.SummableRationalStepVariation
open YMGap.Continuum.TuranPositivity
open YMGap.Continuum.WilsonIteratedNormDecayHandoff
open YMGap.Continuum.WilsonMinimalBoundedMassGapHandoff

/-! ## 1. The generic connected compiler diagram -/

/-- One fully indexed residual diagram from a dynamic raw observable to the
selected Wilson mass-gap endpoint.

All fields are indexed by the same completed family and Wilson datum.  A later
specialization fixes `ratePower` to the adaptive producer's exact physical
exponential limit. -/
structure RawWilsonConnectedMassGapPath
    (family : DynamicVacuumSectorCompletedFamily 0)
    (raw : MovingCubeRawScheduledRepresentativeVariation family)
    (band : DynamicVacuumSectorPhysicalRateBand family)
    (gapVariation : SummableRationalStepVariation family.physicalGap)
    (ratePower : NormalizedMovingCubeSampledRatePowerLimit family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (W : WilsonSelectedOSGNSData H) : Type 3 where
  /-- The chosen raw observable survives cutoff removal at zero time. -/
  nontrivial : MovingCubeRawContinuumNontriviality family raw
  /-- The literal raw representatives are expectations of one fixed connected
  OS insertion on the selected Wilson measure thread. -/
  projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
    family raw H W.measureLinked
  /-- That exact connected insertion is represented by one vacuum-orthogonal
  completed Wilson state and its selected transfer autocorrelation. -/
  matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
    family raw H W projectiveOS
  /-- The same dynamic physical-gap stream converges to the exact logarithm
  of the selected Wilson reconstruction. -/
  exactRate : DynamicVacuumSectorWilsonExactRateHandoff
    family gapVariation W
  /-- Every selected Wilson vacuum vector is a graph-norm limit of finite BF4
  vectors using the exact scheduled-rate limit parameter. -/
  graphNorm : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
    family ratePower W
  /-- The selected transfer fixes its own vacuum, so its one-step gap can be
  iterated on the invariant vacuum complement. -/
  stationarity : WilsonVacuumStationarityPin W

namespace RawWilsonConnectedMassGapPath

/-! ## 2. Contract the all-vector branch -/

/-- The exact-rate and graph-norm branches compile to the minimal bounded
Wilson endpoint on the same selected datum. -/
def minimalBoundedMassGap
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W) :
    WilsonMinimalBoundedMassGap W :=
  DynamicVacuumSectorWilsonExactRateHandoff.compileWilsonMinimalBoundedMassGap
    band path.exactRate path.graphNorm

/-- Vacuum stationarity upgrades the minimal one-step endpoint to uniform
decay under every integer iterate of the same selected transfer. -/
def iteratedBoundedMassGap
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W) :
    WilsonIteratedBoundedMassGap W where
  boundedGap := path.minimalBoundedMassGap
  stationarity := path.stationarity

/-- The endpoint's physical rate is definitionally the limit selected by the
same dynamic physical-gap variation. -/
@[simp] theorem minimalBoundedMassGap_rate
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W) :
    path.minimalBoundedMassGap.rate = gapVariation.limit := rfl

/-- The connected endpoint retains the explicit positive floor supplied by
the physical rate band. -/
theorem physicalRate_posEv
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (_path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W) :
    PosEv gapVariation.limit :=
  physicalGapVariationLimit_posEv family band gapVariation

/-- The same positive physical rate is exactly the logarithm of the separator
used by the selected Wilson operator gap. -/
theorem physicalRate_equiv_selectedSeparatorExactLog
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W) :
    CReal.Equiv gapVariation.limit
      (exactLogGap W.reconstruction path.exactRate.positiveGapBound) :=
  path.exactRate.physicalGapLimit_equiv_exactLog

/-! ## 3. Contract the observable branch onto that endpoint -/

/-- The literal raw cutoff limit is the autocorrelation of its exact embedded
state under the same selected Wilson transfer carrying the all-vector gap. -/
theorem rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W)
    (time : Nat) :
    (rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
        time =
      W.wilson.toGNSData.gnsComplete.hilbert.cinner
        (BoundedTransferCalculus.Tpow W.timeTranslation.op time
          path.matrixCoefficient.gapState)
        path.matrixCoefficient.gapState :=
  path.matrixCoefficient.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
    time

/-- The exact connected observable remains nontrivial at continuum time zero. -/
theorem rawContinuum_zero_isPositive
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W) :
    RCIsPositive
      ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
        0) :=
  path.nontrivial.zero_isPositive

/-- The all-vector iterated Wilson gap implies squared decay of the exact raw
continuum channel.  This is the valid operator-to-observable direction. -/
theorem rawContinuumConnectedAutocorrelationSqDecay
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W)
    (time : Nat) :
    RCle
      (RCmul
        ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
          time)
        ((rawMovingCubeContinuumLimitOfVariation family raw).continuumConnectedAutocorrelation
          time))
      (RCmul
        (RCscale
          ((W.selectedSpectralData.gap.sep *
              W.selectedSpectralData.gap.sep) ^ time)
          (W.wilson.toGNSData.gnsComplete.hilbert.cinner
            path.matrixCoefficient.gapState
            path.matrixCoefficient.gapState))
        (W.wilson.toGNSData.gnsComplete.hilbert.cinner
          path.matrixCoefficient.gapState
          path.matrixCoefficient.gapState)) :=
  path.matrixCoefficient.rawContinuumConnectedAutocorrelationSqDecay
    path.iteratedBoundedMassGap time

end RawWilsonConnectedMassGapPath

/-! ## 4. Off-ray adaptive specialization -/

namespace DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

/-- The generic connected path specialized so its scheduled-rate parameter is
definitionally the physical exponential limit used by the adaptive raw
observable theorem. -/
abbrev AdaptiveRawWilsonConnectedMassGapPath
    (family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily)
    (raw : MovingCubeRawVariation family)
    (band : family.StrengthBand)
    (gapVariation : PhysicalGapRationalVariation family)
    (positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family)
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    (H : ContinuumYMExistence mu)
    (W : WilsonSelectedOSGNSData H) : Type 3 :=
  RawWilsonConnectedMassGapPath family.toCompletedFamily raw
    (family.physicalRateBand band) gapVariation
    (physicalExponentialLimit family positiveRatePower) H W

/-- The adaptive path retains the direct scheduled physical-exponential
bound, with the exact same rate-power limit consumed by its graph-norm field. -/
def adaptiveRawPhysicalExponentialPath
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W)
    (time : Nat) :=
  rawMovingCubePhysicalExponentialPath family raw path.nontrivial band
    gapVariation positiveRatePower time

/-- The adaptive path contracts to the same minimal bounded Wilson endpoint. -/
def adaptiveMinimalBoundedMassGap
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (path : AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W) :
    WilsonMinimalBoundedMassGap W :=
  path.minimalBoundedMassGap

end DynamicSpinCubeOffRayAdaptiveTransitionProductFamily

end YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath

/-! ## Axiom-dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.minimalBoundedMassGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.iteratedBoundedMassGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.physicalRate_equiv_selectedSeparatorExactLog
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.rawContinuumConnectedAutocorrelationSqDecay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveRawPhysicalExponentialPath
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveMinimalBoundedMassGap
