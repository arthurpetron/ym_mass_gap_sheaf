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
import YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff
import YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff
import YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler
import YMGap.Constructive.CRealArtanhEulerPolynomialAnchor

namespace YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.CReal
open YMGap.Constructive.CRealArtanhEulerRatio
open YMGap.Constructive.CRealArtanhEulerGeometricAnchor
open YMGap.Constructive.CRealArtanhEulerPolynomialAnchor
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveNormalizedMovingCubeRationalVariationPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptivePhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawPhysicalExponentialPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler
open YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveWilsonExactLogEulerEvaluationCompiler.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorCompletedFamily
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorNormalizedMovingCubeVariationCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeContinuumDecayCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeNontrivialityCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeProjectiveOSCorrelationHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorRawMovingCubeWilsonGNSHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorSameObjectRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRCChannel
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorScheduledRatePowerPhysicalExponentialCompiler
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonExactRateHandoff
open YMGap.Continuum.BF4PhysicalDynamicVacuumSectorWilsonGraphNormLimitCompiler
open YMGap.Continuum.BF4PhysicalSelectedVacuumMeanConvergence
open YMGap.Continuum.ContinuumMeasure
open YMGap.Continuum.FourDExistence
open YMGap.Continuum.OSExactLogGap
open YMGap.Continuum.PhysicalSeparator
open YMGap.Continuum.PhysicalSeparatorContinuumRealization
open YMGap.Continuum.PhysicalSeparatorLogRate
open YMGap.Continuum.ProjectiveOSCorrelationHandoff
open YMGap.Continuum.ProjectiveWilsonConnectedDecayHandoff
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
  /-- The selected vacuum is the embedded constant observable and is fixed by
  the completed transfer.  This is the smallest concrete-vacuum datum needed
  to iterate the operator gap; no carrier-level `tau one` law is required. -/
  vacuumPin : WilsonDenseUnitStationaryVacuumPin W

namespace RawWilsonConnectedMassGapPath

/-! ## 2. Compile the finite nontriviality source -/

/-- Constructor for the connected path in which raw continuum nontriviality is
derived from one cutoff-independent lower norm floor on the exact finite
moving-cube channel.  Every other semantic field remains explicit. -/
def ofUniformNormFloor
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation W)
    (graphNorm : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower W)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W where
  nontrivial := MovingCubeRawContinuumNontriviality.ofUniformNormFloor uniform
  projectiveOS := projectiveOS
  matrixCoefficient := matrixCoefficient
  exactRate := exactRate
  graphNorm := graphNorm
  vacuumPin := vacuumPin

/-- The same finite-source constructor with the all-vector graph-norm frontier
split into its three independently buildable branches: scalar rate pin,
representative transfer lift, and finite graph approximation. -/
def ofUniformNormFloorAndParallelGraphNormCompilers
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation W)
    (rateLimit : DynamicVacuumSectorWilsonPhysicalTimeRateLimitPin
      family ratePower W)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W :=
  ofUniformNormFloor uniform projectiveOS matrixCoefficient exactRate
    (DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.ofParallelCompilers
      rateLimit transfer finite)
    vacuumPin

/-- The parallel graph-norm constructor with its scalar branch stated as
convergence of the actual scheduled finite rate stream to the selected Wilson
separator square. -/
def ofUniformNormFloorAndParallelGraphNormConvergenceCompilers
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation W)
    (rate : DynamicVacuumSectorWilsonPhysicalTimeRateConvergence
      family ratePower W)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W :=
  ofUniformNormFloor uniform projectiveOS matrixCoefficient exactRate
    (DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit.ofParallelConvergenceCompilers
      rate transfer finite)
    vacuumPin

/-- Reuse an existing rational projective OS handoff on the raw connected
path.  The only additional semantic input is the exact identification of the
literal completed raw representative with that handoff's fixed sampled gap
observable. -/
def ofUniformNormFloorAndProjectiveOSCorrelationHandoff
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (projective : ProjectiveOSCorrelationHandoff
      P H W.measureLinked sampling)
    (sameObject : RawMovingCubeSampledGapCorrelationIdentification
      family raw projective)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family raw H W
        (RawMovingCubeProjectiveOSCorrelationHandoff.ofProjectiveOSCorrelationHandoff
          projective sameObject))
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation W)
    (graphNorm : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower W)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W :=
  ofUniformNormFloor uniform
    (RawMovingCubeProjectiveOSCorrelationHandoff.ofProjectiveOSCorrelationHandoff
      projective sameObject)
    matrixCoefficient exactRate graphNorm vacuumPin

/-- Reuse both the existing rational projective OS semantics and its selected
Wilson matrix-coefficient pin.  The dynamic raw path contributes only its
uniform nontriviality floor and literal same-object representative adapter. -/
def ofUniformNormFloorAndProjectiveWilsonOSMatrixCoefficientPin
    {family : DynamicVacuumSectorCompletedFamily 0}
    {raw : MovingCubeRawScheduledRepresentativeVariation family}
    {band : DynamicVacuumSectorPhysicalRateBand family}
    {gapVariation : SummableRationalStepVariation family.physicalGap}
    {ratePower : NormalizedMovingCubeSampledRatePowerLimit family}
    {P : PhysicalSeparator}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    {A : PhysicalSpacing}
    {sampling : PhysicalSeparationSampling A}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family))
    (projective : ProjectiveOSCorrelationHandoff
      P H W.measureLinked sampling)
    (sameObject : RawMovingCubeSampledGapCorrelationIdentification
      family raw projective)
    (matrixCoefficient : ProjectiveWilsonOSMatrixCoefficientPin projective W)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family gapVariation W)
    (graphNorm : DynamicVacuumSectorWilsonPhysicalTimeGraphNormLimit
      family ratePower W)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    RawWilsonConnectedMassGapPath family raw band gapVariation
      ratePower H W :=
  ofUniformNormFloorAndProjectiveOSCorrelationHandoff uniform projective
    sameObject
    (RawMovingCubeWilsonMatrixCoefficientPin.ofProjectiveWilsonOSMatrixCoefficientPin
      matrixCoefficient)
    exactRate graphNorm vacuumPin

/-! ## 3. Contract the all-vector branch -/

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
  stationarity := path.vacuumPin.stationarity

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

/-! ## 4. Contract the observable branch onto that endpoint -/

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

/-- The exact embedded observable state is orthogonal to the physically
identified dense constant vacuum, not merely to an abstract unnamed vector. -/
theorem gapState_orthogonal_denseUnit
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
    W.wilson.toGNSData.gnsComplete.hilbert.cinner
        path.matrixCoefficient.gapState
        (GNSQuotient.embedV W.wilson.toGNSData H.os_axioms.A.one) =
      RCzero := by
  have h := path.matrixCoefficient.gapState_vacPerp
  change W.wilson.toGNSData.gnsComplete.hilbert.cinner
      path.matrixCoefficient.gapState W.timeTranslation.op.vacuum =
    RCzero at h
  rw [path.vacuumPin.vacuumPinned] at h
  exact h

/-- Zero-time nontriviality is exactly strict positivity of the norm square of
the same completed Wilson state used in the connected matrix coefficient. -/
theorem gapState_norm_isPositive
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
      (W.wilson.toGNSData.gnsComplete.hilbert.cinner
        path.matrixCoefficient.gapState
        path.matrixCoefficient.gapState) := by
  have h := path.rawContinuum_zero_isPositive
  rw [path.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient 0] at h
  simpa [BoundedTransferCalculus.Tpow] using h

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

/-! ## 5. Off-ray adaptive specialization -/

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

/-- Build the adaptive connected path with the scalar all-vector branch
reduced to the construction-specific exact-log Euler evaluation.  The
evaluation is compiled to literal scheduled-rate convergence and then joined
with the representative transfer lift and finite graph approximation. -/
def adaptivePathOfExactLogEulerEvaluationCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (evaluation : DynamicVacuumSectorWilsonExactLogEulerEvaluation
      family.toCompletedFamily gapVariation W exactRate)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  RawWilsonConnectedMassGapPath.ofUniformNormFloor
    uniform projectiveOS matrixCoefficient exactRate
    (wilsonPhysicalTimeGraphNormLimitOfExactLogEulerEvaluation
      family band gapVariation positiveRatePower evaluation transfer finite)
    vacuumPin

/-- The same connected capstone with the dynamic-family scalar certificate
contracted to a static canonical Wilson exact-log evaluator.  The dynamic
Euler stream is now connected by the proved common-exponent continuity
compiler, so the inverse evaluator can be built independently of the adaptive
cutoff producer. -/
def adaptivePathOfCanonicalWilsonEvaluationCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (evaluation : WilsonCanonicalExactLogEulerEvaluation
      W exactRate.positiveGapBound)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  RawWilsonConnectedMassGapPath.ofUniformNormFloor
    uniform projectiveOS matrixCoefficient exactRate
    (wilsonPhysicalTimeGraphNormLimitOfCanonicalWilsonEvaluation
      family band gapVariation positiveRatePower evaluation transfer finite)
    vacuumPin

/-- The connected capstone with the static scalar branch expanded into its
two independent analytic atoms.  The dyadic and reduced-mantissa evaluators
join algebraically before the resulting canonical evaluator is transported
through the dynamic schedule. -/
def adaptivePathOfAtomicWilsonEvaluationCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (dyadic : DyadicLogSquareEulerEvaluation
      (gapBinExp W.reconstruction exactRate.positiveGapBound).k)
    (mantissa : MantissaLogSquareEulerEvaluation
      (gapMantissa W.reconstruction exactRate.positiveGapBound)
      (gapMantissaPlusOne_pos W.reconstruction exactRate.positiveGapBound)
      (gapMantissa_lt_one W.reconstruction exactRate.positiveGapBound)
      (gapMantissa_window W.reconstruction exactRate.positiveGapBound))
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfCanonicalWilsonEvaluationCompilers
    uniform projectiveOS matrixCoefficient exactRate
    (WilsonCanonicalExactLogEulerEvaluation.ofAtomicEvaluations
      W exactRate.positiveGapBound dyadic mantissa)
    transfer finite vacuumPin

/-- The connected capstone after collapsing the entire dyadic evaluator family
to one universal exponent-one seed.  The only reconstruction-dependent scalar
input left here is the reduced mantissa evaluation. -/
def adaptivePathOfDyadicOneAndMantissaEvaluationCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (dyadicOne : DyadicLogSquareEulerEvaluation 1)
    (mantissa : MantissaLogSquareEulerEvaluation
      (gapMantissa W.reconstruction exactRate.positiveGapBound)
      (gapMantissaPlusOne_pos W.reconstruction exactRate.positiveGapBound)
      (gapMantissa_lt_one W.reconstruction exactRate.positiveGapBound)
      (gapMantissa_window W.reconstruction exactRate.positiveGapBound))
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfCanonicalWilsonEvaluationCompilers
    uniform projectiveOS matrixCoefficient exactRate
    (WilsonCanonicalExactLogEulerEvaluation.ofDyadicOneAndMantissa
      W exactRate.positiveGapBound dyadicOne mantissa)
    transfer finite vacuumPin

/-- The connected capstone with the complete scalar inverse branch contracted
to one uniform direct-window compiler.  Its half specialization generates the
entire dyadic family, and its Wilson-mantissa specialization supplies the
remaining atomic evaluator. -/
def adaptivePathOfDirectWindowEvaluationCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : DirectWindowLogSquareEulerCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfCanonicalWilsonEvaluationCompilers
    uniform projectiveOS matrixCoefficient exactRate
    (WilsonCanonicalExactLogEulerEvaluation.ofDirectWindowCompiler
      W exactRate.positiveGapBound scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone with the scalar branch reduced to the universal
negative-window artanh/Euler compiler.  Exact Mobius inversion first contracts
that family-independent analytic witness to the direct-log compiler; all
subsequent dyadic, Wilson, graph-norm, and observable joins are unchanged. -/
def adaptivePathOfArtanhEvaluationCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : NegativeWindowArtanhSquareEulerCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfDirectWindowEvaluationCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (directWindowLogSquareEulerCompilerOfArtanh scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone with the scalar branch reduced to the smallest
current analytic input: one positive-window, one-copy artanh/Euler inverse
compiler.  Oddness and squaring are generated by proved constructors before
the unchanged Wilson and observable joins. -/
def adaptivePathOfPositiveArtanhEvaluationCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfDirectWindowEvaluationCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (directWindowLogSquareEulerCompilerOfPositiveArtanh scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by an explicit one-index pivot certificate.
The computed `ExpNeg.Mexp` cutoff discharges the inner exponential
approximation, so the remaining scalar producer controls only the outer
artanh stage at that pivot. -/
def adaptivePathOfPositiveArtanhPivotCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerPivotCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhEvaluationCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerCompilerOfPivot scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by the denominator-cleared scalar frontier.
Its only open artanh estimate is the rational cross-multiplied defect
`|(1+z)E-(1-z)| <= q(1+z)` at one computed pivot.  The proved constructive
division lemma recovers the ratio comparison before the unchanged convergence,
Wilson, graph-norm, and observable compilers are applied. -/
def adaptivePathOfPositiveArtanhClearedDefectCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerClearedDefectCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPivotCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPivotCompilerOfClearedDefect scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by one fully computed scalar anchor per
tolerance.  Explicit outer artanh stability and finite exponential response
propagate that single division-free rational defect to all later stages before
the unchanged Wilson and same-object observable compilers are applied. -/
def adaptivePathOfPositiveArtanhSingleAnchorCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerSingleAnchorCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhEvaluationCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerCompilerOfSingleAnchor scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by the finite geometric-polynomial anchor.
The polynomial residual is proved internally; the only scalar input compares
two finite cleared defects at computed artanh, Euler, and polynomial indices. -/
def adaptivePathOfPositiveArtanhGeometricAnchorCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerGeometricAnchorCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhSingleAnchorCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerSingleAnchorCompilerOfGeometricAnchor
      scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by the direct finite Euler-value versus
geometric-polynomial comparison.  Every other analytic, Wilson, operator, and
same-object observable compiler is unchanged. -/
def adaptivePathOfPositiveArtanhGeometricValueAnchorCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerGeometricValueAnchorCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhGeometricAnchorCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerGeometricAnchorCompilerOfValueAnchor
      scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by the coefficient-only polynomial anchor.
Exact polynomial semantics and the window majorization are proved internally;
the sole scalar input is a weighted coefficient inequality at the computed
finite indices. -/
def adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerPolynomialCoefficientCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhGeometricValueAnchorCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerGeometricValueAnchorCompilerOfPolynomial
      scalarInverse)
    transfer finite vacuumPin

/-- The same connected capstone with an executable Boolean coefficient check
as its narrowest scalar input. -/
def adaptivePathOfPositiveArtanhPolynomialCheckedCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerPolynomialCheckedCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfChecked
      scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by the separated exact-prefix and weighted-tail
coefficient compiler. -/
def adaptivePathOfPositiveArtanhPolynomialPrefixTailCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerPolynomialPrefixTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfPrefixTail
      scalarInverse)
    transfer finite vacuumPin

/-- The observable-connected capstone after the scalar frontier is split into
two independent ribs: formal coefficient cancellation and analytic control of
the remaining tail.  They rejoin at the computed prefix/tail interface, then
feed the same scalar inverse, Wilson observable, OS reconstruction, transfer
operator, and vacuum sector as every other capstone adapter in this file. -/
def adaptivePathOfPositiveArtanhPolynomialFormalAndTailCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (formal : PositiveArtanhEulerPolynomialFormalCoefficientCertificate)
    (scalarTail : PositiveWindowArtanhEulerPolynomialFullTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFormalAndTail
      formal scalarTail)
    transfer finite vacuumPin

/-- The stronger connected adapter after Euler valuation has eliminated the
moving inner truncation from the formal rib.  The stabilized coefficient
certificate and analytic tail still rejoin before entering the unchanged
same-object Wilson/OS path. -/
def adaptivePathOfPositiveArtanhPolynomialStableAndTailCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (stable : PositiveArtanhEulerPolynomialStableCoefficientCertificate)
    (scalarTail : PositiveWindowArtanhEulerPolynomialFullTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfStableAndTail
      stable scalarTail)
    transfer finite vacuumPin

/-- The connected adapter after both the Euler pivot and geometric degree
have been discharged internally.  The only algebraic scalar input is the
stage/index target recurrence; it joins the same analytic tail and then enters
the unchanged observable path. -/
def adaptivePathOfPositiveArtanhPolynomialTargetAndTailCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (target : PositiveArtanhEulerPolynomialTargetCoefficientCertificate)
    (scalarTail : PositiveWindowArtanhEulerPolynomialFullTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfTargetAndTail
      target scalarTail)
    transfer finite vacuumPin

/-- The connected adapter after the formal branch has contracted to one local
stabilized-coefficient successor recurrence.  Its proved seeds generate the
stage/index target before it rejoins the unchanged analytic tail and
same-object observable path. -/
def adaptivePathOfPositiveArtanhPolynomialRecurrenceAndTailCompilers
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (recurrence :
      PositiveArtanhEulerPolynomialStableRecurrenceCertificate)
    (scalarTail : PositiveWindowArtanhEulerPolynomialFullTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfRecurrenceAndTail
      recurrence scalarTail)
    transfer finite vacuumPin

/-- The formal Euler/artanh coefficient branch is now entirely internal.
Only the analytic full-tail compiler remains at the scalar join, while the
raw Wilson observable and every OS/transfer input stay unchanged. -/
def adaptivePathOfPositiveArtanhPolynomialFullTailCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarTail : PositiveWindowArtanhEulerPolynomialFullTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfFullTail
      scalarTail)
    transfer finite vacuumPin

/-- The computed cancellation cutoff and its geometric radius decay are now
internal.  The sole scalar input is the fixed shifted-tail-size bound, while
the dynamic family, raw observable, Wilson reconstruction, transfer lift,
finite graph approximation, and vacuum pin remain definitionally unchanged. -/
def adaptivePathOfPositiveArtanhPolynomialResidualTailSizeCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarTail :
      PositiveWindowArtanhEulerPolynomialResidualTailSizeCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialFullTailCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialFullTailCompilerOfResidualTailSize
      scalarTail)
    transfer finite vacuumPin

/-- The exact first uncancelled Euler/geometric boundary coefficient is now
internal.  A size-three bound on the strictly later tail reaches the same
connected Wilson observable and all of the same reconstruction data. -/
def adaptivePathOfPositiveArtanhPolynomialPostBoundaryTailSizeCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarTail :
      PositiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialResidualTailSizeCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialResidualTailSizeCompilerOfPostBoundary
      scalarTail)
    transfer finite vacuumPin

/-- The geometric comparison has no support in the remaining tail.  An
Euler-only tail compiler therefore reaches the same connected raw Wilson
observable and reconstruction chain. -/
def adaptivePathOfPositiveArtanhPolynomialEulerOnlyTailSizeCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarTail :
      PositiveWindowArtanhEulerPolynomialEulerOnlyTailSizeCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialPostBoundaryTailSizeCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialPostBoundaryTailSizeCompilerOfEulerOnly
      scalarTail)
    transfer finite vacuumPin

/-- The connected capstone after the constant coefficient has been cancelled
internally.  The scalar input now contains only the weighted tail obligation;
the observable, Wilson reconstruction, and operator inputs are unchanged. -/
def adaptivePathOfPositiveArtanhPolynomialOneTailCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerPolynomialOneTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfOneTail
      scalarInverse)
    transfer finite vacuumPin

/-- The connected capstone fed by the quadratic-radius tail after the
constant and linear coefficient cancellations are proved internally. -/
def adaptivePathOfPositiveArtanhPolynomialTwoTailCompiler
    {family : DynamicSpinCubeOffRayAdaptiveTransitionProductFamily}
    {raw : MovingCubeRawVariation family}
    {band : family.StrengthBand}
    {gapVariation : PhysicalGapRationalVariation family}
    {positiveRatePower : PositiveMovingCubeRatePowerRationalVariation family}
    {M : Nat -> Type} {mu : ContinuumMeasure M}
    {H : ContinuumYMExistence mu}
    {W : WilsonSelectedOSGNSData H}
    (uniform : DynamicVacuumSectorUniformRCNormFloor
      (centralPhysicalDynamicMovingCubeRCChannel family.toCompletedFamily))
    (projectiveOS : RawMovingCubeProjectiveOSCorrelationHandoff
      family.toCompletedFamily raw H W.measureLinked)
    (matrixCoefficient : RawMovingCubeWilsonMatrixCoefficientPin
      family.toCompletedFamily raw H W projectiveOS)
    (exactRate : DynamicVacuumSectorWilsonExactRateHandoff
      family.toCompletedFamily gapVariation W)
    (scalarInverse : PositiveWindowArtanhEulerPolynomialTwoTailCompiler)
    (transfer : WilsonPhysicalTimeRepresentativeTransferLift W)
    (finite : DynamicVacuumSectorWilsonPhysicalTimeFiniteGraphApproximation
      family.toCompletedFamily W transfer)
    (vacuumPin : WilsonDenseUnitStationaryVacuumPin W) :
    AdaptiveRawWilsonConnectedMassGapPath family raw band gapVariation
      positiveRatePower H W :=
  adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
    uniform projectiveOS matrixCoefficient exactRate
    (positiveWindowArtanhEulerPolynomialCoefficientCompilerOfTwoTail
      scalarInverse)
    transfer finite vacuumPin

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
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.ofUniformNormFloor
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.ofUniformNormFloorAndParallelGraphNormCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.ofUniformNormFloorAndParallelGraphNormConvergenceCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.ofUniformNormFloorAndProjectiveOSCorrelationHandoff
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.ofUniformNormFloorAndProjectiveWilsonOSMatrixCoefficientPin
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.minimalBoundedMassGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.iteratedBoundedMassGap
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.physicalRate_equiv_selectedSeparatorExactLog
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.rawContinuumConnectedAutocorrelation_eq_matrixCoefficient
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.gapState_orthogonal_denseUnit
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.gapState_norm_isPositive
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.RawWilsonConnectedMassGapPath.rawContinuumConnectedAutocorrelationSqDecay
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveRawPhysicalExponentialPath
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfExactLogEulerEvaluationCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfCanonicalWilsonEvaluationCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfAtomicWilsonEvaluationCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfDyadicOneAndMantissaEvaluationCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfDirectWindowEvaluationCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfArtanhEvaluationCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhEvaluationCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPivotCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhClearedDefectCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhSingleAnchorCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhGeometricAnchorCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhGeometricValueAnchorCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialCoefficientCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialCheckedCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialPrefixTailCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialFormalAndTailCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialStableAndTailCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialTargetAndTailCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialRecurrenceAndTailCompilers
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialFullTailCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialResidualTailSizeCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialPostBoundaryTailSizeCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialEulerOnlyTailSizeCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialOneTailCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptivePathOfPositiveArtanhPolynomialTwoTailCompiler
#print axioms
  YMGap.Continuum.BF4PhysicalDynamicSpinCubeOffRayAdaptiveRawWilsonConnectedMassGapPath.DynamicSpinCubeOffRayAdaptiveTransitionProductFamily.adaptiveMinimalBoundedMassGap
