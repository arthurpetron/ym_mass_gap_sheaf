/-
# A nonzero completed vacuum-complement face vector with a strict form bound

The explicit reflected bent-cube channel already contracts its same-object
connected face moment.  The variance bridge identifies the discarded source
normalization with the squared GNS norm of the centered face indicator.  This
file therefore places that concrete indicator in the completed physical GNS
space and proves the literal relative form estimate

```text
  <T v,v> <= q <v,v>,       0 <= q < 1.
```

The vector is genuinely vacuum orthogonal and has strictly positive rational
norm.  This is one completed vector at one explicit finite datum, not a dense
family, an operator gap, or a cutoff/volume/spacing-uniform statement.

Constructive contract: existing finite rational estimates, the explicit GNS
embedding, and quotient soundness only; no choice, `Classical`, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabCompletedFaceChannel

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCompletedCenteredFormGap
open YMGap.Continuum.BF4PhysicalCompletedMacroCorrelator
open YMGap.Continuum.BF4PhysicalMarkovGNSCompletion
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.CompactDualSlabObservableFaceSameObjectOSBridge
open YMGap.Continuum.CompactDualSlabObservableFaceVarianceBridge
open YMGap.Continuum.CompactDualSlabObservablePairedConnectedRetainedFraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.CompactDualSlabObservableReflectedPositiveChannelContraction
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabRetainedContraction

local infix:50 " ≈ " => Q'.eqv

/-- The literal lower-face indicator selected by the reflected bent channel. -/
abbrev reflectedBentFaceObservable : EdgeLabelling → Q' :=
  (slabPhysicalFacePositiveUnitObservable reflectedBentRootFaceId).value

/-- Its exact stationary-mean subtraction in the finite physical carrier. -/
abbrev reflectedBentCenteredFaceObservable : EdgeLabelling → Q' :=
  centralPhysicalCenteredObservable
    reflectedBentPhysicalData.coupling
    reflectedBentPhysicalData.coupling_nonnegative
    reflectedBentPhysicalData.cutoff
    reflectedBentPhysicalData.half
    reflectedBentFaceObservable

/-- The centered face indicator in the actual constructive-real GNS
completion. -/
def reflectedBentCompletedCenteredFaceVector :
    CentralPhysicalGNSCompletion
      reflectedBentPhysicalData.coupling
      reflectedBentPhysicalData.coupling_nonnegative
      reflectedBentPhysicalData.cutoff
      reflectedBentPhysicalData.half :=
  centralPhysicalCompletedObservable
    reflectedBentPhysicalData.coupling
    reflectedBentPhysicalData.coupling_nonnegative
    reflectedBentPhysicalData.cutoff
    reflectedBentPhysicalData.half
    reflectedBentCenteredFaceObservable

/-- Centering places the concrete face vector in the completed vacuum
complement. -/
theorem reflectedBentCompletedCenteredFaceVector_vacuumOrthogonal :
    CentralPhysicalCompletedVacuumOrthogonal
      reflectedBentPhysicalData.coupling
      reflectedBentPhysicalData.coupling_nonnegative
      reflectedBentPhysicalData.cutoff
      reflectedBentPhysicalData.half
      reflectedBentCompletedCenteredFaceVector := by
  exact centralPhysicalCompletedObservable_vacuumOrthogonal
    reflectedBentPhysicalData.coupling
    reflectedBentPhysicalData.coupling_nonnegative
    reflectedBentPhysicalData.cutoff
    reflectedBentPhysicalData.half
    reflectedBentCenteredFaceObservable
    (centralPhysicalCenteredObservable_meanZero
      reflectedBentPhysicalData.coupling
      reflectedBentPhysicalData.coupling_nonnegative
      reflectedBentPhysicalData.cutoff
      reflectedBentPhysicalData.half
      reflectedBentFaceObservable)

/-- The explicit retained channel gives the rational relative form estimate
on the centered face indicator. -/
theorem reflectedBentCenteredFaceForm_le_factor_mul_norm :
    slabPhysicalFaceSameObjectConnectedMarkovMoment
        reflectedBentPhysicalData reflectedBentRootFaceId ≤
      reflectedBentSameObjectContractionFactor *
        centralPhysicalWeightedInner
          reflectedBentPhysicalData.coupling
          reflectedBentPhysicalData.coupling_nonnegative
          reflectedBentPhysicalData.cutoff
          reflectedBentPhysicalData.half
          reflectedBentCenteredFaceObservable
          reflectedBentCenteredFaceObservable := by
  exact sameObjectConnectedMarkovMoment_le_factor_mul_centeredFaceNorm
    reflectedBentPhysicalData reflectedBentRootFaceId_lower
    reflectedBentReflectedPositiveChannel.contraction

/-- The completed coefficient is exactly the already identified same-object
connected moment. -/
theorem reflectedBentCompletedCenteredFaceCoefficient_eq :
    (centralPhysicalSmulGNS
      reflectedBentPhysicalData.coupling
      reflectedBentPhysicalData.coupling_nonnegative
      reflectedBentPhysicalData.cutoff
      reflectedBentPhysicalData.half).toGNSData.cinnerCompl
        (centralPhysicalCompletedMarkovTransfer
          reflectedBentPhysicalData.coupling
          reflectedBentPhysicalData.coupling_nonnegative
          reflectedBentPhysicalData.cutoff
          reflectedBentPhysicalData.half
          reflectedBentCompletedCenteredFaceVector)
        reflectedBentCompletedCenteredFaceVector =
      physicalConstantRC
        (slabPhysicalFaceSameObjectConnectedMarkovMoment
          reflectedBentPhysicalData reflectedBentRootFaceId) := by
  unfold reflectedBentCompletedCenteredFaceVector
  unfold centralPhysicalCompletedObservable
  rw [centralPhysicalCompletedMarkovTransfer_embed]
  exact Eq.trans
    (centralPhysicalCompletedObservable_inner
      reflectedBentPhysicalData.coupling
      reflectedBentPhysicalData.coupling_nonnegative
      reflectedBentPhysicalData.cutoff
      reflectedBentPhysicalData.half
      (centralPhysicalMarkovApply
        reflectedBentPhysicalData.coupling
        reflectedBentPhysicalData.coupling_nonnegative
        reflectedBentPhysicalData.cutoff
        reflectedBentPhysicalData.half
        reflectedBentCenteredFaceObservable)
      reflectedBentCenteredFaceObservable)
    (Quotient.sound
      (CReal.ofQ'_equiv_of_eqv
        (centralPhysicalCenteredFaceObservable_markovForm_eqv_sameObject
          reflectedBentPhysicalData reflectedBentRootFaceId)))

/-- The completed squared norm is the rational centered face norm. -/
theorem reflectedBentCompletedCenteredFaceNorm_eq :
    (centralPhysicalSmulGNS
      reflectedBentPhysicalData.coupling
      reflectedBentPhysicalData.coupling_nonnegative
      reflectedBentPhysicalData.cutoff
      reflectedBentPhysicalData.half).toGNSData.cinnerCompl
        reflectedBentCompletedCenteredFaceVector
        reflectedBentCompletedCenteredFaceVector =
      physicalConstantRC
        (centralPhysicalWeightedInner
          reflectedBentPhysicalData.coupling
          reflectedBentPhysicalData.coupling_nonnegative
          reflectedBentPhysicalData.cutoff
          reflectedBentPhysicalData.half
          reflectedBentCenteredFaceObservable
          reflectedBentCenteredFaceObservable) := by
  unfold reflectedBentCompletedCenteredFaceVector
  exact centralPhysicalCompletedObservable_inner
    reflectedBentPhysicalData.coupling
    reflectedBentPhysicalData.coupling_nonnegative
    reflectedBentPhysicalData.cutoff
    reflectedBentPhysicalData.half
    reflectedBentCenteredFaceObservable
    reflectedBentCenteredFaceObservable

private theorem physicalConstantRC_mul_eq_scale (factor value : Q') :
    physicalConstantRC (factor * value) =
      CReal.RCscale factor (physicalConstantRC value) := by
  apply Quotient.sound
  exact YMGap.Constructive.CRealAlg.ofQ'_mul factor value

/-- The promised literal completed relative form bound on this explicit
vacuum-orthogonal vector. -/
theorem reflectedBentCompletedCenteredFace_form_le_factor_mul_norm :
    CReal.RCle
      ((centralPhysicalSmulGNS
        reflectedBentPhysicalData.coupling
        reflectedBentPhysicalData.coupling_nonnegative
        reflectedBentPhysicalData.cutoff
        reflectedBentPhysicalData.half).toGNSData.cinnerCompl
          (centralPhysicalCompletedMarkovTransfer
            reflectedBentPhysicalData.coupling
            reflectedBentPhysicalData.coupling_nonnegative
            reflectedBentPhysicalData.cutoff
            reflectedBentPhysicalData.half
            reflectedBentCompletedCenteredFaceVector)
          reflectedBentCompletedCenteredFaceVector)
      (CReal.RCscale reflectedBentSameObjectContractionFactor
        ((centralPhysicalSmulGNS
          reflectedBentPhysicalData.coupling
          reflectedBentPhysicalData.coupling_nonnegative
          reflectedBentPhysicalData.cutoff
          reflectedBentPhysicalData.half).toGNSData.cinnerCompl
            reflectedBentCompletedCenteredFaceVector
            reflectedBentCompletedCenteredFaceVector)) := by
  rw [reflectedBentCompletedCenteredFaceCoefficient_eq,
    reflectedBentCompletedCenteredFaceNorm_eq,
    ← physicalConstantRC_mul_eq_scale]
  exact physicalConstantRC_le_of_rat
    reflectedBentCenteredFaceForm_le_factor_mul_norm

/-- The underlying rational norm is strictly positive, so the completed
channel is not a zero-vector form estimate in disguise. -/
theorem reflectedBentCenteredFaceNorm_pos :
    (0 : Q') <
      centralPhysicalWeightedInner
        reflectedBentPhysicalData.coupling
        reflectedBentPhysicalData.coupling_nonnegative
        reflectedBentPhysicalData.cutoff
        reflectedBentPhysicalData.half
        reflectedBentCenteredFaceObservable
        reflectedBentCenteredFaceObservable := by
  have hsource : (0 : Q') <
      slabObservablePairedConnectedSourceMass
        reflectedBentPhysicalData reflectedBentRootFaceId
        reflectedBentTargetFaceId :=
    slabObservablePairedConnectedSourceMass_pos
      reflectedBentPhysicalData reflectedBentPhysicalData_coupling_pos
      reflectedBentRootFaceId reflectedBentTargetFaceId
      reflectedBentPositiveChannelWitness
  have hpartition : (0 : Q') < reflectedBentPhysicalData.physicalPartition :=
    slabParametricKPhysicalPartition_pos
      reflectedBentPhysicalData.coupling_nonnegative
      reflectedBentPhysicalData.cutoff reflectedBentPhysicalData.extent
  have hnormalized : (0 : Q') <
      slabObservableNormalizedPairedSupportConnectedMass
        reflectedBentPhysicalData reflectedBentRootFaceId
        reflectedBentTargetFaceId := by
    unfold slabObservableNormalizedPairedSupportConnectedMass
    exact Q'.divPos_pos _ _ (Q'.mul_pos hpartition hpartition) hsource
  exact YMGap.Continuum.ClusteringImpliesGap.lt_of_lt_of_le hnormalized
    (slabObservableNormalizedPairedSupportConnectedMass_le_centeredFaceNorm
      reflectedBentPhysicalData reflectedBentTargetFaceId
      reflectedBentRootFaceId_lower)

#print axioms reflectedBentCompletedCenteredFaceVector_vacuumOrthogonal
#print axioms reflectedBentCenteredFaceForm_le_factor_mul_norm
#print axioms reflectedBentCompletedCenteredFaceCoefficient_eq
#print axioms reflectedBentCompletedCenteredFace_form_le_factor_mul_norm
#print axioms reflectedBentCenteredFaceNorm_pos

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabCompletedFaceChannel
