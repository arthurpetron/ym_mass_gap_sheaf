/-
# Component endpoints of active accepted tilted-row response pairs

The active response carrier supplies a changed coarse target coordinate in a
source packet-disagreement face.  For each of the accepted left and right
support-swap row pairs, this file computes a fine dyadic preimage selected by
the true finite support-mask search.  The returned structure records that the
fine face lies in the target-rooted physical source component.

The other endpoint comes from the observable.  Separate constructive
specializations show that an active root or target event changes that exact
coarse coordinate, while an active joint event returns one of the two marked
coordinates together with its inequality witness.

These are endpoint certificates, not a connecting path or an activity bound.
No volume-uniform response estimate, continuum construction, or mass gap is
asserted.

Constructive contract: explicit structures, finite Boolean search, and exact
decidable reasoning only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualPhysicalConnectedCovarianceActualFourCellPositivePaths
open YMGap.Continuum.CompactDualSlabObservableFaceEventLaw
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4CanonicalTwoBlockConnectedResidueCarrier
open YMGap.Continuum.Z4DyadicBinarySourceSupportSwapPacketComponent
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAntisymmetricPair
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginOccupationSwapTransport
open YMGap.Continuum.Z4DyadicSpinFourXorAssembly
open YMGap.Continuum.Z4DyadicWholeSlabComponentRawFaceLocality
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Accepted source-component endpoint certificates -/

/-- A changed coarse target coordinate together with a fine dyadic preimage
in the target-rooted physical component of the accepted source pair. -/
structure AcceptedActivePairComponentEndpoint
    (S : SlabScalePair) (first second : EdgeLabelling)
    (sourcePair targetPair : EdgeLabelling × EdgeLabelling)
    (targetFaceId : Nat) : Type where
  coarseFaceId : Nat
  coarse_mem_sourceDisagreement :
    coarseFaceId ∈
      finePacketTotalDisagreementCoarseFaces S first second
  targetStates_ne : targetPair.1 coarseFaceId ≠ targetPair.2 coarseFaceId
  fineFaceId : Nat
  fine_mem_dyadicPacket :
    fineFaceId ∈ dyadicCoarseFaceFineFaceIds S coarseFaceId
  fine_mem_targetComponent :
    fineFaceId ∈ slabTwoReplicaTargetSupportComponent
      S.fine.extent sourcePair.1 sourcePair.2 targetFaceId

/-- Every active accepted left-versus-swapped-left row pair returns a fine
component endpoint carrying a changed coarse target coordinate. -/
def acceptedLeftActivePairComponentEndpoint
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S
      (fineCouplingAcceptedSeparatedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      event targetPair = true) :
    AcceptedActivePairComponentEndpoint S
      (fineCouplingAcceptedSeparatedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
      targetPair targetFaceId := by
  let first :=
    (fineCouplingAcceptedSeparatedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId source).1
  let second :=
    (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source).1
  let sourcePair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let coarseWitness := activePairTargetDisagreementWitness
    S first second event targetPair hactive
  have haccepted : coarseWitness.1 ∈
      fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source := by
    simpa only
      [fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces,
        first, second] using coarseWitness.2.1
  have hgeneric : coarseWitness.1 ∈
      fineCouplingPhysicalSupportSwapLeftPacketTotalDisagreementFaces
        S targetFaceId sourcePair := by
    rw [← fineCouplingAcceptedSeparatedLeftPacketTotalDisagreementFaces_eq
      S hfineCoupling rootFaceId targetFaceId htarget source]
    exact haccepted
  have htouch := mem_leftPacketTotalDisagreementFaces_implies_touch
    S targetFaceId sourcePair hgeneric
  let fineWitness := listAnyTrueWitness
    (dyadicCoarseFaceFineFaceIds S coarseWitness.1)
    (fineCouplingPhysicalSupportSwapMask S targetFaceId sourcePair)
    htouch
  refine
    { coarseFaceId := coarseWitness.1
      coarse_mem_sourceDisagreement := coarseWitness.2.1
      targetStates_ne := coarseWitness.2.2
      fineFaceId := fineWitness.1
      fine_mem_dyadicPacket := fineWitness.2.1
      fine_mem_targetComponent := ?_ }
  have hmask := fineWitness.2.2
  unfold fineCouplingPhysicalSupportSwapMask
    slabTwoReplicaSupportSwapMask at hmask
  exact of_decide_eq_true hmask

/-- The analogous explicit endpoint for an active accepted
right-versus-swapped-right row pair. -/
def acceptedRightActivePairComponentEndpoint
    (S : SlabScalePair) (hfineCoupling : (0 : Q') < S.fine.coupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (event : EdgeLabelling → Bool)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S
      (fineCouplingAcceptedSeparatedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      event targetPair = true) :
    AcceptedActivePairComponentEndpoint S
      (fineCouplingAcceptedSeparatedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
      targetPair targetFaceId := by
  let first :=
    (fineCouplingAcceptedSeparatedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId source).1
  let second :=
    (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source).1
  let sourcePair := fineCouplingAcceptedSeparatedPhysicalPair
    S rootFaceId targetFaceId source
  let coarseWitness := activePairTargetDisagreementWitness
    S first second event targetPair hactive
  have haccepted : coarseWitness.1 ∈
      fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces
        S hfineCoupling rootFaceId targetFaceId htarget source := by
    simpa only
      [fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces,
        first, second] using coarseWitness.2.1
  have hgeneric : coarseWitness.1 ∈
      fineCouplingPhysicalSupportSwapRightPacketTotalDisagreementFaces
        S targetFaceId sourcePair := by
    rw [← fineCouplingAcceptedSeparatedRightPacketTotalDisagreementFaces_eq
      S hfineCoupling rootFaceId targetFaceId htarget source]
    exact haccepted
  have htouch := mem_rightPacketTotalDisagreementFaces_implies_touch
    S targetFaceId sourcePair hgeneric
  let fineWitness := listAnyTrueWitness
    (dyadicCoarseFaceFineFaceIds S coarseWitness.1)
    (fineCouplingPhysicalSupportSwapMask S targetFaceId sourcePair)
    htouch
  refine
    { coarseFaceId := coarseWitness.1
      coarse_mem_sourceDisagreement := coarseWitness.2.1
      targetStates_ne := coarseWitness.2.2
      fineFaceId := fineWitness.1
      fine_mem_dyadicPacket := fineWitness.2.1
      fine_mem_targetComponent := ?_ }
  have hmask := fineWitness.2.2
  unfold fineCouplingPhysicalSupportSwapMask
    slabTwoReplicaSupportSwapMask at hmask
  exact of_decide_eq_true hmask

/-! ## 2. Observable endpoint certificates -/

/-- An active one-face event pair changes the underlying spin coordinate at
that exact face. -/
theorem activePair_facePositive_targetStates_ne
    (S : SlabScalePair) (first second : EdgeLabelling)
    (faceId : Nat) (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePositiveB faceId) targetPair = true) :
    targetPair.1 faceId ≠ targetPair.2 faceId := by
  intro heq
  have hevent := activePair_event_ne S first second
    (slabPhysicalFacePositiveB faceId) targetPair hactive
  apply hevent
  unfold slabPhysicalFacePositiveB
  rw [heq]

/-- A concrete marked endpoint chosen from an active two-face joint event. -/
structure ActiveJointFaceEndpoint
    (rootFaceId targetFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling) : Type where
  faceId : Nat
  is_root_or_target : faceId = rootFaceId ∨ faceId = targetFaceId
  targetStates_ne : targetPair.1 faceId ≠ targetPair.2 faceId

/-- An active root-target joint event constructively selects either the root
or the target as a changed coarse target-state coordinate. -/
def activePair_jointFaceEndpoint
    (S : SlabScalePair) (first second : EdgeLabelling)
    (rootFaceId targetFaceId : Nat)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S first second
      (slabPhysicalFacePairEvent rootFaceId targetFaceId)
      targetPair = true) :
    ActiveJointFaceEndpoint rootFaceId targetFaceId targetPair := by
  have hevent := activePair_event_ne S first second
    (slabPhysicalFacePairEvent rootFaceId targetFaceId)
    targetPair hactive
  by_cases hroot :
      targetPair.1 rootFaceId = targetPair.2 rootFaceId
  · have htargetNe :
        targetPair.1 targetFaceId ≠ targetPair.2 targetFaceId := by
      intro htargetEq
      apply hevent
      unfold slabPhysicalFacePairEvent slabPhysicalFacePositiveB
      rw [hroot, htargetEq]
    exact
      { faceId := targetFaceId
        is_root_or_target := Or.inr rfl
        targetStates_ne := htargetNe }
  · exact
      { faceId := rootFaceId
        is_root_or_target := Or.inl rfl
        targetStates_ne := hroot }

/-! ## 3. Axiom audit -/

#print axioms AcceptedActivePairComponentEndpoint
#print axioms acceptedLeftActivePairComponentEndpoint
#print axioms acceptedRightActivePairComponentEndpoint
#print axioms activePair_facePositive_targetStates_ne
#print axioms ActiveJointFaceEndpoint
#print axioms activePair_jointFaceEndpoint

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints
