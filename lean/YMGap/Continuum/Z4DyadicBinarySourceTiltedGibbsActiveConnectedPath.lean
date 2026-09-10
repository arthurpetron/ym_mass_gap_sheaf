/-
# Connected coarse paths for active tilted-row response pairs

An active accepted response pair already carries two different geometric
facts: the observable changes at a marked coarse face, and a changed coarse
source-disagreement face has a fine preimage in the target-rooted physical
source component.  This file inserts the missing decidable connectivity test
on the two coarse target states.

When that test is true, the result is not merely propositional reachability.
It returns the selected source-component endpoint together with a `ChainIn`
in the coarse target-pair union-support graph from the observable face to the
changed source-disagreement face.  The endpoint still carries its fine
dyadic preimage, so the certificate joins the observable geometry to the
already-localized fine source component across one blocking step.

The false branch and its involutive cancellation are not proved here.  No
activity estimate, volume-uniform response bound, continuum construction, or
mass gap is asserted.

Constructive contract: decidable finite-component membership and Type-level
chains only; no `Classical`, choice, `native_decide`, proof hole,
noncomputable declaration, trusted external computation, or new axiom.
-/

import YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints

namespace YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectedPath

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Continuum.CompactDualSlabExpandedPhysicalEventDisintegration
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabObservableFaceEventLaw
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportComponent
open YMGap.Continuum.CompactDualSlabObservablePairedSupportPhysicalFiber
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteBoolGraphComponents
open YMGap.Continuum.FiniteBoolGraphRootComponent
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveComponentEndpoints
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsResponseActiveCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourFineCouplingCenteredMarginAcceptedSupportSwapResponse
open YMGap.Continuum.Z4DyadicSpinFourLoweringKernel
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Generic endpoint-to-observable connectivity -/

private def positiveEitherOfNatNe
    (left right : Nat) (hne : left ≠ right) :
    0 < left ∨ 0 < right := by
  cases left with
  | zero =>
      cases right with
      | zero => exact False.elim (hne rfl)
      | succ value => exact Or.inr (Nat.zero_lt_succ value)
  | succ value => exact Or.inl (Nat.zero_lt_succ value)

/-- The decidable question separating the connected and disconnected
branches: does the already-selected changed source-disagreement face lie in
the observable-rooted union-support component of the two coarse targets? -/
def acceptedActivePairEndpointConnectedB
    (S : SlabScalePair) (first second : EdgeLabelling)
    (sourcePair targetPair : EdgeLabelling × EdgeLabelling)
    (targetFaceId observableFaceId : Nat)
    (endpoint : AcceptedActivePairComponentEndpoint S first second
      sourcePair targetPair targetFaceId) : Bool :=
  decide (endpoint.coarseFaceId ∈
    slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId)

/-- A complete cross-scale connected certificate.  Its coarse path starts at
the marked observable face and ends at the changed disagreement coordinate;
the stored endpoint continues from that coordinate to a fine face in the
physical source component. -/
structure AcceptedActivePairConnectedBridge
    (S : SlabScalePair) (first second : EdgeLabelling)
    (sourcePair targetPair : EdgeLabelling × EdgeLabelling)
    (targetFaceId observableFaceId : Nat) : Type where
  endpoint : AcceptedActivePairComponentEndpoint S first second
    sourcePair targetPair targetFaceId
  observable_mem_coarseFaces : observableFaceId ∈ S.coarse.faceEdges
  observable_targetStates_ne :
    targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId
  observable_mem_targetComponent : observableFaceId ∈
    slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId
  source_mem_targetComponent : endpoint.coarseFaceId ∈
    slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId
  coarsePath : ChainIn (slabSupportFaceAdjacentB S.coarse.extent)
    (slabTwoReplicaTargetSupportComponent S.coarse.extent
      targetPair.1 targetPair.2 observableFaceId)
    observableFaceId endpoint.coarseFaceId

/-- A true component test constructs the full bridge, including an explicit
coarse graph chain. -/
def acceptedActivePairConnectedBridgeOfConnected
    (S : SlabScalePair) (first second : EdgeLabelling)
    (sourcePair targetPair : EdgeLabelling × EdgeLabelling)
    (targetFaceId observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (hobservableNe :
      targetPair.1 observableFaceId ≠ targetPair.2 observableFaceId)
    (endpoint : AcceptedActivePairComponentEndpoint S first second
      sourcePair targetPair targetFaceId)
    (hconnected : acceptedActivePairEndpointConnectedB S first second
      sourcePair targetPair targetFaceId observableFaceId endpoint = true) :
    AcceptedActivePairConnectedBridge S first second sourcePair targetPair
      targetFaceId observableFaceId := by
  let vertices := slabTwoReplicaSupportFaceVertices S.coarse.extent
    targetPair.1 targetPair.2
  let component := slabTwoReplicaTargetSupportComponent S.coarse.extent
    targetPair.1 targetPair.2 observableFaceId
  have hobservableSupport :
      0 < targetPair.1 observableFaceId ∨
        0 < targetPair.2 observableFaceId :=
    positiveEitherOfNatNe _ _ hobservableNe
  have hobservableVertex : observableFaceId ∈ vertices := by
    exact mem_slabTwoReplicaSupportFaceVertices
      hobservableFace hobservableSupport
  have hobservableComponent : observableFaceId ∈ component := by
    exact root_mem_rootComponent
      (slabSupportFaceAdjacentB S.coarse.extent) hobservableVertex
  have hsourceComponent : endpoint.coarseFaceId ∈ component := by
    exact of_decide_eq_true hconnected
  have hpath : ChainIn (slabSupportFaceAdjacentB S.coarse.extent)
      component observableFaceId endpoint.coarseFaceId :=
    rootComponent_connected
      (slabSupportFaceAdjacentB S.coarse.extent)
      (slabSupportFaceAdjacentB_symmetric S.coarse.extent)
      hobservableVertex observableFaceId endpoint.coarseFaceId
      hobservableComponent hsourceComponent
  exact
    { endpoint := endpoint
      observable_mem_coarseFaces := hobservableFace
      observable_targetStates_ne := hobservableNe
      observable_mem_targetComponent := hobservableComponent
      source_mem_targetComponent := hsourceComponent
      coarsePath := hpath }

/-! ## 2. Accepted support-swap rows, specialized to one-face events -/

/-- The connected active branch of the accepted left-versus-swapped-left
response returns an explicit cross-scale path certificate. -/
def acceptedLeftFaceActivePairConnectedBridge
    (S : SlabScalePair) (hfineCoupling : (0 : YMGap.Constructive.Q') < S.fine.coupling)
    (rootFaceId targetFaceId observableFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (hobservable : observableFaceId ∈ S.coarse.faceEdges)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S
      (fineCouplingAcceptedSeparatedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (slabPhysicalFacePositiveB observableFaceId) targetPair = true)
    (hconnected : acceptedActivePairEndpointConnectedB S
      (fineCouplingAcceptedSeparatedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
      targetPair targetFaceId observableFaceId
      (acceptedLeftActivePairComponentEndpoint S hfineCoupling
        rootFaceId targetFaceId htarget source
        (slabPhysicalFacePositiveB observableFaceId) targetPair hactive) = true) :
    AcceptedActivePairConnectedBridge S
      (fineCouplingAcceptedSeparatedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
      targetPair targetFaceId observableFaceId := by
  let endpoint := acceptedLeftActivePairComponentEndpoint S hfineCoupling
    rootFaceId targetFaceId htarget source
    (slabPhysicalFacePositiveB observableFaceId) targetPair hactive
  exact acceptedActivePairConnectedBridgeOfConnected S
    (fineCouplingAcceptedSeparatedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId source).1
    (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source).1
    (fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source)
    targetPair targetFaceId observableFaceId hobservable
    (activePair_facePositive_targetStates_ne S
      (fineCouplingAcceptedSeparatedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedLeftPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      observableFaceId targetPair hactive)
    endpoint hconnected

/-- The analogous connected path certificate for the accepted
right-versus-swapped-right response. -/
def acceptedRightFaceActivePairConnectedBridge
    (S : SlabScalePair) (hfineCoupling : (0 : YMGap.Constructive.Q') < S.fine.coupling)
    (rootFaceId targetFaceId observableFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent)
    (hobservable : observableFaceId ∈ S.coarse.faceEdges)
    (source : SlabObservablePairedSupportSeparatedSource
      S.fine rootFaceId targetFaceId)
    (targetPair : EdgeLabelling × EdgeLabelling)
    (hactive : finePacketLocalizedResponsePairActiveB S
      (fineCouplingAcceptedSeparatedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (slabPhysicalFacePositiveB observableFaceId) targetPair = true)
    (hconnected : acceptedActivePairEndpointConnectedB S
      (fineCouplingAcceptedSeparatedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
      targetPair targetFaceId observableFaceId
      (acceptedRightActivePairComponentEndpoint S hfineCoupling
        rootFaceId targetFaceId htarget source
        (slabPhysicalFacePositiveB observableFaceId) targetPair hactive) = true) :
    AcceptedActivePairConnectedBridge S
      (fineCouplingAcceptedSeparatedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      (fineCouplingAcceptedSeparatedPhysicalPair
        S rootFaceId targetFaceId source)
      targetPair targetFaceId observableFaceId := by
  let endpoint := acceptedRightActivePairComponentEndpoint S hfineCoupling
    rootFaceId targetFaceId htarget source
    (slabPhysicalFacePositiveB observableFaceId) targetPair hactive
  exact acceptedActivePairConnectedBridgeOfConnected S
    (fineCouplingAcceptedSeparatedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId source).1
    (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
      S hfineCoupling rootFaceId targetFaceId htarget source).1
    (fineCouplingAcceptedSeparatedPhysicalPair
      S rootFaceId targetFaceId source)
    targetPair targetFaceId observableFaceId hobservable
    (activePair_facePositive_targetStates_ne S
      (fineCouplingAcceptedSeparatedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId source).1
      (fineCouplingAcceptedSeparatedSwappedRightPositiveSource
        S hfineCoupling rootFaceId targetFaceId htarget source).1
      observableFaceId targetPair hactive)
    endpoint hconnected

/-! ## 3. Axiom audit -/

#print axioms acceptedActivePairEndpointConnectedB
#print axioms AcceptedActivePairConnectedBridge
#print axioms acceptedActivePairConnectedBridgeOfConnected
#print axioms acceptedLeftFaceActivePairConnectedBridge
#print axioms acceptedRightFaceActivePairConnectedBridge

end YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsActiveConnectedPath
