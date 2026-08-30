/-
# The common receiver fiber pays a transported separated observable event

The receiver-fiber theorem leaves its event mass abstract.  The transported
pivot-cylinder compiler supplies exactly such an event on any propositionally
equal presentation of the guarded recoupling row.  This module identifies the
two quantities without exposing or normalizing the concrete dependent product.

Constructive contract: exact finite event transport and the previously proved
common-receiver joint payment only; no `Classical`, choice, `native_decide`,
`sorry`, new axiom, noncomputable declaration, or unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionFiber

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionObservableFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionFiber
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionRate
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

private theorem anchorDataExtentFive (cutoff : Nat) :
    (anchorSlabPhysicalData cutoff 2).extent = 5 := rfl

/-- **Same-row separated joint payment.**  The event on the right is the
literal transported pivot-cylinder list carried by `row`; every one of its
members retains the marked-face disconnection certificate. -/
theorem reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_transportedEventJoint
    (cutoff : Nat) (hcutoff : 1 ≤ cutoff)
    (sources : List (SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2)))
    (hsources : sources.Nodup)
    (representative : SlabAcceptedTwoReplicaState
      (anchorSlabPhysicalData cutoff 2))
    (same_receiver : ∀ source, source ∈ sources →
      reflectedBentGuardGraftAcceptedStateOfOneLE
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) source =
        reflectedBentGuardGraftAcceptedStateOfOneLE
          (anchorSlabPhysicalData cutoff 2) hcutoff
            (anchorDataExtentFive cutoff) representative)
    (linkedList : List
      {link // link ∈ boundaryCompleteSlabLinks 5})
    (hnodup : linkedList.Nodup)
    (hpivot : reflectedBentSwitchPivotLinked ∈ linkedList)
    (row : ReflectedBentGuardGraftPivotCylinderRowPresentationAtCutoff
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff) representative linkedList) :
    let event :=
      reflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
        (anchorSlabPhysicalData cutoff 2) hcutoff
          (anchorDataExtentFive cutoff) representative linkedList
          hnodup hpivot
    reflectedBentGuardSeparatedTransitionRate
          (anchorSlabPhysicalData cutoff 2).coupling
          reflectedBentPatternGuardFaceIds *
        listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2) sources ≤
      slabObservableTwoReplicaPairWeight
          (anchorSlabPhysicalData cutoff 2)
          (reflectedBentGuardGraftObservableSourcePairAtCutoff
            (anchorSlabPhysicalData cutoff 2) hcutoff
              (anchorDataExtentFive cutoff) representative) *
        listQSum
          (reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
            (anchorSlabPhysicalData cutoff 2) hcutoff
              (anchorDataExtentFive cutoff) representative linkedList
                row event)
          (reflectedBentGuardGraftPivotCylinderTransportedChoicesAtCutoff
            (anchorSlabPhysicalData cutoff 2) hcutoff
              (anchorDataExtentFive cutoff) representative linkedList
                row event) := by
  let event :=
    reflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      (anchorSlabPhysicalData cutoff 2) hcutoff
        (anchorDataExtentFive cutoff) representative linkedList hnodup hpivot
  apply reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_joint
    cutoff hcutoff sources hsources representative same_receiver
  exact reflectedBentGuardGraftPivotCylinderTransportedChoices_weight_floor
    (anchorSlabPhysicalData cutoff 2) hcutoff
      (anchorDataExtentFive cutoff) representative linkedList row event

#print axioms reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_transportedEventJoint

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionObservableFiber
