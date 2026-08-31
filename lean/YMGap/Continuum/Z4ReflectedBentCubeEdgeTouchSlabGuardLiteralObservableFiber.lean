/-
# The separated receiver fiber on the literal observable SU(2) row

Instantiate the presentation-parametric receiver payment with the exact
whole-slab observable production row.  The event is the complete-link pivot
cylinder, so every transported target remains marked-face disconnected and
its literal observable row mass is at least one quarter.

Constructive contract: finite list membership, exact equality transport, and
the previously proved joint-mass estimate only; no `Classical`, choice,
`native_decide`, `sorry`, new axiom, noncomputable declaration, or unbounded
heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRow
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionObservableFiber

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionGeometry
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabConnectedSource
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableRow
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderObservableEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPivotCylinderSeparatedEvent
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionObservableFiber
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionRate
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabWholeProductPositivity

private theorem anchorDataExtentFive (cutoff : Nat) :
    (anchorSlabPhysicalData cutoff 2).extent = 5 := rfl

private theorem fullLinkedList_nodup :
    (boundaryCompleteSlabLinks 5).attach.Nodup :=
  attach_nodup_of_nodup _ (boundaryCompleteSlabLinks_nodup 5)

private theorem pivot_mem_fullLinkedList :
    reflectedBentSwitchPivotLinked ∈
      (boundaryCompleteSlabLinks 5).attach :=
  List.mem_attach _ _

/-- The quarter-mass separated cylinder on the complete literal observable
link row. -/
def reflectedBentGuardGraftLiteralObservableSeparatedEventAtCutoff
    (D : SlabPhysicalData) (hcutoff : 1 ≤ D.cutoff)
    (hextent : D.extent = 5)
    (state : SlabAcceptedTwoReplicaState D) :
    ReflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
      D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach :=
  reflectedBentGuardGraftPivotCylinderSeparatedEventAtCutoff
    D hcutoff hextent state (boundaryCompleteSlabLinks 5).attach
      fullLinkedList_nodup pivot_mem_fullLinkedList

/-- **Literal-row separated joint payment.**  Every source in one common
guarded receiver fiber is paid into a concrete disconnected event on the
exact observable SU(2) production row. -/
theorem reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_literalObservableEventJoint
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
            (anchorDataExtentFive cutoff) representative) :
    let D := anchorSlabPhysicalData cutoff 2
    let hextent := anchorDataExtentFive cutoff
    let event :=
      reflectedBentGuardGraftLiteralObservableSeparatedEventAtCutoff
        D hcutoff hextent representative
    let row := reflectedBentGuardGraftLiteralObservableRowAtCutoff
      D hcutoff hextent representative
    reflectedBentGuardSeparatedTransitionRate D.coupling
          reflectedBentPatternGuardFaceIds *
        listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2) sources ≤
      slabObservableTwoReplicaPairWeight D
          (reflectedBentGuardGraftObservableSourcePairAtCutoff
            D hcutoff hextent representative) *
        listQSum
          (reflectedBentGuardGraftPivotCylinderTransportedChoiceWeightAtCutoff
            D hcutoff hextent representative
              (boundaryCompleteSlabLinks 5).attach row event)
          (reflectedBentGuardGraftPivotCylinderTransportedChoicesAtCutoff
            D hcutoff hextent representative
              (boundaryCompleteSlabLinks 5).attach row event) := by
  exact
    reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_transportedEventJoint
      cutoff hcutoff sources hsources representative same_receiver
      (boundaryCompleteSlabLinks 5).attach fullLinkedList_nodup
      pivot_mem_fullLinkedList
      (reflectedBentGuardGraftLiteralObservableRowAtCutoff
        (anchorSlabPhysicalData cutoff 2) hcutoff
          (anchorDataExtentFive cutoff) representative)

#print axioms reflectedBentGuardGraftLiteralObservableSeparatedEventAtCutoff
#print axioms reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_literalObservableEventJoint

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardLiteralObservableFiber
