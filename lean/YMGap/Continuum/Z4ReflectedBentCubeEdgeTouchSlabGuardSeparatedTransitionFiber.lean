/-
# A common guarded receiver fiber has an explicit separated joint floor

Take any duplicate-free finite list of accepted two-replica sources whose
ambient-cutoff guarded grafts are equal.  Receiver recoverability identifies
one common canonical peeled terminal.  The complete geometric peeling rate
pays the source list into that terminal, the cutoff-uniform insertion rate
pays the terminal into the literal observable receiver, and a quarter-mass
event then supplies the separated joint transition.

Constructive contract: finite source lists, exact anchor weights, receiver
recoverability, and rational payment composition only; no `Classical`,
choice, `native_decide`, `sorry`, new axiom, noncomputable declaration, or
unbounded heartbeat option.
-/

import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionRate
import YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverabilityCutoffPersistence

namespace YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionFiber

set_option autoImplicit false
set_option maxHeartbeats 1000000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingBlockProfileGeometric
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.PentagonRelation
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuard
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardAcceptedGraftCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardInsertionRateCutoffUniform
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPeeling
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardPositiveTargetObservableSourceCutoffPersistence
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionRate
open YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardTerminalRecoverabilityCutoffPersistence
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

private theorem anchorDataExtentFive (cutoff : Nat) :
    (anchorSlabPhysicalData cutoff 2).extent = 5 := rfl

private theorem anchorDataCouplingPos (cutoff : Nat) :
    (0 : Q') < (anchorSlabPhysicalData cutoff 2).coupling := by
  change (0 : Q') < anchorCoupling
  decide

/-- **Literal common-receiver joint payment.**  Every displayed source has
the same ambient-cutoff guarded receiver as `representative`; hence the
explicit three-factor rate pays their complete anchor Gibbs weight into that
receiver times any event of mass at least one quarter. -/
theorem reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_joint
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
            (anchorDataExtentFive cutoff)
            representative)
    (eventMass : Q') (eventMass_floor : oneQuarter ≤ eventMass) :
    reflectedBentGuardSeparatedTransitionRate
          (anchorSlabPhysicalData cutoff 2).coupling
          reflectedBentPatternGuardFaceIds *
        listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2) sources ≤
      slabObservableTwoReplicaPairWeight
          (anchorSlabPhysicalData cutoff 2)
          (reflectedBentGuardGraftObservableSourcePairAtCutoff
            (anchorSlabPhysicalData cutoff 2) hcutoff
              (anchorDataExtentFive cutoff)
              representative) *
        eventMass := by
  let D := anchorSlabPhysicalData cutoff 2
  let terminal :=
    (reflectedBentGuardCanonicalPeeling D
      (anchorDataExtentFive cutoff) representative).1
  apply reflectedBentGuardSeparatedTransitionRate_mul_sourceMass_le_joint
    D.coupling (anchorDataCouplingPos cutoff)
    reflectedBentPatternGuardFaceIds
    (listQSum (slabAcceptedTwoReplicaStateWeight cutoff 2) sources)
    (slabAcceptedTwoReplicaStateWeight cutoff 2 terminal)
    (slabObservableTwoReplicaPairWeight D
      (reflectedBentGuardGraftObservableSourcePairAtCutoff
        D hcutoff (anchorDataExtentFive cutoff) representative))
    eventMass
  · exact listQSum_nonnegative_on
      (slabAcceptedTwoReplicaStateWeight cutoff 2) sources
      (fun source _ =>
        slabAcceptedTwoReplicaStateWeight_nonnegative cutoff 2 source)
  · exact slabObservableTwoReplicaPairWeight_nonnegative
      D _
      (reflectedBentGuardGraftObservableSourcePairAtCutoff
        D hcutoff (anchorDataExtentFive cutoff) representative)
  · exact pairedPeelProfilePaymentRate_mul_fixedTerminal_weight_sum_le
      cutoff 2 reflectedBentPatternGuardFaceIds
      reflectedBentPatternGuardFaceIds_nodup
      (fun faceId hface => by
        exact reflectedBentPatternGuardFaceId_mem_physical hface)
      terminal sources hsources
      (fun source hsource =>
        reflectedBentGuardCanonicalPeeling_terminal_eq_of_graftOfOneLE_eq
          D hcutoff (anchorDataExtentFive cutoff) source representative
            (same_receiver source hsource))
  · simpa only [D, terminal, slabAcceptedTwoReplicaStateWeight] using
      reflectedBentGuardGraftObservableSourcePairAtCutoffWeight_floor
        D hcutoff (anchorDataExtentFive cutoff)
          (anchorDataCouplingPos cutoff) representative
  · exact eventMass_floor

#print axioms reflectedBentGuardSeparatedTransitionRate_mul_sourceWeightSum_le_joint

end YMGap.Continuum.Z4ReflectedBentCubeEdgeTouchSlabGuardSeparatedTransitionFiber
