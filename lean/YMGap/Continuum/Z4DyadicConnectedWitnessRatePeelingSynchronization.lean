/-
# Synchronize weighted and trace-producing rate peelings

The weighted canonical recursion records an explicit multiplicative payment,
whereas the structural canonical recursion records the full peel trace used
for reconstruction.  They inspect the same deterministic choice at every
state.  This module proves, by the same mass descent, that their terminal
accepted states are identical.

Both recursions are then run at the common comparison rate on the fine and
coarse component scans.  The four-entry source telescope is restated with
the trace-producing terminal states, while retaining the weighted payments.
Thus the quantitative estimate and the observable injective code now meet
at one literal terminal object.

Constructive contract: well-founded recursion on accepted physical mass and
proof irrelevance only; no classical choice, proof hole, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

/-! ## 1. Generic synchronization of the two deterministic recursions -/

/-- Recording payments instead of trace records does not change the terminal
accepted state. -/
theorem slabAcceptedPairCanonicalHighSpinWeightedPeeling_terminal_eq
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    (slabAcceptedPairCanonicalHighSpinWeightedPeeling
        D threshold faces hphysical state).1 =
      (slabAcceptedPairCanonicalPeeling D faces hphysical state).1 := by
  rw [slabAcceptedPairCanonicalHighSpinWeightedPeeling,
    slabAcceptedPairCanonicalPeeling]
  split
  · rename_i hchoice
    rw [hchoice]
  · rename_i choice hchoice
    rw [hchoice]
    exact slabAcceptedPairCanonicalHighSpinWeightedPeeling_terminal_eq
      D threshold faces hphysical choice.lowerState
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-! ## 2. Trace-producing common-rate peeling at both scales -/

abbrev FinePacketConnectedFourEntryRateCanonicalPeelingOutput
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :=
  SlabAcceptedPairedCanonicalPeelingOutput
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0) ×
    SlabAcceptedPairedCanonicalPeelingOutput
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryRateCanonicalPeelingOutput
      S rate hrate0 :=
  (slabAcceptedPairCanonicalPeeling
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        rate hrate0 expanded.2.1.1),
    slabAcceptedPairCanonicalPeeling
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        rate hrate0
        (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
          S expanded.2.1)))

/-- Fine and coarse weighted terminals are the corresponding trace-producing
terminals at the same rate. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRatePeeling_terminals_eq
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let weighted :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling
        S rate hrate0 orientation observableFaceId hobservableFace expanded
    let canonical :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
        S rate hrate0 orientation observableFaceId hobservableFace expanded
    weighted.1.1 = canonical.1.1 ∧
      weighted.2.1 = canonical.2.1 := by
  constructor
  · exact slabAcceptedPairCanonicalHighSpinWeightedPeeling_terminal_eq
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (anchorPaidExteriorThreshold rate)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        rate hrate0 expanded.2.1.1)
  · exact slabAcceptedPairCanonicalHighSpinWeightedPeeling_terminal_eq
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)
      (anchorPaidExteriorThreshold rate)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (coarseUnitCouplingSlabPhysicalData S)
        rate hrate0
        (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
          S expanded.2.1))

/-! ## 3. The source estimate now lands on trace-coded terminals -/

theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling_sourceWeight_le
    (S : SlabScalePair) (rate : Q')
    (hrate0 : (0 : Q') < rate) (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    let weighted :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling
        S rate rate0 orientation observableFaceId hobservableFace expanded
    let canonical :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
        S rate rate0 orientation observableFaceId hobservableFace expanded
    finePacketOrientedJointExpandedWitnessAtCouplingWeight
        S rate rate0 expanded.2.1 ≤
      (weighted.1.2 * weighted.2.2) *
        (slabAcceptedTwoReplicaStateWeight
            (finePacketFineRateCouplingSlabPhysicalData S rate rate0)
            canonical.1.1 *
          slabAcceptedTwoReplicaStateWeight
            (finePacketCoarseRateCouplingSlabPhysicalData S rate rate0)
            canonical.2.1) := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  have hsource :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling_sourceWeight_le
      S rate hrate0 hrate1 orientation observableFaceId
        hobservableFace expanded
  have hterminals :=
    finePacketGlobalNonzeroConnectedExpandedWitnessRatePeeling_terminals_eq
      S rate rate0 orientation observableFaceId hobservableFace expanded
  dsimp only at hsource hterminals ⊢
  rw [hterminals.1, hterminals.2] at hsource
  exact hsource

#print axioms slabAcceptedPairCanonicalHighSpinWeightedPeeling_terminal_eq
#print axioms FinePacketConnectedFourEntryRateCanonicalPeelingOutput
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRatePeeling_terminals_eq
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateCanonicalPeeling_sourceWeight_le

end YMGap.Continuum.Z4DyadicConnectedWitnessRatePeelingSynchronization
