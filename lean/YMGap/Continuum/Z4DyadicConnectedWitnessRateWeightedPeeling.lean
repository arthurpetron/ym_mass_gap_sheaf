/-
# Apply the arbitrary-coupling peeling telescope to all four entries

The preceding comparison places every connected witness inside a product of
two accepted pair weights at one explicit rate.  Here the deterministic
weighted canonical peeling is run on the fine component children and on the
coarse component itself.  Both recursions use that same named rate.

Their source inequalities multiply to a single four-entry telescope: the
rate-coupled joint weight is bounded by the product of the two explicit path
payments times the product weight of the two terminal accepted pairs.  This
is still a pointwise theorem; summation over faithful terminal fibers is the
next contraction.

Constructive contract: the existing well-founded deterministic recursion,
explicit positive rate interval, and rational order algebra only; no
classical choice, proof hole, trusted external computation, computability
escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.Z4DyadicConnectedWitnessRateCoupledDomination

namespace YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalStep
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.Z4DyadicAcceptedStateCouplingRebase
open YMGap.Continuum.Z4DyadicBinaryGlobalOrientedNonzeroConnectedCarrier
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsConnectedOrientationDecomposition
open YMGap.Continuum.Z4DyadicBinarySourceTiltedGibbsJointActivityFloor
open YMGap.Continuum.Z4DyadicConnectedEntropyExpandedWitnessCarrier
open YMGap.Continuum.Z4DyadicConnectedFourEntryComponentPeeling
open YMGap.Continuum.Z4DyadicConnectedWitnessRateCoupledDomination
open YMGap.Continuum.Z4DyadicJointUnitReferenceExpandedWitness
open YMGap.Continuum.Z4DyadicJointWitnessRateCouplingRebase
open YMGap.Continuum.Z4DyadicLocalizedUnitTargetExpandedWitness
open YMGap.Continuum.Z4StrongCouplingParametricAnchor
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex

local infix:50 " ≈ " => Q'.eqv

private theorem mul_four_regroup_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) := by
  show _ * (_ : Int) = _ * (_ : Int)
  simp only [Q'.mul_num_cast, Q'.mul_den_cast]
  ac_rfl

/-! ## 1. The two rate-coupled slab data and scan proofs -/

def finePacketFineRateCouplingSlabPhysicalData
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :
    SlabPhysicalData :=
  slabPhysicalDataAtCoupling
    (finePacketFineUnitCouplingSlabPhysicalData S) rate hrate0

def finePacketCoarseRateCouplingSlabPhysicalData
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :
    SlabPhysicalData :=
  slabPhysicalDataAtCoupling
    (coarseUnitCouplingSlabPhysicalData S) rate hrate0

theorem finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (fineFaceId : Nat)
    (hface : fineFaceId ∈
      finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId entry) :
    fineFaceId ∈ slabPhysicalFaceEdges
      (finePacketFineRateCouplingSlabPhysicalData
        S rate hrate0).extent := by
  simpa only [finePacketFineRateCouplingSlabPhysicalData,
    slabPhysicalDataAtCoupling, SlabPhysicalData.extent] using
    (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace entry fineFaceId hface)

theorem finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (entry : FinePacketGlobalOrientedNonzeroConnectedEntry
      S orientation observableFaceId)
    (coarseFaceId : Nat)
    (hface : coarseFaceId ∈
      finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
        S orientation observableFaceId entry) :
    coarseFaceId ∈ slabPhysicalFaceEdges
      (finePacketCoarseRateCouplingSlabPhysicalData
        S rate hrate0).extent := by
  simpa only [finePacketCoarseRateCouplingSlabPhysicalData,
    slabPhysicalDataAtCoupling, SlabPhysicalData.extent] using
    (finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_physical
      S orientation observableFaceId hobservableFace entry coarseFaceId hface)

/-! ## 2. Paired weighted peeling at both scales -/

abbrev FinePacketConnectedFourEntryRateWeightedPeelingOutput
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate) :=
  SlabAcceptedPairedHighSpinWeightedPeelingOutput
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0) ×
    SlabAcceptedPairedHighSpinWeightedPeelingOutput
      (finePacketCoarseRateCouplingSlabPhysicalData S rate hrate0)

def finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling
    (S : SlabScalePair) (rate : Q') (hrate0 : (0 : Q') ≤ rate)
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    FinePacketConnectedFourEntryRateWeightedPeelingOutput
      S rate hrate0 :=
  (slabAcceptedPairCanonicalHighSpinWeightedPeeling
      (finePacketFineRateCouplingSlabPhysicalData S rate hrate0)
      (anchorPaidExteriorThreshold rate)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces
        S orientation observableFaceId expanded.1)
      (finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
        S rate hrate0 orientation observableFaceId hobservableFace expanded.1)
      (slabAcceptedTwoReplicaStateAtCoupling
        (finePacketFineUnitCouplingSlabPhysicalData S)
        rate hrate0 expanded.2.1.1),
    slabAcceptedPairCanonicalHighSpinWeightedPeeling
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
          S expanded.2.1)))

/-- The recursively accumulated explicit payment is nonnegative. -/
theorem slabAcceptedPairCanonicalHighSpinWeightedPeeling_payment_nonnegative
    (D : SlabPhysicalData) (threshold : Nat)
    (faces : List Nat)
    (hphysical : forall faceId, faceId ∈ faces ->
      faceId ∈ slabPhysicalFaceEdges D.extent)
    (state : SlabAcceptedTwoReplicaState D) :
    (0 : Q') ≤
      (slabAcceptedPairCanonicalHighSpinWeightedPeeling
        D threshold faces hphysical state).2 := by
  rw [slabAcceptedPairCanonicalHighSpinWeightedPeeling]
  split
  · exact Q'.zero_le_one
  · rename_i choice hchoice
    exact Q'.mul_nonneg _ _
      (slabAcceptedPairedPeelChoiceHighSpinPaymentRate_nonnegative
        threshold choice)
      (slabAcceptedPairCanonicalHighSpinWeightedPeeling_payment_nonnegative
        D threshold faces hphysical choice.lowerState)
termination_by slabAcceptedTwoReplicaStateMass state
decreasing_by
  apply SlabAcceptedPairedPeelChoice.lowerState_mass_lt

/-- The product of the two rate-coupled accepted source weights telescopes to
the product of the two explicit payments and terminal weights. -/
theorem finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling_sourceWeight_le
    (S : SlabScalePair) (rate : Q')
    (hrate0 : (0 : Q') < rate) (hrate1 : rate < (1 : Q'))
    (orientation : FinePacketEnvelopeOrientation)
    (observableFaceId : Nat)
    (hobservableFace : observableFaceId ∈ S.coarse.faceEdges)
    (expanded : FinePacketGlobalNonzeroConnectedExpandedWitnessEntry
      S orientation observableFaceId) :
    let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
    let result :=
      finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling
        S rate rate0 orientation observableFaceId hobservableFace expanded
    finePacketOrientedJointExpandedWitnessAtCouplingWeight
        S rate rate0 expanded.2.1 ≤
      (result.1.2 * result.2.2) *
        (slabAcceptedTwoReplicaStateWeight
            (finePacketFineRateCouplingSlabPhysicalData S rate rate0)
            result.1.1 *
          slabAcceptedTwoReplicaStateWeight
            (finePacketCoarseRateCouplingSlabPhysicalData S rate rate0)
            result.2.1) := by
  let rate0 : (0 : Q') ≤ rate := Q'.le_of_lt hrate0
  let fineD := finePacketFineRateCouplingSlabPhysicalData S rate rate0
  let coarseD := finePacketCoarseRateCouplingSlabPhysicalData S rate rate0
  let fineFaces :=
    finePacketGlobalNonzeroConnectedEntryFineComponentFaces
      S orientation observableFaceId expanded.1
  let coarseFaces :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces
      S orientation observableFaceId expanded.1
  let finePhysical :=
    finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
      S rate rate0 orientation observableFaceId hobservableFace expanded.1
  let coarsePhysical :=
    finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
      S rate rate0 orientation observableFaceId hobservableFace expanded.1
  let fineState := slabAcceptedTwoReplicaStateAtCoupling
    (finePacketFineUnitCouplingSlabPhysicalData S)
    rate rate0 expanded.2.1.1
  let coarseState := slabAcceptedTwoReplicaStateAtCoupling
    (coarseUnitCouplingSlabPhysicalData S)
    rate rate0
    (finePacketOrientedJointUnitExpandedWitnessCoarseAcceptedState
      S expanded.2.1)
  let fineResult := slabAcceptedPairCanonicalHighSpinWeightedPeeling
    fineD (anchorPaidExteriorThreshold rate)
      fineFaces finePhysical fineState
  let coarseResult := slabAcceptedPairCanonicalHighSpinWeightedPeeling
    coarseD (anchorPaidExteriorThreshold rate)
      coarseFaces coarsePhysical coarseState
  have hfine :=
    slabAcceptedPairCanonicalHighSpinWeightedPeeling_sourceWeight_le
      fineD (by simpa only [fineD,
        finePacketFineRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate0)
      (by simpa only [fineD,
        finePacketFineRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate1)
      fineFaces finePhysical fineState
  have hcoarse :=
    slabAcceptedPairCanonicalHighSpinWeightedPeeling_sourceWeight_le
      coarseD (by simpa only [coarseD,
        finePacketCoarseRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate0)
      (by simpa only [coarseD,
        finePacketCoarseRateCouplingSlabPhysicalData,
        slabPhysicalDataAtCoupling] using hrate1)
      coarseFaces coarsePhysical coarseState
  have hfineUpper0 : (0 : Q') ≤
      fineResult.2 * slabAcceptedTwoReplicaStateWeight fineD fineResult.1 :=
    Q'.mul_nonneg _ _
      (slabAcceptedPairCanonicalHighSpinWeightedPeeling_payment_nonnegative
        fineD (anchorPaidExteriorThreshold rate)
          fineFaces finePhysical fineState)
      (slabAcceptedTwoReplicaStateWeight_nonnegative fineD fineResult.1)
  have hcoarseSource0 : (0 : Q') ≤
      slabAcceptedTwoReplicaStateWeight coarseD coarseState :=
    slabAcceptedTwoReplicaStateWeight_nonnegative coarseD coarseState
  have hproduct := Q'.mul_le_mul_of_nonneg hfine hcoarse
    hfineUpper0 hcoarseSource0
  refine Q'.le_trans' _ _ _ hproduct (Q'.le_of_eqv ?_)
  exact mul_four_regroup_local _ _ _ _

#print axioms finePacketFineRateCouplingSlabPhysicalData
#print axioms finePacketCoarseRateCouplingSlabPhysicalData
#print axioms finePacketGlobalNonzeroConnectedEntryFineComponentFaces_mem_ratePhysical
#print axioms finePacketGlobalNonzeroConnectedEntryCoarseComponentFaces_mem_ratePhysical
#print axioms FinePacketConnectedFourEntryRateWeightedPeelingOutput
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling
#print axioms slabAcceptedPairCanonicalHighSpinWeightedPeeling_payment_nonnegative
#print axioms finePacketGlobalNonzeroConnectedExpandedWitnessRateWeightedPeeling_sourceWeight_le

end YMGap.Continuum.Z4DyadicConnectedWitnessRateWeightedPeeling
