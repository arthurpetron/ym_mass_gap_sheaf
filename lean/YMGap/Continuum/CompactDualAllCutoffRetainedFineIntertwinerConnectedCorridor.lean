/-
# Connected corridor decay for the retained all-cutoff pair law

The retained two-replica point law is now restricted to the literal
observable four-cell pairs whose paired physical support connects the root to
the target and whose two four-preimage raw partitions are nonpositive.  This
is exactly the positive-incoherent part of the corrected enriched blocked law
that enters the established component-peeling carrier.

Summing the pointwise law identifies its probability with the corresponding
filtered accepted-pair Gibbs weight divided by the physical partition square.
Nonnegativity makes this filtered weight no larger than the complete connected
carrier.  The existing SU(2) component estimate therefore gives the explicit
cutoff- and volume-independent bound

  (25/9) * (16/25)^(linfDistance + 1)

for every rational `0 < w < 1` with `w <= 1/400`.

This controls one genuine sector of the enriched pair law.  It does not bound
the coherent/coarse or mixed sectors, identify an OS transfer observable,
prove a strict form bound, pass to the continuum, or prove the Clay theorem.

## Axiom gate

Finite filtering and summation, exact rational normalization, and the
existing non-abelian SU(2) component estimate only.  No classical choice,
placeholder, trusted external computation, computability escape, heartbeat
increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTwoReplicaLaw
import YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
import YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
import YMGap.Continuum.FiniteWeightedGramSOS

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerPeelingBridge
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerTwoReplicaLaw
open YMGap.Continuum.CompactDualAllCutoffTotalKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabObservablePairedPositivePhysicalWeights
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDependentKernelFirstSourceThinning
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The positive-incoherent connected subcarrier -/

/-- Both physical rows of an observable pair use the retained branch of the
all-cutoff kernel. -/
def slabObservablePairRetainedIncoherentB
    (S : SlabScalePair) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair S.fine rootFaceId) : Bool :=
  decide (¬ (0 : Q') < wholeSlabRawRowPartition S pair.1.1.1) &&
    decide (¬ (0 : Q') < wholeSlabRawRowPartition S pair.2.1.1)

/-- Observable support-connected pairs lying entirely in the retained
positive-incoherent sector. -/
def slabObservableRetainedIncoherentConnectedPairs
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) :
    List (SlabObservableTwoReplicaPair S.fine rootFaceId) :=
  (slabObservablePairedSupportConnectedFourCellSourcePairs
    S.fine rootFaceId targetFaceId).filter
      (slabObservablePairRetainedIncoherentB S)

/-- Actual product probability assigned to one observable pair by two copies
of the enriched blocked law. -/
def slabObservableRetainedPairBlockedPointMass
    (S : SlabScalePair) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair S.fine rootFaceId) : Q' :=
  retainedFinePairBlockedPointMass S pair.1.1 pair.2.1

/-- Total enriched probability of the retained positive-incoherent connected
observable subcarrier. -/
def slabObservableRetainedIncoherentConnectedMass
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) : Q' :=
  listQSum (slabObservableRetainedPairBlockedPointMass S)
    (slabObservableRetainedIncoherentConnectedPairs
      S rootFaceId targetFaceId)

/-! ## 2. Exact sum-level identification -/

private theorem divPos_le_divPos_of_le_local
    {left right denominator : Q'}
    (hdenominator : (0 : Q') < denominator)
    (hle : left <= right) :
    Q'.divPos left denominator hdenominator <=
      Q'.divPos right denominator hdenominator := by
  unfold Q'.divPos
  exact Q'.mul_le_mul_of_nonneg_right _ _ _ hle
    (Q'.le_of_lt (Q'.recipPos_pos denominator hdenominator))

theorem slabObservableRetainedPairBlockedPointMass_eqv_normalizedWeight
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (hcoupling : (0 : Q') < S.fine.coupling)
    (pair : SlabObservableTwoReplicaPair S.fine rootFaceId)
    (hpair : pair ∈ slabObservableRetainedIncoherentConnectedPairs
      S rootFaceId targetFaceId) :
    slabObservableRetainedPairBlockedPointMass S pair ≈
      Q'.divPos
        (slabObservableTwoReplicaPairWeight S.fine pair)
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)) := by
  have htest := (List.mem_filter.mp hpair).2
  have hleftIncoherent : ¬ (0 : Q') <
      wholeSlabRawRowPartition S pair.1.1.1 := by
    intro hpositive
    simp [slabObservablePairRetainedIncoherentB, hpositive] at htest
  have hrightIncoherent : ¬ (0 : Q') <
      wholeSlabRawRowPartition S pair.2.1.1 := by
    intro hpositive
    simp [slabObservablePairRetainedIncoherentB, hpositive] at htest
  have hleft : (Sum.inr pair.1.1 : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S :=
    (allCutoffRetainedFineTarget_mem_iff S pair.1.1).mpr
      pair.1.source_mem_expanded
  have hright : (Sum.inr pair.2.1 : AllCutoffRetainedTarget) ∈
      allCutoffRetainedTargets S :=
    (allCutoffRetainedFineTarget_mem_iff S pair.2.1).mpr pair.2.2
  have hpoint :=
    retainedFinePairBlockedPointMass_eqv_acceptedNormalizedMass
      S pair.1.1 pair.2.1 hleft hright hcoupling
        hleftIncoherent hrightIncoherent
  simpa only [slabObservableRetainedPairBlockedPointMass,
    slabAcceptedTwoReplicaStateNormalizedMass,
    retainedFinePairAcceptedState,
    retainedFineTargetExpandedEntry,
    slabAcceptedTwoReplicaStateWeight,
    slabObservableTwoReplicaPairWeight,
    slabObservablePositiveEntryWeight,
    slabExpandedFineEntryWeight,
    slabExpandedFineSourceWeight] using hpoint

/-- The complete retained connected event is exactly the normalized Gibbs
weight of its explicit filtered accepted-pair carrier. -/
theorem slabObservableRetainedIncoherentConnectedMass_eqv_normalizedWeight
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat)
    (hcoupling : (0 : Q') < S.fine.coupling) :
    slabObservableRetainedIncoherentConnectedMass
        S rootFaceId targetFaceId ≈
      Q'.divPos
        (listQSum (slabObservableTwoReplicaPairWeight S.fine)
          (slabObservableRetainedIncoherentConnectedPairs
            S rootFaceId targetFaceId))
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)) := by
  let items := slabObservableRetainedIncoherentConnectedPairs
    S rootFaceId targetFaceId
  let denominator := S.fine.physicalPartition * S.fine.physicalPartition
  let denominatorPos := Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  refine Q'.eqv_trans _
    (listQSum
      (fun pair => Q'.divPos
        (slabObservableTwoReplicaPairWeight S.fine pair)
        denominator denominatorPos)
      items) _ ?_ ?_
  · unfold slabObservableRetainedIncoherentConnectedMass
    apply listQSum_congr_on
    intro pair hpair
    exact slabObservableRetainedPairBlockedPointMass_eqv_normalizedWeight
      S rootFaceId targetFaceId hcoupling pair hpair
  · unfold Q'.divPos
    exact listQSum_mul_right
      (slabObservableTwoReplicaPairWeight S.fine)
      (Q'.recipPos denominator denominatorPos) items

/-! ## 3. The inherited explicit SU(2) corridor rate -/

/-- The actual retained positive-incoherent connected probability is bounded
by the explicit SU(2) component rate throughout `0 < w <= 1/400`.  Coupling,
cutoff, and volume all remain named in the statement through `S.fine`. -/
theorem slabObservableRetainedIncoherentConnectedMass_le_corridorRate
    (S : SlabScalePair)
    (hw0 : (0 : Q') < S.fine.coupling)
    (hw1 : S.fine.coupling < (1 : Q'))
    (hwAnchor : S.fine.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent) :
    slabObservableRetainedIncoherentConnectedMass
        S rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        S.fine rootFaceId targetFaceId := by
  let denominator := S.fine.physicalPartition * S.fine.physicalPartition
  let denominatorPos := Q'.mul_pos
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
    (slabParametricKPhysicalPartition_pos
      S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
  have hfilter :
      listQSum (slabObservableTwoReplicaPairWeight S.fine)
          (slabObservableRetainedIncoherentConnectedPairs
            S rootFaceId targetFaceId) <=
        listQSum (slabObservableTwoReplicaPairWeight S.fine)
          (slabObservablePairedSupportConnectedFourCellSourcePairs
            S.fine rootFaceId targetFaceId) := by
    unfold slabObservableRetainedIncoherentConnectedPairs
    apply listQSum_filter_le_of_nonnegative
    intro pair
    exact Q'.le_of_lt
      (slabObservableTwoReplicaPairWeight_pos_of_coupling_pos
        S.fine hw0 pair)
  have hnormalized :
      Q'.divPos
          (listQSum (slabObservableTwoReplicaPairWeight S.fine)
            (slabObservableRetainedIncoherentConnectedPairs
              S rootFaceId targetFaceId))
          denominator denominatorPos <=
        slabObservableNormalizedPairedSupportConnectedMass
          S.fine rootFaceId targetFaceId := by
    unfold slabObservableNormalizedPairedSupportConnectedMass
    exact divPos_le_divPos_of_le_local denominatorPos hfilter
  exact Q'.le_trans' _ _ _
    (Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (slabObservableRetainedIncoherentConnectedMass_eqv_normalizedWeight
          S rootFaceId targetFaceId hw0))
      hnormalized)
    (slabObservableNormalizedPairedSupportConnectedMass_le_corridorRate
      S.fine hw0 hw1 hwAnchor rootFaceId targetFaceId htarget)

/-! ## Axiom audit -/

#print axioms slabObservablePairRetainedIncoherentB
#print axioms slabObservableRetainedIncoherentConnectedMass_eqv_normalizedWeight
#print axioms slabObservableRetainedIncoherentConnectedMass_le_corridorRate

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor
