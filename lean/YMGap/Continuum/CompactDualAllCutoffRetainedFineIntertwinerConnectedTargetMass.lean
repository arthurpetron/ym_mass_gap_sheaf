/-
# Total mass and corridor decay of the enriched connected target submeasure

The targetwise connected contribution is a genuine submeasure of the product
enriched blocked law.  This module sums it over the complete enriched target
square.  Finite Fubini moves the target sum inside the embedded connected
source list; exact stochasticity collapses each two-copy output row.

The remaining product of normalized expanded-source masses is exactly the
accepted paired Gibbs weight divided by the physical partition square.
Therefore the total target-submeasure mass equals the established normalized
support-connected source mass and inherits its explicit SU(2) corridor decay.

No target observable or reflection identity is asserted: the theorem controls
the canonical connected contribution itself.  No strict form bound,
continuum limit, or Clay theorem is claimed.

## Axiom gate

Finite Fubini, exact stochastic row normalization, and rational quotient
algebra only.  No classical choice, placeholder, trusted external computation,
computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetMass

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.BF4SU2FineIntertwinerPhysicalDisintegration
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetSubmeasure
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerExpandedMarginal
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Target normalization of one expanded source -/

/-- Summing one normalized expanded-source joint density over every enriched
target returns that source's normalized expanded mass. -/
theorem allCutoffExpandedSourceJointWeight_target_total
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (source : AllCutoffExpandedSource S.fine) :
    listQSum
        (fun target => allCutoffExpandedSourceJointWeight S target source)
        (allCutoffRetainedTargets S) ≈
      allCutoffExpandedSourceNormalizedMass S.fine source := by
  unfold allCutoffExpandedSourceJointWeight
    allCutoffExpandedSourceKernel
  refine Q'.eqv_trans _
    (allCutoffExpandedSourceNormalizedMass S.fine source *
      listQSum
        (allCutoffRetainedFineIntertwinerKernel S source.1)
        (allCutoffRetainedTargets S)) _ ?_ ?_
  · exact listQSum_mul_left
      (allCutoffExpandedSourceNormalizedMass S.fine source)
      (allCutoffRetainedFineIntertwinerKernel S source.1)
      (allCutoffRetainedTargets S)
  · refine Q'.eqv_trans _
      (allCutoffExpandedSourceNormalizedMass S.fine source * 1) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _
        (allCutoffRetainedFineIntertwinerKernel_row_normalized
          S hfineCutoff source.1)
    · exact Q'.mul_one_eqv _

/-- The complete two-copy enriched target row above one attached expanded
source pair sums to the product of the two normalized source masses. -/
theorem allCutoffExpandedSourceEntryPairTargetWeight_total
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (sources : AllCutoffExpandedSourceEntry S.fine ×
      AllCutoffExpandedSourceEntry S.fine) :
    listQSum
        (fun target =>
          allCutoffExpandedSourceEntryPairTargetWeight S target sources)
        (allCutoffRetainedTwoReplicaTargets S) ≈
      allCutoffExpandedSourceNormalizedMass S.fine sources.1.1 *
        allCutoffExpandedSourceNormalizedMass S.fine sources.2.1 := by
  refine Q'.eqv_trans _
    (listQSum
        (fun target =>
          allCutoffExpandedSourceJointWeight S target sources.1.1)
        (allCutoffRetainedTargets S) *
      listQSum
        (fun target =>
          allCutoffExpandedSourceJointWeight S target sources.2.1)
        (allCutoffRetainedTargets S)) _ ?_ ?_
  · exact listQSum_cartesian_product
      (fun target =>
        allCutoffExpandedSourceJointWeight S target sources.1.1)
      (fun target =>
        allCutoffExpandedSourceJointWeight S target sources.2.1)
      (allCutoffRetainedTargets S) (allCutoffRetainedTargets S)
  · exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_right _ _ _
        (allCutoffExpandedSourceJointWeight_target_total
          S hfineCutoff sources.1.1))
      (Q'.mul_eqv_congr_left _ _ _
        (allCutoffExpandedSourceJointWeight_target_total
          S hfineCutoff sources.2.1))

/-! ## 2. Expanded normalization equals accepted-pair normalization -/

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

private theorem mul4_rearrange_local (a b c d : Q') :
    (a * b) * (c * d) ≈ (a * c) * (b * d) :=
  Q'.eqv_trans _ _ _ (Q'.mul_assoc_eqv a b (c * d))
    (Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left a (b * (c * d)) ((b * c) * d)
        (Q'.eqv_symm (Q'.mul_assoc_eqv b c d)))
      (Q'.eqv_trans _ _ _
        (Q'.mul_eqv_congr_left a ((b * c) * d) ((c * b) * d)
          (Q'.mul_eqv_congr_right (b * c) (c * b) d
            (Q'.mul_comm_eqv b c)))
        (Q'.eqv_trans _ _ _
          (Q'.mul_eqv_congr_left a ((c * b) * d) (c * (b * d))
            (Q'.mul_assoc_eqv c b d))
          (Q'.eqv_symm (Q'.mul_assoc_eqv a c (b * d))))))

private theorem divPos_eqv_of_eqv_mul_local {p q c : Q'}
    (hq : (0 : Q') < q) (h : p ≈ c * q) :
    Q'.divPos p q hq ≈ c := by
  unfold Q'.divPos
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ h) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_assoc_eqv c q (Q'.recipPos q hq)) ?_
  refine Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_left c _ _ (Q'.mul_recipPos_eqv q hq)) ?_
  exact Q'.mul_one_eqv c

private theorem divPos_mul_divPos_same_denominator
    (left right denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos left denominator hdenominator *
        Q'.divPos right denominator hdenominator ≈
      Q'.divPos (left * right) (denominator * denominator)
        (Q'.mul_pos hdenominator hdenominator) := by
  apply Q'.eqv_symm
  apply divPos_eqv_of_eqv_mul_local
  refine Q'.eqv_trans _
    ((Q'.divPos left denominator hdenominator * denominator) *
      (Q'.divPos right denominator hdenominator * denominator)) _ ?_ ?_
  · exact Q'.eqv_symm
      (mul_eqv_both_local
        (Q'.divPos_mul_eqv left denominator hdenominator)
        (Q'.divPos_mul_eqv right denominator hdenominator))
  · exact mul4_rearrange_local
      (Q'.divPos left denominator hdenominator) denominator
      (Q'.divPos right denominator hdenominator) denominator

/-- For an observable expanded source pair, the product of its two grouped
normalized masses is exactly its paired Gibbs weight over the partition
square. -/
theorem slabObservablePairExpandedNormalizedMass_eqv
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    allCutoffExpandedSourceNormalizedMass D
          (slabObservablePairLeftExpandedSourceEntry D pair).1 *
        allCutoffExpandedSourceNormalizedMass D
          (slabObservablePairRightExpandedSourceEntry D pair).1 ≈
      Q'.divPos
        (slabObservableTwoReplicaPairWeight D pair)
        (D.physicalPartition * D.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)
          (slabParametricKPhysicalPartition_pos
            D.coupling_nonnegative D.cutoff D.extent)) := by
  simpa only [allCutoffExpandedSourceNormalizedMass,
    allCutoffExpandedSourceWeight,
    slabObservablePairLeftExpandedSourceEntry,
    slabObservablePairRightExpandedSourceEntry,
    slabObservablePairLeftPhysicalSource,
    slabObservablePairRightPhysicalSource,
    slabObservableTwoReplicaPairWeight,
    slabObservablePositiveEntryWeight,
    slabExpandedFineEntryWeight,
    slabExpandedFineSourceWeight] using
      divPos_mul_divPos_same_denominator
        (retainedFineIntertwinerPhysicalFiberWeight
          D pair.1.1.1 pair.1.1.2)
        (retainedFineIntertwinerPhysicalFiberWeight
          D pair.2.1.1 pair.2.1.2)
        D.physicalPartition
        (slabParametricKPhysicalPartition_pos
          D.coupling_nonnegative D.cutoff D.extent)

/-! ## 3. Total target mass and the corridor estimate -/

def allCutoffConnectedExpandedTargetTotalMass
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) : Q' :=
  listQSum
    (allCutoffConnectedExpandedTargetContribution
      S rootFaceId targetFaceId)
    (allCutoffRetainedTwoReplicaTargets S)

/-- Summing the connected target submeasure gives exactly the normalized
paired-support connected source mass. -/
theorem allCutoffConnectedExpandedTargetTotalMass_eqv_connectedMass
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (rootFaceId targetFaceId : Nat) :
    allCutoffConnectedExpandedTargetTotalMass
        S rootFaceId targetFaceId ≈
      slabObservableNormalizedPairedSupportConnectedMass
        S.fine rootFaceId targetFaceId := by
  let sourcePairs := allCutoffConnectedExpandedSourceEntryPairs
    S rootFaceId targetFaceId
  let targetPairs := allCutoffRetainedTwoReplicaTargets S
  refine Q'.eqv_trans _
    (listQSum
      (fun sources =>
        listQSum
          (fun target =>
            allCutoffExpandedSourceEntryPairTargetWeight S target sources)
          targetPairs)
      sourcePairs) _ ?_ ?_
  · unfold allCutoffConnectedExpandedTargetTotalMass
      allCutoffConnectedExpandedTargetContribution
    exact listQSum_swap
      (fun sources target =>
        allCutoffExpandedSourceEntryPairTargetWeight S target sources)
      sourcePairs targetPairs
  refine Q'.eqv_trans _
    (listQSum
      (fun sources =>
        allCutoffExpandedSourceNormalizedMass S.fine sources.1.1 *
          allCutoffExpandedSourceNormalizedMass S.fine sources.2.1)
      sourcePairs) _ ?_ ?_
  · apply listQSum_congr
    intro sources
    exact allCutoffExpandedSourceEntryPairTargetWeight_total
      S hfineCutoff sources
  refine Q'.eqv_trans _
    (listQSum
      (fun pair =>
        Q'.divPos
          (slabObservableTwoReplicaPairWeight S.fine pair)
          (S.fine.physicalPartition * S.fine.physicalPartition)
          (Q'.mul_pos
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative
              S.fine.cutoff S.fine.extent)
            (slabParametricKPhysicalPartition_pos
              S.fine.coupling_nonnegative
              S.fine.cutoff S.fine.extent)))
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine rootFaceId targetFaceId)) _ ?_ ?_
  · unfold sourcePairs allCutoffConnectedExpandedSourceEntryPairs
    rw [listQSum_map]
    apply listQSum_congr
    intro pair
    exact slabObservablePairExpandedNormalizedMass_eqv S.fine pair
  · unfold slabObservableNormalizedPairedSupportConnectedMass Q'.divPos
    exact listQSum_mul_right
      (slabObservableTwoReplicaPairWeight S.fine)
      (Q'.recipPos
        (S.fine.physicalPartition * S.fine.physicalPartition)
        (Q'.mul_pos
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative
            S.fine.cutoff S.fine.extent)
          (slabParametricKPhysicalPartition_pos
            S.fine.coupling_nonnegative
            S.fine.cutoff S.fine.extent)))
      (slabObservablePairedSupportConnectedFourCellSourcePairs
        S.fine rootFaceId targetFaceId)

/-- The total enriched connected target submeasure has the explicit SU(2)
geometric rate throughout the fully named strong-coupling corridor. -/
theorem allCutoffConnectedExpandedTargetTotalMass_le_corridorRate
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (hw0 : (0 : Q') < S.fine.coupling)
    (hw1 : S.fine.coupling < (1 : Q'))
    (hwAnchor : S.fine.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent) :
    allCutoffConnectedExpandedTargetTotalMass
        S rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        S.fine rootFaceId targetFaceId :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (allCutoffConnectedExpandedTargetTotalMass_eqv_connectedMass
        S hfineCutoff rootFaceId targetFaceId))
    (slabObservableNormalizedPairedSupportConnectedMass_le_corridorRate
      S.fine hw0 hw1 hwAnchor rootFaceId targetFaceId htarget)

/-! ## Axiom audit -/

#print axioms allCutoffExpandedSourceJointWeight_target_total
#print axioms slabObservablePairExpandedNormalizedMass_eqv
#print axioms allCutoffConnectedExpandedTargetTotalMass_eqv_connectedMass
#print axioms allCutoffConnectedExpandedTargetTotalMass_le_corridorRate

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedTargetMass
