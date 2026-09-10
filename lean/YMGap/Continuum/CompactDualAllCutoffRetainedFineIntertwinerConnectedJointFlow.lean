/-
# Source-labelled connected joint flow through every enriched output sector

The component estimate is naturally stated on expanded two-replica source
pairs, whereas the corrected all-cutoff kernel has coarse and retained output
branches.  The mathematically lossless common object is therefore the joint
law: keep the expanded source pair as a label and append the two independent
enriched kernel outputs.

This module constructs that conditional finite law on the support-connected
observable carrier.  Its output fiber includes coarse/coarse, coarse/retained,
retained/coarse, and retained/retained targets.  Exact stochastic row
normalization contracts the complete output fiber to one, so its normalized
connected mass is exactly the previously bounded normalized connected Gibbs
mass.  The explicit SU(2) corridor rate therefore controls the complete joint
flow without discarding the source component witness.

The target marginal is not yet identified here with the product enriched
blocked law.  Nor is an output observable, reflection lift, strict form bound,
continuum limit, or Clay theorem claimed.

## Axiom gate

Finite Cartesian summation, exact kernel row normalization, and rational
quotient algebra only.  No classical choice, placeholder, trusted external
computation, computability escape, heartbeat increase, or new axiom.
-/

import YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor

namespace YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow

set_option autoImplicit false
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerKernel
open YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedCorridor
open YMGap.Continuum.CompactDualFiniteBlockRemainder
open YMGap.Continuum.CompactDualSlabExpandedSourceEnumeration
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The complete paired enriched output fiber -/

/-- The fine physical source underlying the positive first replica. -/
def slabObservablePairLeftPhysicalSource
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SlabPhysicalSourceEntry D :=
  ⟨pair.1.1.1,
    (mem_slabExpandedFineSources_iff.mp
      pair.1.source_mem_expanded).1⟩

/-- The fine physical source underlying the second replica. -/
def slabObservablePairRightPhysicalSource
    (D : SlabPhysicalData) {rootFaceId : Nat}
    (pair : SlabObservableTwoReplicaPair D rootFaceId) :
    SlabPhysicalSourceEntry D :=
  ⟨pair.2.1.1,
    (mem_slabExpandedFineSources_iff.mp pair.2.2).1⟩

/-- Every ordered pair of corrected coarse-or-retained targets. -/
def allCutoffRetainedTwoReplicaTargets (S : SlabScalePair) :
    List (AllCutoffRetainedTarget × AllCutoffRetainedTarget) :=
  cartesian (allCutoffRetainedTargets S) (allCutoffRetainedTargets S)

/-- Product conditional row from one expanded observable source pair to one
ordered pair of enriched outputs. -/
def allCutoffRetainedTwoReplicaKernel
    (S : SlabScalePair) {rootFaceId : Nat}
    (source : SlabObservableTwoReplicaPair S.fine rootFaceId)
    (target : AllCutoffRetainedTarget × AllCutoffRetainedTarget) : Q' :=
  allCutoffRetainedFineIntertwinerKernel S
      (slabObservablePairLeftPhysicalSource S.fine source) target.1 *
    allCutoffRetainedFineIntertwinerKernel S
      (slabObservablePairRightPhysicalSource S.fine source) target.2

private theorem mul_eqv_both_local {a a' b b' : Q'}
    (ha : a ≈ a') (hb : b ≈ b') : a * b ≈ a' * b' :=
  Q'.eqv_trans _ _ _
    (Q'.mul_eqv_congr_right _ _ _ ha)
    (Q'.mul_eqv_congr_left _ _ _ hb)

/-- The product enriched output row has exact mass one and includes all four
coarse/retained branch combinations. -/
theorem allCutoffRetainedTwoReplicaKernel_row_normalized
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    {rootFaceId : Nat}
    (source : SlabObservableTwoReplicaPair S.fine rootFaceId) :
    listQSum (allCutoffRetainedTwoReplicaKernel S source)
        (allCutoffRetainedTwoReplicaTargets S) ≈ 1 := by
  refine Q'.eqv_trans _
    (listQSum
        (allCutoffRetainedFineIntertwinerKernel S
          (slabObservablePairLeftPhysicalSource S.fine source))
        (allCutoffRetainedTargets S) *
      listQSum
        (allCutoffRetainedFineIntertwinerKernel S
          (slabObservablePairRightPhysicalSource S.fine source))
        (allCutoffRetainedTargets S)) _ ?_ ?_
  · exact listQSum_cartesian_product
      (allCutoffRetainedFineIntertwinerKernel S
        (slabObservablePairLeftPhysicalSource S.fine source))
      (allCutoffRetainedFineIntertwinerKernel S
        (slabObservablePairRightPhysicalSource S.fine source))
      (allCutoffRetainedTargets S) (allCutoffRetainedTargets S)
  · refine Q'.eqv_trans _ (1 * 1) _ ?_ ?_
    · exact mul_eqv_both_local
        (allCutoffRetainedFineIntertwinerKernel_row_normalized
          S hfineCutoff
            (slabObservablePairLeftPhysicalSource S.fine source))
        (allCutoffRetainedFineIntertwinerKernel_row_normalized
          S hfineCutoff
            (slabObservablePairRightPhysicalSource S.fine source))
    · exact Q'.one_mul_eqv 1

/-! ## 2. The source-labelled connected joint law -/

/-- Unnormalized mass of the support-connected expanded source pairs together
with every possible pair of enriched kernel outputs. -/
def allCutoffRetainedConnectedJointRawMass
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) : Q' :=
  listQSum
    (fun source =>
      slabObservableTwoReplicaPairWeight S.fine source *
        listQSum (allCutoffRetainedTwoReplicaKernel S source)
          (allCutoffRetainedTwoReplicaTargets S))
    (slabObservablePairedSupportConnectedFourCellSourcePairs
      S.fine rootFaceId targetFaceId)

/-- Normalized probability of that complete source-labelled connected joint
event. -/
def allCutoffRetainedConnectedJointMass
    (S : SlabScalePair) (rootFaceId targetFaceId : Nat) : Q' :=
  Q'.divPos
    (allCutoffRetainedConnectedJointRawMass S rootFaceId targetFaceId)
    (S.fine.physicalPartition * S.fine.physicalPartition)
    (Q'.mul_pos
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent)
      (slabParametricKPhysicalPartition_pos
        S.fine.coupling_nonnegative S.fine.cutoff S.fine.extent))

/-- Summing every enriched output branch loses no connected source mass: each
conditional output fiber has mass exactly one. -/
theorem allCutoffRetainedConnectedJointRawMass_eqv_connectedWeight
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (rootFaceId targetFaceId : Nat) :
    allCutoffRetainedConnectedJointRawMass
        S rootFaceId targetFaceId ≈
      listQSum (slabObservableTwoReplicaPairWeight S.fine)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          S.fine rootFaceId targetFaceId) := by
  unfold allCutoffRetainedConnectedJointRawMass
  apply listQSum_congr_on
  intro source _
  refine Q'.eqv_trans _
    (slabObservableTwoReplicaPairWeight S.fine source * 1) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left _ _ _
      (allCutoffRetainedTwoReplicaKernel_row_normalized
        S hfineCutoff source)
  · exact Q'.mul_one_eqv _

/-- After normalization, the complete joint-flow connected mass is exactly
the established normalized connected Gibbs mass. -/
theorem allCutoffRetainedConnectedJointMass_eqv_connectedMass
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (rootFaceId targetFaceId : Nat) :
    allCutoffRetainedConnectedJointMass
        S rootFaceId targetFaceId ≈
      slabObservableNormalizedPairedSupportConnectedMass
        S.fine rootFaceId targetFaceId := by
  unfold allCutoffRetainedConnectedJointMass
    slabObservableNormalizedPairedSupportConnectedMass Q'.divPos
  exact Q'.mul_eqv_congr_right _ _ _
    (allCutoffRetainedConnectedJointRawMass_eqv_connectedWeight
      S hfineCutoff rootFaceId targetFaceId)

/-! ## 3. Complete branch coverage inherits the corridor rate -/

/-- The complete source-labelled flow through all coherent, retained, and
mixed output branches obeys the explicit SU(2) connected-component rate. -/
theorem allCutoffRetainedConnectedJointMass_le_corridorRate
    (S : SlabScalePair) (hfineCutoff : 1 ≤ S.fine.cutoff)
    (hw0 : (0 : Q') < S.fine.coupling)
    (hw1 : S.fine.coupling < (1 : Q'))
    (hwAnchor : S.fine.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges S.fine.extent) :
    allCutoffRetainedConnectedJointMass
        S rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        S.fine rootFaceId targetFaceId :=
  Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (allCutoffRetainedConnectedJointMass_eqv_connectedMass
        S hfineCutoff rootFaceId targetFaceId))
    (slabObservableNormalizedPairedSupportConnectedMass_le_corridorRate
      S.fine hw0 hw1 hwAnchor rootFaceId targetFaceId htarget)

/-! ## Axiom audit -/

#print axioms allCutoffRetainedTwoReplicaKernel_row_normalized
#print axioms allCutoffRetainedConnectedJointRawMass_eqv_connectedWeight
#print axioms allCutoffRetainedConnectedJointMass_eqv_connectedMass
#print axioms allCutoffRetainedConnectedJointMass_le_corridorRate

end YMGap.Continuum.CompactDualAllCutoffRetainedFineIntertwinerConnectedJointFlow
