/-
# Global observable decay on the explicit coupling corridor

The coupling-sensitive profile closes every fixed-terminal, fixed-mass source
fiber at the common rate `16/25` whenever `0 < w <= 1/400`.  This module
performs the remaining exact finite Fubini steps:

1. sum all accepted terminals to the genuine partition square;
2. sum all masses above the observable separation floor geometrically;
3. divide by that same positive partition square; and
4. apply the arbitrary-coupling two-replica switch reduction.

The result is the cutoff- and finite-volume-independent bound

  covariance <= (25/9) * (16/25)^(linfDistance + 1)

throughout the whole explicit strong-coupling corridor.  This extends the
previous production-point theorem from `w = 1/400` to every rational
`0 < w <= 1/400`.  It does not reach couplings above the corridor, a continuum
trajectory, an all-observable OS/GNS operator gap, or physical mass
normalization.

Constructive contract: finite deterministic fibers, exact Cartesian Fubini,
positive rational division, and the proved corridor fiber estimate only; no
choice, `Classical`, `native_decide`, `sorry`, noncomputable declaration, or
new axiom.
-/

import YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
import YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
import YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
import YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingCorridor

namespace YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

open YMGap.Constructive
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeeling
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingArbitraryCouplingWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedCanonicalPeelingSupportMass
open YMGap.Continuum.CompactDualSlabAcceptedPairedPeel
open YMGap.Continuum.CompactDualSlabHighSpinFacePeelWeight
open YMGap.Continuum.CompactDualSlabAcceptedPairedStateCarrier
open YMGap.Continuum.CompactDualSlabObservableBooleanCovariance
open YMGap.Continuum.CompactDualSlabObservablePairedSupportArbitraryCouplingContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportConnectedMassFloor
open YMGap.Continuum.CompactDualSlabObservablePairedSupportFractionalWeightedContraction
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalDecay
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalPartition
open YMGap.Continuum.CompactDualSlabObservablePairedSupportGlobalWeight
open YMGap.Continuum.CompactDualSlabObservablePairedSupportHighSpinProfileCouplingCorridor
open YMGap.Continuum.CompactDualSlabObservableRemovalFiber
open YMGap.Continuum.CompactDualSlabObservableRemovalPartition
open YMGap.Continuum.CompactDualSlabObservableTwoReplicaSwitchReduction
open YMGap.Continuum.CompactDualSlabPhysicalData
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.SepLatticeZ4Linf
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private def expandedEntryDecidableEq
    (D : SlabPhysicalData) : DecidableEq (SlabExpandedFineSourceEntry D) :=
  fun left right =>
    if hkey : left.key = right.key then
      isTrue (SlabExpandedFineSourceEntry.eq_of_key_eq hkey)
    else
      isFalse (fun heq => hkey
        (congrArg SlabExpandedFineSourceEntry.key heq))

local instance (D : SlabPhysicalData) :
    DecidableEq (SlabExpandedFineSourceEntry D) :=
  expandedEntryDecidableEq D

/-! ## 1. Arbitrary-coupling accepted terminal mass -/

/-- The complete accepted paired carrier has exactly the physical partition
square at every nonnegative coupling, not only at the production anchor. -/
theorem slabAcceptedTwoReplicaStates_weight_total_general
    (D : SlabPhysicalData) :
    listQSum (slabAcceptedTwoReplicaStateWeight D)
        (slabAcceptedTwoReplicaStates D) ≈
      D.physicalPartition * D.physicalPartition := by
  have hcart := listQSum_cartesian_product
    (slabExpandedFineEntryWeight D)
    (slabExpandedFineEntryWeight D)
    (slabExpandedFineSourceEntries D)
    (slabExpandedFineSourceEntries D)
  have hpartition := slabExpandedFineSourceEntries_weight_total D
  refine Q'.eqv_trans _
    (listQSum (slabExpandedFineEntryWeight D)
        (slabExpandedFineSourceEntries D) *
      listQSum (slabExpandedFineEntryWeight D)
        (slabExpandedFineSourceEntries D)) _ ?_ ?_
  · simpa only [slabAcceptedTwoReplicaStates,
      slabAcceptedTwoReplicaStateWeight] using hcart
  · exact Q'.eqv_trans _
      (D.physicalPartition *
        listQSum (slabExpandedFineEntryWeight D)
          (slabExpandedFineSourceEntries D)) _
      (Q'.mul_eqv_congr_right _ _ _ hpartition)
      (Q'.mul_eqv_congr_left _ _ _ hpartition)

/-! ## 2. Exact terminal/mass Fubini on the corridor -/

/-- Every deterministic canonical terminal/mass fiber inherits the corridor
profile estimate. -/
theorem slabObservablePairedSupportCanonicalPeeling_fiberWeight_le_of_zeroCoefficient_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hzero : exteriorFaceCoefficient D.coupling 0 <= anchorFaceCoefficient)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (key : Nat × SlabAcceptedTwoReplicaState D) :
    fiberWeight
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairTargetSupportCanonicalPeelingKey
          D rootFaceId targetFaceId htarget)
        key <=
      slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
        slabAcceptedTwoReplicaStateWeight D key.2 := by
  unfold fiberWeight
  apply
    slabObservablePairTargetSupportCanonicalHighSpinProfile_fixedTerminalMass_weight_sum_le_of_zeroCoefficient_le
      D hw0 hw1 hzero rootFaceId targetFaceId key.1 htarget key.2
  · exact List.filter_sublist.nodup
      (slabObservablePairedSupportConnectedFourCellSourceEntries_nodup
        D rootFaceId targetFaceId)
  · intro source hsource
    have hkey := of_decide_eq_true (List.mem_filter.mp hsource).2
    exact (congrArg Prod.snd hkey).symm
  · intro source hsource
    have hkey := of_decide_eq_true (List.mem_filter.mp hsource).2
    exact (congrArg Prod.fst hkey).symm

/-- Corridor specialization of the coefficient-level deterministic fiber
bound. -/
theorem slabObservablePairedSupportCanonicalPeeling_fiberWeight_le_corridor
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent)
    (key : Nat × SlabAcceptedTwoReplicaState D) :
    fiberWeight
        (slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId)
        (fun source => slabObservableTwoReplicaPairWeight D source.1)
        (slabObservablePairTargetSupportCanonicalPeelingKey
          D rootFaceId targetFaceId htarget)
        key <=
      slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
        slabAcceptedTwoReplicaStateWeight D key.2 := by
  exact
    slabObservablePairedSupportCanonicalPeeling_fiberWeight_le_of_zeroCoefficient_le
      D hw0 hw1
        (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
          (Q'.le_of_lt hw0) hwAnchor)
        rootFaceId targetFaceId htarget key

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hle => by
      exact Q'.add_le_add
        (hle head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hle item (List.mem_cons_of_mem head hitem)))

/-- Summing every accepted terminal introduces exactly the physical partition
square and no terminal-count prefactor. -/
theorem slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum_of_zeroCoefficient_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hzero : exteriorFaceCoefficient D.coupling 0 <= anchorFaceCoefficient)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    let floor := linfDist
      (slabPlaquetteAt D.extent rootFaceId)
      (slabPlaquetteAt D.extent targetFaceId) + 1
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) <=
      listQSum
          (fun mass =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
          (slabObservablePairedSupportPaidMasses D floor) *
        (D.physicalPartition * D.physicalPartition) := by
  let floor := linfDist
    (slabPlaquetteAt D.extent rootFaceId)
    (slabPlaquetteAt D.extent targetFaceId) + 1
  have hfloor : forall source, source ∈
        slabObservablePairedSupportConnectedFourCellSourceEntries
          D rootFaceId targetFaceId ->
      floor <= slabAcceptedPairedPeelTraceMass
        (slabObservablePairTargetSupportCanonicalPeeling
          D rootFaceId targetFaceId htarget source.1 source.2).2 := by
    intro source hsource
    exact
      slabObservablePairTargetSupportCanonicalPeeling_traceMass_floor
        D rootFaceId targetFaceId htarget source.1 source.2
          (slabObservablePairedSupportConnectedEntry_connected
            D rootFaceId targetFaceId source hsource)
  have hpartition :=
    slabObservablePairedSupportCanonicalPeeling_fiberWeight_total
      D rootFaceId targetFaceId floor htarget hfloor
  have hfibers :
      listQSum
          (fiberWeight
            (slabObservablePairedSupportConnectedFourCellSourceEntries
              D rootFaceId targetFaceId)
            (fun source => slabObservableTwoReplicaPairWeight D source.1)
            (slabObservablePairTargetSupportCanonicalPeelingKey
              D rootFaceId targetFaceId htarget))
          (slabObservablePairedSupportCanonicalPeelingKeyCarrier
            D floor) <=
        listQSum
          (fun key =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ key.1 *
              slabAcceptedTwoReplicaStateWeight D key.2)
          (slabObservablePairedSupportCanonicalPeelingKeyCarrier
            D floor) := by
    apply listQSum_le_termwise_local
    intro key _
    exact
      slabObservablePairedSupportCanonicalPeeling_fiberWeight_le_of_zeroCoefficient_le
        D hw0 hw1 hzero rootFaceId targetFaceId htarget key
  have hcart := listQSum_cartesian_product
    (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
    (slabAcceptedTwoReplicaStateWeight D)
    (slabObservablePairedSupportPaidMasses D floor)
    (slabAcceptedTwoReplicaStates D)
  have hterminals := slabAcceptedTwoReplicaStates_weight_total_general D
  have hentries :=
    slabObservablePairedSupportConnectedFourCellSourceEntries_weight
      D rootFaceId targetFaceId
  refine Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_trans _ _ _
      (Q'.eqv_of_eq hentries.symm) (Q'.eqv_symm hpartition))) ?_
  refine Q'.le_trans' _ _ _ hfibers ?_
  apply Q'.le_of_eqv
  refine Q'.eqv_trans _
    (listQSum
        (fun mass => slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
        (slabObservablePairedSupportPaidMasses D floor) *
      listQSum (slabAcceptedTwoReplicaStateWeight D)
        (slabAcceptedTwoReplicaStates D)) _ ?_ ?_
  · simpa only [slabObservablePairedSupportCanonicalPeelingKeyCarrier]
      using hcart
  · exact Q'.mul_eqv_congr_left _ _ _ hterminals

/-- Corridor specialization of the coefficient-level exact terminal/mass
Fubini bound. -/
theorem slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum_corridor
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    let floor := linfDist
      (slabPlaquetteAt D.extent rootFaceId)
      (slabPlaquetteAt D.extent targetFaceId) + 1
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) <=
      listQSum
          (fun mass =>
            slabObservablePairedGlobalEntropyAnchorRatio ^ mass)
          (slabObservablePairedSupportPaidMasses D floor) *
        (D.physicalPartition * D.physicalPartition) := by
  exact
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum_of_zeroCoefficient_le
      D hw0 hw1
        (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
          (Q'.le_of_lt hw0) hwAnchor)
        rootFaceId targetFaceId htarget

/-! ## 3. Geometric decay and normalized covariance -/

/-- The unnormalized connected carrier has the same volume-independent
geometric envelope throughout the explicit corridor. -/
theorem slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare_of_zeroCoefficient_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hzero : exteriorFaceCoefficient D.coupling 0 <= anchorFaceCoefficient)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) <=
      slabObservablePairedSupportGlobalAnchorRate
          D rootFaceId targetFaceId *
        (D.physicalPartition * D.physicalPartition) := by
  let floor := linfDist
    (slabPlaquetteAt D.extent rootFaceId)
    (slabPlaquetteAt D.extent targetFaceId) + 1
  have hpartition :=
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum_of_zeroCoefficient_le
      D hw0 hw1 hzero rootFaceId targetFaceId htarget
  have hmass := slabObservablePairedSupportPaidMasses_weight_le D floor
  have hpartitionNonnegative :
      (0 : Q') <= D.physicalPartition * D.physicalPartition :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
      (Q'.le_of_lt (slabParametricKPhysicalPartition_pos
        D.coupling_nonnegative D.cutoff D.extent))
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _
    (D.physicalPartition * D.physicalPartition)
    hmass hpartitionNonnegative
  exact Q'.le_trans' _ _ _ hpartition hscaled

/-- Corridor specialization of the coefficient-level unnormalized connected
carrier bound. -/
theorem slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare_corridor
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    listQSum (slabObservableTwoReplicaPairWeight D)
        (slabObservablePairedSupportConnectedFourCellSourcePairs
          D rootFaceId targetFaceId) <=
      slabObservablePairedSupportGlobalAnchorRate
          D rootFaceId targetFaceId *
        (D.physicalPartition * D.physicalPartition) := by
  exact
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare_of_zeroCoefficient_le
      D hw0 hw1
        (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
          (Q'.le_of_lt hw0) hwAnchor)
        rootFaceId targetFaceId htarget

/-- The normalized connected two-replica mass has the common strict
geometric rate on the full corridor. -/
theorem slabObservableNormalizedPairedSupportConnectedMass_le_of_zeroCoefficient_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hzero : exteriorFaceCoefficient D.coupling 0 <= anchorFaceCoefficient)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        D rootFaceId targetFaceId := by
  unfold slabObservableNormalizedPairedSupportConnectedMass
  apply Q'.divPos_le_of_le_mul
  exact
    slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare_of_zeroCoefficient_le
      D hw0 hw1 hzero rootFaceId targetFaceId htarget

/-- Corridor specialization of the coefficient-level normalized connected
mass bound. -/
theorem slabObservableNormalizedPairedSupportConnectedMass_le_corridorRate
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservableNormalizedPairedSupportConnectedMass
        D rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        D rootFaceId targetFaceId := by
  exact
    slabObservableNormalizedPairedSupportConnectedMass_le_of_zeroCoefficient_le
      D hw0 hw1
        (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
          (Q'.le_of_lt hw0) hwAnchor)
        rootFaceId targetFaceId htarget

/-- **Same-object finite-volume corridor decay.**  The literal centered
Boolean face covariance is bounded by the cutoff- and volume-independent
`(25/9)*(16/25)^(distance+1)` envelope for every `0 < w <= 1/400`. -/
theorem slabObservableFaceBooleanCovariance_le_of_zeroCoefficient_le
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hzero : exteriorFaceCoefficient D.coupling 0 <= anchorFaceCoefficient)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservableFaceBooleanCovariance
        D rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        D rootFaceId targetFaceId := by
  exact Q'.le_trans' _ _ _
    (slabObservableFaceBooleanCovariance_le_pairedSupportConnectedMass
      D rootFaceId targetFaceId htarget)
    (slabObservableNormalizedPairedSupportConnectedMass_le_of_zeroCoefficient_le
      D hw0 hw1 hzero rootFaceId targetFaceId htarget)

/-- **Same-object finite-volume corridor decay.**  The literal centered
Boolean face covariance is bounded by the cutoff- and volume-independent
`(25/9)*(16/25)^(distance+1)` envelope for every `0 < w <= 1/400`. -/
theorem slabObservableFaceBooleanCovariance_le_corridorRate
    (D : SlabPhysicalData)
    (hw0 : (0 : Q') < D.coupling)
    (hw1 : D.coupling < (1 : Q'))
    (hwAnchor : D.coupling <= anchorCoupling)
    (rootFaceId targetFaceId : Nat)
    (htarget : targetFaceId ∈ slabPhysicalFaceEdges D.extent) :
    slabObservableFaceBooleanCovariance
        D rootFaceId targetFaceId <=
      slabObservablePairedSupportGlobalAnchorRate
        D rootFaceId targetFaceId := by
  exact slabObservableFaceBooleanCovariance_le_of_zeroCoefficient_le
    D hw0 hw1
      (exteriorFaceCoefficient_zero_le_anchorFaceCoefficient
        (Q'.le_of_lt hw0) hwAnchor)
      rootFaceId targetFaceId htarget

#print axioms slabAcceptedTwoReplicaStates_weight_total_general
#print axioms slabObservablePairedSupportCanonicalPeeling_fiberWeight_le_of_zeroCoefficient_le
#print axioms slabObservablePairedSupportCanonicalPeeling_fiberWeight_le_corridor
#print axioms slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum_of_zeroCoefficient_le
#print axioms slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_massSum_corridor
#print axioms slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare_of_zeroCoefficient_le
#print axioms slabObservablePairedSupportConnectedFourCellSourcePairs_weight_le_partitionSquare_corridor
#print axioms slabObservableNormalizedPairedSupportConnectedMass_le_of_zeroCoefficient_le
#print axioms slabObservableNormalizedPairedSupportConnectedMass_le_corridorRate
#print axioms slabObservableFaceBooleanCovariance_le_of_zeroCoefficient_le
#print axioms slabObservableFaceBooleanCovariance_le_corridorRate

end YMGap.Continuum.CompactDualSlabObservablePairedSupportCouplingCorridorDecay
