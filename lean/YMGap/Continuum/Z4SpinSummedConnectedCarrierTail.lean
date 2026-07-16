/-
# Uniform spin-summed tail for connected singleton residues

The canonical shifted carrier shells and both oriented injections are purely
geometric.  Reweighting them by the arbitrary-cutoff support-family activity
and the decorated face envelope gives a uniform geometric tail with ratio
`anchorDecoratedEffectiveRatio = 1/4` and exact background factor
`Z_target * Z_embedded,target`.
-/

import YMGap.Continuum.Z4CanonicalConnectedCarrierTail
import YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail
import YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize

namespace YMGap.Continuum.Z4SpinSummedConnectedCarrierTail

set_option maxRecDepth 100000
set_option maxHeartbeats 3000000

open YMGap.Constructive
open YMGap.Constructive.RationalTail
open YMGap.Continuum
open YMGap.Continuum.CayleyInjection
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.FiniteWeightedCartesianInjection
open YMGap.Continuum.PinnedCluster
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4CanonicalBoundaryRightRootSummation
open YMGap.Continuum.Z4CanonicalBoundarySwitchSummation
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedCarrierTail
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SpinSummedColoredSupportWeight
open YMGap.Continuum.Z4SpinSummedCompatibleGas
open YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize
open YMGap.Continuum.Z4SpinSummedConnectedCarrierWeight
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4SpinSummedSupportComponentUpper
open YMGap.Continuum.Z4SpinSummedTargetCylinderRatio
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

def spinSummedShiftedCarrierTargetWeight
    (cutoff n floor : Nat) (tagged : Nat × ConnectedCarrier) : Q' :=
  spinSummedConnectedCarrierTargetWeight cutoff n
    (floor + tagged.1) tagged.2

theorem spinSummedShiftedCarrierTargetSum_eqv_finSum
    (cutoff small n rootFace floor : Nat) : ∀ depth : Nat,
    listQSum (spinSummedShiftedCarrierTargetWeight cutoff n floor)
        (shiftedCarrierTargetList small n rootFace floor depth) ≈
      finSum (fun offset =>
        listQSum
          (spinSummedConnectedCarrierTargetWeight cutoff n
            (floor + offset))
          (connectedCarrierTargetList small n rootFace
            (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold shiftedCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append
          (spinSummedShiftedCarrierTargetWeight cutoff n floor)
          (shiftedCarrierTargetList small n rootFace floor depth)
          ((connectedCarrierTargetList small n rootFace
              (floor + depth)).map (fun carrier => (depth, carrier)))) ?_
      refine Q'.add_eqv_congr'
        (spinSummedShiftedCarrierTargetSum_eqv_finSum
          cutoff small n rootFace floor depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

/-! ## 1. Forward shifted-shell injection -/

theorem spinSummedConnectedSourcePairSum_le_shiftedTarget
    (cutoff : Nat) {small n inner distance start : Nat}
    {root : List Nat} (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (spinSummedSourcePairWeight cutoff)
        (connectedSourcePairs (root := root) hsmall) ≤
      listQSum (spinSummedShiftedCarrierTargetWeight
          cutoff n (distance + 2))
        (shiftedCarrierTargetList small n start (distance + 2)
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedSourcePairs (root := root) hsmall).attach
    (shiftedCarrierTargetList small n start (distance + 2)
      ((physicalFaceEdges n).length + 1))
    (fun entry : ConnectedSourceEntry root hsmall =>
      spinSummedSourcePairWeight cutoff entry.val)
    (spinSummedShiftedCarrierTargetWeight cutoff n (distance + 2))
    (connectedCarrierShiftEncode hsmall (distance + 2))
    (attach_nodup_of_nodup _ (connectedSourcePairs_nodup hsmall root))
    (fun entry _ => by
      have hfloor := connectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hmax := connectedCarrierSupport_length_le_ambient hsmall entry
      let offset := (connectedCarrierSupport hsmall entry).length -
        (distance + 2)
      have hoffset : offset < (physicalFaceEdges n).length + 1 := by
        unfold offset
        omega
      have hsize :
          (connectedCarrierSupport hsmall entry).length =
            distance + 2 + offset := by
        unfold offset
        omega
      apply mem_shiftedCarrierTargetList_of_lt
        small n start (distance + 2)
        ((physicalFaceEdges n).length + 1) hoffset
      exact connectedCarrier_mem_target hsmall entry hstart hsize)
    (fun first _ second _ heq => by
      apply connectedCarrier_injective hsmall first second
      exact congrArg Prod.snd heq)
    (fun entry _ => by
      have hfloor := connectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hsize :
          distance + 2 +
              ((connectedCarrierSupport hsmall entry).length -
                (distance + 2)) =
            (connectedCarrierSupport hsmall entry).length := by
        omega
      have hbound :=
        spinSummedConnectedSourcePairWeight_le_support_background
          cutoff hsmall entry
      unfold connectedCarrierShiftEncode
        spinSummedShiftedCarrierTargetWeight
        spinSummedConnectedCarrierTargetWeight connectedCarrier
      rw [hsize]
      simpa [spinSummedConnectedBackgroundPairWeight] using hbound)
    (fun tagged _ => by
      unfold spinSummedShiftedCarrierTargetWeight
        spinSummedConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (parametricKSupportFamilyActivity_nonnegative
            cutoff n tagged.2.2.1)
          (parametricKSupportFamilyActivity_nonnegative
            cutoff n tagged.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

/-! ## 2. Mirrored shifted-shell injection -/

theorem spinSummedConnectedReverseSourcePairSum_le_shiftedTarget
    (cutoff : Nat) {small n inner distance start : Nat}
    {root : List Nat} (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (spinSummedReverseSourcePairWeight cutoff)
        (connectedReverseSourcePairs (root := root) hsmall) ≤
      listQSum (spinSummedShiftedCarrierTargetWeight
          cutoff n (distance + 2))
        (shiftedCarrierTargetList small n start (distance + 2)
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedReverseSourcePairs (root := root) hsmall).attach
    (shiftedCarrierTargetList small n start (distance + 2)
      ((physicalFaceEdges n).length + 1))
    (fun entry : ReverseConnectedSourceEntry root hsmall =>
      spinSummedReverseSourcePairWeight cutoff entry.val)
    (spinSummedShiftedCarrierTargetWeight cutoff n (distance + 2))
    (reverseConnectedCarrierShiftEncode hsmall (distance + 2))
    (attach_nodup_of_nodup _
      (connectedReverseSourcePairs_nodup hsmall root))
    (fun entry _ => by
      have hfloor := reverseConnectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hmax :=
        reverseConnectedCarrierSupport_length_le_ambient hsmall entry
      let offset := (reverseConnectedCarrierSupport hsmall entry).length -
        (distance + 2)
      have hoffset : offset < (physicalFaceEdges n).length + 1 := by
        unfold offset
        omega
      have hsize :
          (reverseConnectedCarrierSupport hsmall entry).length =
            distance + 2 + offset := by
        unfold offset
        omega
      apply mem_shiftedCarrierTargetList_of_lt
        small n start (distance + 2)
        ((physicalFaceEdges n).length + 1) hoffset
      exact reverseConnectedCarrier_mem_target
        hsmall entry hstart hsize)
    (fun first _ second _ heq => by
      apply reverseConnectedCarrier_injective hsmall first second
      exact congrArg Prod.snd heq)
    (fun entry _ => by
      have hfloor := reverseConnectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hsize :
          distance + 2 +
              ((reverseConnectedCarrierSupport hsmall entry).length -
                (distance + 2)) =
            (reverseConnectedCarrierSupport hsmall entry).length := by
        omega
      have hbound :=
        spinSummedReverseConnectedSourcePairWeight_le_support_background
          cutoff hsmall entry
      unfold reverseConnectedCarrierShiftEncode
        spinSummedShiftedCarrierTargetWeight
        spinSummedConnectedCarrierTargetWeight reverseConnectedCarrier
      rw [hsize]
      simpa [spinSummedReverseConnectedBackgroundPairWeight] using hbound)
    (fun tagged _ => by
      unfold spinSummedShiftedCarrierTargetWeight
        spinSummedConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (parametricKSupportFamilyActivity_nonnegative
            cutoff n tagged.2.2.1)
          (parametricKSupportFamilyActivity_nonnegative
            cutoff n tagged.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

/-! ## 3. Geometric summation -/

theorem spinSummedConnectedCarrierTargetSum_le_geom_partition
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (rootFace size : Nat) :
    listQSum (spinSummedConnectedCarrierTargetWeight cutoff n size)
        (connectedCarrierTargetList small n rootFace size) ≤
      anchorDecoratedEffectiveRatio ^ size *
        (parametricKCompatibleSupportGasPartition cutoff n *
          parametricKEmbeddedTargetPartition cutoff small n) := by
  have hfactor := spinSummedConnectedCarrierTargetSum_eqv
    cutoff hsmall rootFace size
  have hpartition0 : (0 : Q') ≤
      parametricKCompatibleSupportGasPartition cutoff n *
        parametricKEmbeddedTargetPartition cutoff small n :=
    Q'.mul_nonneg _ _
      (parametricKCompatibleSupportGasPartition_nonnegative cutoff n)
      (parametricKEmbeddedTargetPartition_nonnegative cutoff small n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedColoredPinnedSizeWeightSum_le_geom n rootFace size)
      hpartition0)

theorem spinSummedShiftedCarrierTargetSum_le_tail
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (rootFace floor depth : Nat) :
    listQSum (spinSummedShiftedCarrierTargetWeight cutoff n floor)
        (shiftedCarrierTargetList small n rootFace floor depth) ≤
      (parametricKCompatibleSupportGasPartition cutoff n *
          parametricKEmbeddedTargetPartition cutoff small n) *
        (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2) := by
  let partitionProduct :=
    parametricKCompatibleSupportGasPartition cutoff n *
      parametricKEmbeddedTargetPartition cutoff small n
  have htargets := spinSummedShiftedCarrierTargetSum_eqv_finSum
    cutoff small n rootFace floor depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (spinSummedConnectedCarrierTargetWeight cutoff n
              (floor + offset))
            (connectedCarrierTargetList small n rootFace
              (floor + offset))) depth ≤
        finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ (floor + offset) *
            partitionProduct) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        spinSummedConnectedCarrierTargetSum_le_geom_partition
          cutoff hsmall rootFace (floor + offset)) depth
  have hreorder :
      (finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ (floor + offset) *
            partitionProduct) depth).eqv
        (finSum (fun offset =>
          (partitionProduct * anchorDecoratedEffectiveRatio ^ floor) *
            anchorDecoratedEffectiveRatio ^ offset) depth) := by
    apply RationalTail.finSum_eqv_congr
    intro offset
    refine Q'.eqv_trans _ _ _
      (Q'.mul_comm_eqv
        (anchorDecoratedEffectiveRatio ^ (floor + offset))
        partitionProduct) ?_
    refine Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left partitionProduct _ _
        (Q'.pow_add_eqv anchorDecoratedEffectiveRatio floor offset)) ?_
    exact Q'.eqv_symm
      (Q'.mul_assoc_eqv partitionProduct
        (anchorDecoratedEffectiveRatio ^ floor)
        (anchorDecoratedEffectiveRatio ^ offset))
  have hpull :
      (finSum (fun offset =>
          (partitionProduct * anchorDecoratedEffectiveRatio ^ floor) *
            anchorDecoratedEffectiveRatio ^ offset) depth).eqv
        ((partitionProduct * anchorDecoratedEffectiveRatio ^ floor) *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth) :=
    Q'.eqv_symm (RationalTail.const_mul_finSum
      (fun offset => anchorDecoratedEffectiveRatio ^ offset)
      (partitionProduct * anchorDecoratedEffectiveRatio ^ floor) depth)
  have hgeo :
      finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ offset) depth ≤ Q'.ofNat 2 :=
    geom_partial_le_two anchorDecoratedEffectiveRatio_nonnegative
      anchorDecoratedEffectiveRatio_le_half depth
  have hproduct0 : (0 : Q') ≤ partitionProduct :=
    Q'.mul_nonneg _ _
      (parametricKCompatibleSupportGasPartition_nonnegative cutoff n)
      (parametricKEmbeddedTargetPartition_nonnegative cutoff small n)
  have hscale0 : (0 : Q') ≤
      partitionProduct * anchorDecoratedEffectiveRatio ^ floor :=
    Q'.mul_nonneg _ _ hproduct0
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative floor)
  have hscaled :
      (partitionProduct * anchorDecoratedEffectiveRatio ^ floor) *
          finSum (fun offset =>
            anchorDecoratedEffectiveRatio ^ offset) depth ≤
        (partitionProduct * anchorDecoratedEffectiveRatio ^ floor) *
          Q'.ofNat 2 :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hgeo hscale0
  have hfinal :
      ((partitionProduct * anchorDecoratedEffectiveRatio ^ floor) *
          Q'.ofNat 2).eqv
        (partitionProduct *
          (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2)) :=
    Q'.mul_assoc_eqv partitionProduct
      (anchorDecoratedEffectiveRatio ^ floor) (Q'.ofNat 2)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv htargets)
    (Q'.le_trans' _ _ _ hterms
      (Q'.le_trans' _ _ _ (Q'.le_of_eqv hreorder)
        (Q'.le_trans' _ _ _ (Q'.le_of_eqv hpull)
          (Q'.le_trans' _ _ _ hscaled (Q'.le_of_eqv hfinal)))))

theorem spinSummedConnectedSourcePairSum_le_boundaryTail
    (cutoff : Nat) {small n inner distance start : Nat}
    {root : List Nat} (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (spinSummedSourcePairWeight cutoff)
        (connectedSourcePairs (root := root) hsmall) ≤
      (parametricKCompatibleSupportGasPartition cutoff n *
          parametricKEmbeddedTargetPartition cutoff small n) *
        (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (spinSummedConnectedSourcePairSum_le_shiftedTarget
      cutoff hsmall hstart hstartInner hbox)
    (spinSummedShiftedCarrierTargetSum_le_tail
      cutoff hsmall start (distance + 2)
        ((physicalFaceEdges n).length + 1))

theorem spinSummedConnectedReverseSourcePairSum_le_boundaryTail
    (cutoff : Nat) {small n inner distance start : Nat}
    {root : List Nat} (hsmall : small ≤ n)
    (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (spinSummedReverseSourcePairWeight cutoff)
        (connectedReverseSourcePairs (root := root) hsmall) ≤
      (parametricKCompatibleSupportGasPartition cutoff n *
          parametricKEmbeddedTargetPartition cutoff small n) *
        (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2) := by
  exact Q'.le_trans' _ _ _
    (spinSummedConnectedReverseSourcePairSum_le_shiftedTarget
      cutoff hsmall hstart hstartInner hbox)
    (spinSummedShiftedCarrierTargetSum_le_tail
      cutoff hsmall start (distance + 2)
        ((physicalFaceEdges n).length + 1))

end YMGap.Continuum.Z4SpinSummedConnectedCarrierTail

/-! ## Dependency gates -/

#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierTail.spinSummedConnectedSourcePairSum_le_shiftedTarget
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierTail.spinSummedConnectedReverseSourcePairSum_le_shiftedTarget
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierTail.spinSummedShiftedCarrierTargetSum_le_tail
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierTail.spinSummedConnectedSourcePairSum_le_boundaryTail
#print axioms YMGap.Continuum.Z4SpinSummedConnectedCarrierTail.spinSummedConnectedReverseSourcePairSum_le_boundaryTail
