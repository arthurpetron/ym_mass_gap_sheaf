/-
# Uniform connected-cylinder tail below the anchor

The connected carrier geometry is independent of the coupling.  The path
part of every two-replica source pair is bounded by the anchor decorated-face
envelope, while the two background parts retain their exact coupling-`w`
weights.  Finite Cartesian summation therefore produces the exact product of
the coupling-`w` target partition and embedded target partition, multiplied
by the same geometric `1/4` tail used at the anchor.
-/

import YMGap.Continuum.Z4CouplingParametricCylinderWeights
import YMGap.Continuum.Z4SpinSummedConnectedCarrierTail
import YMGap.Continuum.Z4SpinSummedCylinderConnectedTail

namespace YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail

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
open YMGap.Continuum.Z4CanonicalBipartitePath
open YMGap.Continuum.Z4CanonicalColoredSupportCount
open YMGap.Continuum.Z4CanonicalConnectedCarrierAnimal
open YMGap.Continuum.Z4CanonicalConnectedCarrierFixedSize
open YMGap.Continuum.Z4CanonicalConnectedCarrierTail
open YMGap.Continuum.Z4CanonicalConnectedPathCarrier
open YMGap.Continuum.Z4CanonicalCylinderConnectedClassification
open YMGap.Continuum.Z4CanonicalCylinderConnectedTail
open YMGap.Continuum.Z4CanonicalCylinderSwitchSummation
open YMGap.Continuum.Z4CanonicalPinnedPolymerBound
open YMGap.Continuum.Z4CanonicalPolymerAnchorBounds
open YMGap.Continuum.Z4CanonicalPolymerAnimalBridge
open YMGap.Continuum.Z4CanonicalPolymerRange
open YMGap.Continuum.Z4CanonicalPolymerSpecification
open YMGap.Continuum.Z4CanonicalPolymerTransport
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrier
open YMGap.Continuum.Z4CanonicalRightRootConnectedCarrierTail
open YMGap.Continuum.Z4CouplingParametricCrossVolumeCylinder
open YMGap.Continuum.Z4CouplingParametricCylinderWeights
open YMGap.Continuum.Z4CouplingParametricSpinSummedSupportFactorization
open YMGap.Continuum.Z4CutoffOneSupportBijection
open YMGap.Continuum.Z4ExplicitVacuumActivityDecomposition
open YMGap.Continuum.Z4FiniteBoxExhaustion
open YMGap.Continuum.Z4SpinSummedColoredSupportWeight
open YMGap.Continuum.Z4SpinSummedConnectedCarrierFixedSize
open YMGap.Continuum.Z4SpinSummedConnectedCarrierTail
open YMGap.Continuum.Z4SpinSummedFaceActivityBound
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Fixed-size carrier factorization -/

def couplingSpinSummedConnectedCarrierTargetWeight
    (coupling : Q') (cutoff n size : Nat)
    (carrier : ConnectedCarrier) : Q' :=
  anchorDecoratedFaceEnvelope ^ size *
    (couplingParametricKSupportFamilyActivity
        coupling cutoff n carrier.2.1 *
      couplingParametricKSupportFamilyActivity
        coupling cutoff n carrier.2.2)

theorem couplingSpinSummedConnectedCarrierTargetSum_eqv
    (coupling : Q') (cutoff : Nat) {small n : Nat}
    (hsmall : small ≤ n) (rootFace size : Nat) :
    listQSum
        (couplingSpinSummedConnectedCarrierTargetWeight
          coupling cutoff n size)
        (connectedCarrierTargetList small n rootFace size) ≈
      spinSummedColoredPinnedSizeWeightSum n rootFace size *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n *
          couplingParametricKEmbeddedTargetPartition
            coupling cutoff small n) := by
  have houter := listQSum_cartesian_product
    (fun _ : ColoredSupportPair =>
      anchorDecoratedFaceEnvelope ^ size)
    (fun background : List (List Nat) × List (List Nat) =>
      couplingParametricKSupportFamilyActivity
          coupling cutoff n background.1 *
        couplingParametricKSupportFamilyActivity
          coupling cutoff n background.2)
    (canonicalColoredPinnedSizePairs n rootFace size)
    (cartesian (canonicalCompatibleAmbientFamilies n)
      (embeddedCompatibleFamilies small n))
  have hinner := listQSum_cartesian_product
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (canonicalCompatibleAmbientFamilies n)
    (embeddedCompatibleFamilies small n)
  have hembedded := listQSum_perm
    (couplingParametricKSupportFamilyActivity coupling cutoff n)
    (embeddedCompatibleFamilies_perm_target hsmall)
  unfold connectedCarrierTargetList
    couplingSpinSummedConnectedCarrierTargetWeight
    spinSummedColoredPinnedSizeWeightSum
  refine Q'.eqv_trans _ _ _ houter ?_
  refine Q'.mul_eqv_congr_left _ _ _ ?_
  refine Q'.eqv_trans _ _ _ hinner ?_
  unfold couplingParametricKCompatibleSupportGasPartition
    couplingParametricKEmbeddedTargetPartition
  exact Q'.mul_eqv_congr_left _ _ _ hembedded

theorem couplingSpinSummedConnectedCarrierTargetSum_le_geom_partition
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (rootFace size : Nat) :
    listQSum
        (couplingSpinSummedConnectedCarrierTargetWeight
          coupling cutoff n size)
        (connectedCarrierTargetList small n rootFace size) ≤
      anchorDecoratedEffectiveRatio ^ size *
        (couplingParametricKCompatibleSupportGasPartition
            coupling cutoff n *
          couplingParametricKEmbeddedTargetPartition
            coupling cutoff small n) := by
  have hfactor := couplingSpinSummedConnectedCarrierTargetSum_eqv
    coupling cutoff hsmall rootFace size
  have hpartition0 : (0 : Q') ≤
      couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n *
        couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff n)
      (couplingParametricKEmbeddedTargetPartition_nonnegative
        hcoupling cutoff small n)
  exact Q'.le_trans' _ _ _ (Q'.le_of_eqv hfactor)
    (Q'.mul_le_mul_of_nonneg_right _ _ _
      (spinSummedColoredPinnedSizeWeightSum_le_geom
        n rootFace size) hpartition0)

/-! ## 2. Shifted shells and the geometric tail -/

def couplingSpinSummedShiftedCarrierTargetWeight
    (coupling : Q') (cutoff n floor : Nat)
    (tagged : Nat × ConnectedCarrier) : Q' :=
  couplingSpinSummedConnectedCarrierTargetWeight
    coupling cutoff n (floor + tagged.1) tagged.2

theorem couplingSpinSummedShiftedCarrierTargetSum_eqv_finSum
    (coupling : Q') (cutoff small n rootFace floor : Nat) :
    ∀ depth : Nat,
    listQSum
        (couplingSpinSummedShiftedCarrierTargetWeight
          coupling cutoff n floor)
        (shiftedCarrierTargetList small n rootFace floor depth) ≈
      finSum (fun offset =>
        listQSum
          (couplingSpinSummedConnectedCarrierTargetWeight
            coupling cutoff n (floor + offset))
          (connectedCarrierTargetList small n rootFace
            (floor + offset))) depth
  | 0 => Q'.eqv_refl 0
  | depth + 1 => by
      rw [finSum_succ]
      unfold shiftedCarrierTargetList
      refine Q'.eqv_trans _ _ _
        (listQSum_append
          (couplingSpinSummedShiftedCarrierTargetWeight
            coupling cutoff n floor)
          (shiftedCarrierTargetList small n rootFace floor depth)
          ((connectedCarrierTargetList small n rootFace
              (floor + depth)).map (fun carrier => (depth, carrier)))) ?_
      refine Q'.add_eqv_congr'
        (couplingSpinSummedShiftedCarrierTargetSum_eqv_finSum
          coupling cutoff small n rootFace floor depth) ?_
      rw [listQSum_map]
      exact Q'.eqv_refl _

theorem couplingSpinSummedShiftedCarrierTargetSum_le_tail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff : Nat) {small n : Nat} (hsmall : small ≤ n)
    (rootFace floor depth : Nat) :
    listQSum
        (couplingSpinSummedShiftedCarrierTargetWeight
          coupling cutoff n floor)
        (shiftedCarrierTargetList small n rootFace floor depth) ≤
      (couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n *
        couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n) *
        (anchorDecoratedEffectiveRatio ^ floor * Q'.ofNat 2) := by
  let partitionProduct :=
    couplingParametricKCompatibleSupportGasPartition
        coupling cutoff n *
      couplingParametricKEmbeddedTargetPartition
        coupling cutoff small n
  have htargets := couplingSpinSummedShiftedCarrierTargetSum_eqv_finSum
    coupling cutoff small n rootFace floor depth
  have hterms :
      finSum (fun offset =>
          listQSum
            (couplingSpinSummedConnectedCarrierTargetWeight
              coupling cutoff n (floor + offset))
            (connectedCarrierTargetList small n rootFace
              (floor + offset))) depth ≤
        finSum (fun offset =>
          anchorDecoratedEffectiveRatio ^ (floor + offset) *
            partitionProduct) depth :=
    YMGap.Constructive.CharacterTail.finSum_le_termwise _ _
      (fun offset =>
        couplingSpinSummedConnectedCarrierTargetSum_le_geom_partition
          hcoupling cutoff hsmall rootFace (floor + offset)) depth
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
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff n)
      (couplingParametricKEmbeddedTargetPartition_nonnegative
        hcoupling cutoff small n)
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

/-! ## 3. Forward and reverse source-pair injection -/

theorem couplingSpinSummedConnectedSourcePairSum_le_shiftedTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n) (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (couplingSpinSummedSourcePairWeight coupling cutoff)
        (connectedSourcePairs (root := root) hsmall) ≤
      listQSum
        (couplingSpinSummedShiftedCarrierTargetWeight
          coupling cutoff n (distance + 2))
        (shiftedCarrierTargetList small n start (distance + 2)
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedSourcePairs (root := root) hsmall).attach
    (shiftedCarrierTargetList small n start (distance + 2)
      ((physicalFaceEdges n).length + 1))
    (fun entry : ConnectedSourceEntry root hsmall =>
      couplingSpinSummedSourcePairWeight coupling cutoff entry.val)
    (couplingSpinSummedShiftedCarrierTargetWeight
      coupling cutoff n (distance + 2))
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
        couplingSpinSummedConnectedSourcePairWeight_le_support_background
          hcoupling hle cutoff hsmall entry
      unfold connectedCarrierShiftEncode
        couplingSpinSummedShiftedCarrierTargetWeight
        couplingSpinSummedConnectedCarrierTargetWeight connectedCarrier
      rw [hsize]
      simpa [couplingSpinSummedConnectedBackgroundPairWeight]
        using hbound)
    (fun tagged _ => by
      unfold couplingSpinSummedShiftedCarrierTargetWeight
        couplingSpinSummedConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff n tagged.2.2.1)
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff n tagged.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

theorem couplingSpinSummedConnectedReverseSourcePairSum_le_shiftedTarget
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n) (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (couplingSpinSummedReverseSourcePairWeight coupling cutoff)
        (connectedReverseSourcePairs (root := root) hsmall) ≤
      listQSum
        (couplingSpinSummedShiftedCarrierTargetWeight
          coupling cutoff n (distance + 2))
        (shiftedCarrierTargetList small n start (distance + 2)
          ((physicalFaceEdges n).length + 1)) := by
  have hinjection := listQSum_le_of_injective
    (connectedReverseSourcePairs (root := root) hsmall).attach
    (shiftedCarrierTargetList small n start (distance + 2)
      ((physicalFaceEdges n).length + 1))
    (fun entry : ReverseConnectedSourceEntry root hsmall =>
      couplingSpinSummedReverseSourcePairWeight
        coupling cutoff entry.val)
    (couplingSpinSummedShiftedCarrierTargetWeight
      coupling cutoff n (distance + 2))
    (reverseConnectedCarrierShiftEncode hsmall (distance + 2))
    (attach_nodup_of_nodup _
      (connectedReverseSourcePairs_nodup hsmall root))
    (fun entry _ => by
      have hfloor := reverseConnectedCarrierSupport_boundary_floor
        hsmall entry hstart hstartInner hbox
      have hmax :=
        reverseConnectedCarrierSupport_length_le_ambient hsmall entry
      let offset :=
        (reverseConnectedCarrierSupport hsmall entry).length -
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
        couplingSpinSummedReverseConnectedSourcePairWeight_le_support_background
          hcoupling hle cutoff hsmall entry
      unfold reverseConnectedCarrierShiftEncode
        couplingSpinSummedShiftedCarrierTargetWeight
        couplingSpinSummedConnectedCarrierTargetWeight
        reverseConnectedCarrier
      rw [hsize]
      simpa [couplingSpinSummedReverseConnectedBackgroundPairWeight]
        using hbound)
    (fun tagged _ => by
      unfold couplingSpinSummedShiftedCarrierTargetWeight
        couplingSpinSummedConnectedCarrierTargetWeight
      exact Q'.mul_nonneg _ _
        (Q'.pow_nonneg anchorDecoratedFaceEnvelope
          anchorDecoratedFaceEnvelope_nonnegative _)
        (Q'.mul_nonneg _ _
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff n tagged.2.2.1)
          (couplingParametricKSupportFamilyActivity_nonnegative
            hcoupling cutoff n tagged.2.2.2)))
  rw [listQSum_attach] at hinjection
  exact hinjection

theorem couplingSpinSummedConnectedSourcePairSum_le_boundaryTail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n) (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum (couplingSpinSummedSourcePairWeight coupling cutoff)
        (connectedSourcePairs (root := root) hsmall) ≤
      (couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n *
        couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n) *
        (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2) :=
  Q'.le_trans' _ _ _
    (couplingSpinSummedConnectedSourcePairSum_le_shiftedTarget
      hcoupling hle cutoff hsmall hstart hstartInner hbox)
    (couplingSpinSummedShiftedCarrierTargetSum_le_tail
      hcoupling cutoff hsmall start (distance + 2)
        ((physicalFaceEdges n).length + 1))

theorem couplingSpinSummedConnectedReverseSourcePairSum_le_boundaryTail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance start : Nat} {root : List Nat}
    (hsmall : small ≤ n) (hstart : start ∈ root)
    (hstartInner : boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum
        (couplingSpinSummedReverseSourcePairWeight coupling cutoff)
        (connectedReverseSourcePairs (root := root) hsmall) ≤
      (couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n *
        couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n) *
        (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2) :=
  Q'.le_trans' _ _ _
    (couplingSpinSummedConnectedReverseSourcePairSum_le_shiftedTarget
      hcoupling hle cutoff hsmall hstart hstartInner hbox)
    (couplingSpinSummedShiftedCarrierTargetSum_le_tail
      hcoupling cutoff hsmall start (distance + 2)
        ((physicalFaceEdges n).length + 1))

/-! ## 4. Finite-cylinder connected residue -/

private theorem listQSum_pointwise_eqv {A : Type}
    (f g : A → Q') (hfg : ∀ x, f x ≈ g x) :
    ∀ xs : List A, listQSum f xs ≈ listQSum g xs
  | [] => Q'.eqv_refl 0
  | head :: tail =>
      Q'.add_eqv_congr' (hfg head)
        (listQSum_pointwise_eqv f g hfg tail)

theorem couplingSpinSummedRootedCylinderConnectedRawPairSum_eqv
    (coupling : Q') (cutoff : Nat) {small n : Nat}
    (hsmall : small ≤ n) (root : CanonicalAtom n) :
    listQSum
        (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
        (rootedCylinderConnectedRawPairs hsmall root) ≈
      listQSum (couplingSpinSummedSourcePairWeight coupling cutoff)
          (connectedSourcePairs (root := root.val) hsmall) +
        listQSum
          (couplingSpinSummedReverseSourcePairWeight coupling cutoff)
          (connectedReverseSourcePairs (root := root.val) hsmall) := by
  unfold rootedCylinderConnectedRawPairs
  refine Q'.eqv_trans _ _ _
    (listQSum_append
      (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
      (forwardConnectedRawPairs hsmall root)
      (reverseConnectedRawPairs hsmall root)) ?_
  refine Q'.add_eqv_congr' ?_ ?_
  · unfold forwardConnectedRawPairs
    rw [listQSum_map]
    exact Q'.eqv_refl _
  · unfold reverseConnectedRawPairs
    rw [listQSum_map]
    apply listQSum_pointwise_eqv
    intro pair
    unfold couplingSpinSummedCylinderRawPairWeight
      couplingSpinSummedReverseSourcePairWeight
    exact Q'.mul_comm_eqv _ _

def couplingSpinSummedCylinderSingleRootBoundaryTail
    (coupling : Q') (cutoff small n distance : Nat) : Q' :=
  (couplingParametricKCompatibleSupportGasPartition
      coupling cutoff n *
    couplingParametricKEmbeddedTargetPartition
      coupling cutoff small n) *
    (anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2)

def couplingSpinSummedCylinderSingleRootTwoSidedTail
    (coupling : Q') (cutoff small n distance : Nat) : Q' :=
  couplingSpinSummedCylinderSingleRootBoundaryTail
      coupling cutoff small n distance +
    couplingSpinSummedCylinderSingleRootBoundaryTail
      coupling cutoff small n distance

theorem couplingSpinSummedCylinderSingleRootTwoSidedTail_nonnegative
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (cutoff small n distance : Nat) :
    (0 : Q') ≤ couplingSpinSummedCylinderSingleRootTwoSidedTail
      coupling cutoff small n distance := by
  unfold couplingSpinSummedCylinderSingleRootTwoSidedTail
    couplingSpinSummedCylinderSingleRootBoundaryTail
  have hpartition : (0 : Q') ≤
      couplingParametricKCompatibleSupportGasPartition
          coupling cutoff n *
        couplingParametricKEmbeddedTargetPartition
          coupling cutoff small n :=
    Q'.mul_nonneg _ _
      (couplingParametricKCompatibleSupportGasPartition_nonnegative
        hcoupling cutoff n)
      (couplingParametricKEmbeddedTargetPartition_nonnegative
        hcoupling cutoff small n)
  have htail : (0 : Q') ≤
      anchorDecoratedEffectiveRatio ^ (distance + 2) * Q'.ofNat 2 :=
    Q'.mul_nonneg _ _
      (Q'.pow_nonneg anchorDecoratedEffectiveRatio
        anchorDecoratedEffectiveRatio_nonnegative _) (by decide)
  exact Q'.zero_le_add _ _
    (Q'.mul_nonneg _ _ hpartition htail)
    (Q'.mul_nonneg _ _ hpartition htail)

theorem couplingSpinSummedConnectedCylinderPairSum_le_boundaryTail
    {coupling : Q'} (hcoupling : (0 : Q') ≤ coupling)
    (hle : coupling ≤ anchorCoupling) (cutoff : Nat)
    {small n inner distance : Nat} (hsmall : small ≤ n)
    (roots : List (CanonicalAtom n)) (predicate : List Bool → Bool)
    (hrootsInside : ∀ root, root ∈ roots →
      polymerInsideBoxB small n root.val = true)
    (hgeometry : ∀ root, root ∈ roots →
      ∃ start, start ∈ root.val ∧
        boxPlaquetteAt n start ∈ boxPlaquettes inner)
    (hbox : inner + distance = small) :
    listQSum
        (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
        (connectedCylinderSourcePairs
          (roots := roots) (predicate := predicate) hsmall) ≤
      Q'.ofNat roots.length *
        couplingSpinSummedCylinderSingleRootTwoSidedTail
          coupling cutoff small n distance := by
  have hinject :
      listQSum
          (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
          (connectedCylinderSourcePairs
            (roots := roots) (predicate := predicate) hsmall) ≤
        listQSum
          (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
          (allCylinderConnectedRawPairs hsmall roots) := by
    apply listQSum_le_of_injective
      (connectedCylinderSourcePairs
        (roots := roots) (predicate := predicate) hsmall)
      (allCylinderConnectedRawPairs hsmall roots)
      (couplingSpinSummedCylinderSourcePairWeight coupling cutoff)
      (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
      cylinderConnectedRawEncode
      (connectedCylinderSourcePairs_nodup hsmall roots predicate)
    · exact cylinderConnectedRawEncode_mem_all hsmall hrootsInside
    · intro first _ second _ heq
      exact cylinderConnectedRawEncode_injective first second heq
    · intro pair _
      exact Q'.le_refl' _
    · intro pair _
      exact Q'.mul_nonneg _ _
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff n pair.1)
        (couplingParametricKSupportFamilyActivity_nonnegative
          hcoupling cutoff n pair.2)
  have hflat := listQSum_flatMap
    (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
    (rootedCylinderConnectedRawPairs hsmall) roots
  apply Q'.le_trans' _ _ _ hinject
  apply Q'.le_trans' _ _ _ (Q'.le_of_eqv hflat)
  apply listQSum_le_length_mul
    (fun root => listQSum
      (couplingSpinSummedCylinderRawPairWeight coupling cutoff n)
      (rootedCylinderConnectedRawPairs hsmall root))
    (couplingSpinSummedCylinderSingleRootTwoSidedTail_nonnegative
      hcoupling cutoff small n distance)
    roots
  intro root hroot
  obtain ⟨start, hstart, hstartInner⟩ := hgeometry root hroot
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (couplingSpinSummedRootedCylinderConnectedRawPairSum_eqv
        coupling cutoff hsmall root))
    (Q'.add_le_add
      (couplingSpinSummedConnectedSourcePairSum_le_boundaryTail
        hcoupling hle cutoff hsmall hstart hstartInner hbox)
      (couplingSpinSummedConnectedReverseSourcePairSum_le_boundaryTail
        hcoupling hle cutoff hsmall hstart hstartInner hbox))

#print axioms couplingSpinSummedConnectedCarrierTargetSum_eqv
#print axioms couplingSpinSummedShiftedCarrierTargetSum_le_tail
#print axioms couplingSpinSummedConnectedSourcePairSum_le_boundaryTail
#print axioms couplingSpinSummedConnectedReverseSourcePairSum_le_boundaryTail
#print axioms couplingSpinSummedConnectedCylinderPairSum_le_boundaryTail

end YMGap.Continuum.Z4CouplingParametricConnectedCarrierTail
