/-
# Weighted capacity of one physical-target/root/size block

Inside a fixed coarse block, every realized representative has the same peel
rate and the same physical target atom.  The proved residual-code injection
bounds the number of representatives by the genuine SU(2) target-tuple
multiplicity.  Therefore the strict-rate weight of the whole block is at most
that rate times the exact physical target-block weight.

This is the weighted local contraction needed before summing sizes, roots,
and physical targets.  No geometric series or six-root union bound is taken
in this module.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockFubini

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullPeelData
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockInjection
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.BondMovingStep
open YMGap.Continuum.CompactDualSlabFaceStrandComponentAdaptiveEntropyCarrier
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.SU2CharacterVacuumHaar
open YMGap.Continuum.SU2FiniteSharedLinkFusionNetwork
open YMGap.Continuum.Z4FiniteBoxHeatKernelPacketState
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Small exact-sum and positivity lemmas -/

private theorem listQSum_le_length_mul_local {A : Type}
    (value : A -> Q') (bound : Q') : forall items : List A,
    (0 : Q') <= bound ->
    (forall item, item ∈ items -> value item <= bound) ->
      listQSum value items <= Q'.ofNat items.length * bound
  | [], _, _ =>
      Q'.le_of_eqv (Q'.eqv_symm (Q'.zero_mul_eqv bound))
  | head :: tail, hbound0, hvalue => by
      have htail := listQSum_le_length_mul_local value bound tail hbound0
        (fun item hitem => hvalue item (List.mem_cons_of_mem head hitem))
      have hadd := Q'.add_le_add
        (hvalue head List.mem_cons_self) htail
      exact Q'.le_trans' _ _ _ hadd
        (Q'.le_of_eqv (by
          refine Q'.eqv_symm ?_
          refine Q'.eqv_trans _
            ((Q'.ofNat tail.length + 1) * bound) _ ?_ ?_
          · exact Q'.mul_eqv_congr_right _ _ bound
              (Q'.ofNat_add_eqv tail.length 1)
          refine Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + (1 : Q') * bound) _
            (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 bound) ?_
          exact Q'.eqv_trans _
            (Q'.ofNat tail.length * bound + bound) _
            (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv bound))
            (Q'.add_comm_eqv
              (Q'.ofNat tail.length * bound) bound)))

private theorem listQSum_const_local {A : Type} (constant : Q') :
    forall items : List A,
      listQSum (fun _item => constant) items ≈
        Q'.ofNat items.length * constant
  | [] => Q'.eqv_symm (Q'.zero_mul_eqv constant)
  | _head :: tail => by
      refine Q'.eqv_trans _
        (constant + Q'.ofNat tail.length * constant) _
        (Q'.add_eqv_congr_left constant _ _
          (listQSum_const_local constant tail)) ?_
      refine Q'.eqv_symm ?_
      refine Q'.eqv_trans _
        ((Q'.ofNat tail.length + 1) * constant) _ ?_ ?_
      · exact Q'.mul_eqv_congr_right _ _ constant
          (Q'.ofNat_add_eqv tail.length 1)
      refine Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + (1 : Q') * constant) _
        (Q'.add_mul_eqv (Q'.ofNat tail.length) 1 constant) ?_
      exact Q'.eqv_trans _
        (Q'.ofNat tail.length * constant + constant) _
        (Q'.add_eqv_congr_left _ _ _ (Q'.one_mul_eqv constant))
        (Q'.add_comm_eqv
          (Q'.ofNat tail.length * constant) constant)

private theorem slabParametricCoefficient_anchor_nonnegative
    (K spin : Nat) :
    (0 : Q') <= coeffAt (heatKernelPacket K anchorCoupling) spin := by
  by_cases hspin : spin < K + 1
  · rw [coeffAt_heatKernelPacket hspin]
    exact coeffW_nonneg (by decide) spin
  · have hlarge : K < spin := by omega
    rw [coeffAt_of_gt (heatKernelPacket K anchorCoupling) hlarge]
    exact Q'.le_refl' 0

private theorem eliminateLinks_anchor_nonnegative_local
    (K : Nat) (physical : EdgeLabelling) : forall faceIds : List Nat,
    (0 : Q') <= eliminateLinks
      (fun faceId => coeffAt (heatKernelPacket K anchorCoupling)
        (physical faceId)) faceIds
  | [] => Q'.zero_le_one
  | head :: tail =>
      Q'.mul_nonneg _ _
        (slabParametricCoefficient_anchor_nonnegative K (physical head))
        (eliminateLinks_anchor_nonnegative_local K physical tail)

/-- Every fixed-order target atom is nonnegative at the SU(2) anchor. -/
theorem cubeInwardMateFixedOrderTargetBlockEntryWeight_nonnegative
    (K : Nat) (target : EdgeLabelling) :
    (0 : Q') <= cubeInwardMateFixedOrderTargetBlockEntryWeight
      anchorCoupling K target := by
  unfold cubeInwardMateFixedOrderTargetBlockEntryWeight
    slabParametricKPhysicalFaceFactor
  exact Q'.mul_nonneg _ _
    (eliminateLinks_anchor_nonnegative_local K target
      (slabPhysicalFaceEdges 1)) Q'.zero_le_one

/-! ## 2. A representative has the common block atom -/

/-- Inside one literal block, the strict-rate representative weight is the
common peel rate times the fixed physical target atom. -/
theorem cubeInwardMateFullPeelRepresentativeTargetWeight_eqv_blockAtom
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    {target : EdgeLabelling} {rootFaceId peelSize : Nat}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : EnumeratedCubeInwardMateFullSource
      K physical hK hbounded)
    (hrepresentative : representative ∈
      cubeInwardMateFullPeelTargetBlockRepresentatives
        K physical hK hbounded target rootFaceId peelSize) :
    cubeInwardMateFullPeelRepresentativeTargetWeight K representative ≈
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockEntryWeight
          anchorCoupling K target := by
  have hspec := cubeInwardMateFullPeelTargetBlockRepresentatives_spec
    representative hrepresentative
  have htargetEq :=
    cubeInwardMateFullPeelTargetBlockRepresentative_lowerPhysical_eq
      hphysical htarget representative hrepresentative
  have hatom :=
    EnumeratedCubeInwardMateFullSource.presentedTargetWeight_eqv_fixedOrderAtom
      representative
  unfold cubeInwardMateFullPeelRepresentativeTargetWeight
  dsimp only
  refine Q'.eqv_trans _
    (componentAdaptiveEntropyAnchorRatio ^
        representative.adaptiveInverseData.peelSize *
      cubeInwardMateFixedOrderTargetBlockEntryWeight anchorCoupling K
        representative.adaptiveInverseData.lowerPhysical) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left
      (componentAdaptiveEntropyAnchorRatio ^
        representative.adaptiveInverseData.peelSize) _ _ hatom
  · rw [hspec.2.1, htargetEq]
    exact Q'.eqv_refl _

/-! ## 3. Weighted physical capacity of one block -/

/-- Reassociate the cardinality majorant into the physical block total. -/
private theorem blockCardinalityWeight_eqv_physicalBlock
    (K : Nat) (target : EdgeLabelling) (peelSize : Nat) :
    Q'.ofNat (cubeInwardMateFixedOrderTargetTuples K target).length *
        (componentAdaptiveEntropyAnchorRatio ^ peelSize *
          cubeInwardMateFixedOrderTargetBlockEntryWeight
            anchorCoupling K target) ≈
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let rate := componentAdaptiveEntropyAnchorRatio ^ peelSize
  let atom := cubeInwardMateFixedOrderTargetBlockEntryWeight
    anchorCoupling K target
  let tuples := cubeInwardMateFixedOrderTargetTuples K target
  refine Q'.eqv_trans _ ((Q'.ofNat tuples.length * rate) * atom) _
    (Q'.eqv_symm (Q'.mul_assoc_eqv (Q'.ofNat tuples.length) rate atom)) ?_
  refine Q'.eqv_trans _ ((rate * Q'.ofNat tuples.length) * atom) _
    (Q'.mul_eqv_congr_right _ _ atom
      (Q'.mul_comm_eqv (Q'.ofNat tuples.length) rate)) ?_
  refine Q'.eqv_trans _ (rate * (Q'.ofNat tuples.length * atom)) _
    (Q'.mul_assoc_eqv rate (Q'.ofNat tuples.length) atom) ?_
  apply Q'.mul_eqv_congr_left rate
  unfold cubeInwardMateFixedOrderTargetBlockWeight tuples atom
  exact Q'.eqv_symm (listQSum_const_local
    (cubeInwardMateFixedOrderTargetBlockEntryWeight anchorCoupling K target)
    (cubeInwardMateFixedOrderTargetTuples K target))

/-- **Weighted fixed-block capacity.**  One physical-target/root/size block
costs at most its geometric rate times the exact genuine SU(2) physical
target block. -/
theorem cubeInwardMateFullPeelTargetBlockWeight_le_physicalBlock
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (target : EdgeLabelling) (rootFaceId peelSize : Nat)
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    cubeInwardMateFullPeelTargetBlockWeight
        (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
        (cubeInwardMateFullPeelRepresentativeTargetWeight
          K (physical := physical) (hK := hK) (hbounded := hbounded))
        (target, (rootFaceId, peelSize)) <=
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let block := cubeInwardMateFullPeelTargetBlockRepresentatives
    K physical hK hbounded target rootFaceId peelSize
  let rate := componentAdaptiveEntropyAnchorRatio ^ peelSize
  let atom := cubeInwardMateFixedOrderTargetBlockEntryWeight
    anchorCoupling K target
  let bound := rate * atom
  have hrate0 : (0 : Q') <= rate :=
    Q'.pow_nonneg componentAdaptiveEntropyAnchorRatio (by decide) peelSize
  have hatom0 : (0 : Q') <= atom :=
    cubeInwardMateFixedOrderTargetBlockEntryWeight_nonnegative K target
  have hbound0 : (0 : Q') <= bound :=
    Q'.mul_nonneg _ _ hrate0 hatom0
  have hsum :
      listQSum (cubeInwardMateFullPeelRepresentativeTargetWeight K) block <=
        Q'.ofNat block.length * bound := by
    apply listQSum_le_length_mul_local
    · exact hbound0
    · intro representative hrepresentative
      exact Q'.le_of_eqv
        (cubeInwardMateFullPeelRepresentativeTargetWeight_eqv_blockAtom
          hphysical htarget representative hrepresentative)
  have hlength :=
    cubeInwardMateFullPeelTargetBlock_length_le_targetTuples
      (K := K) (physical := physical) (hK := hK) (hbounded := hbounded)
      (target := target) (rootFaceId := rootFaceId) (peelSize := peelSize)
      hphysical htarget
  have hlengthQ : Q'.ofNat block.length <=
      Q'.ofNat (cubeInwardMateFixedOrderTargetTuples K target).length :=
    CReal.ofNat_le_ofNat hlength
  have hscaled := Q'.mul_le_mul_of_nonneg_right _ _ bound hlengthQ hbound0
  unfold cubeInwardMateFullPeelTargetBlockWeight
  change
    listQSum (cubeInwardMateFullPeelRepresentativeTargetWeight K) block <=
      componentAdaptiveEntropyAnchorRatio ^ peelSize *
        cubeInwardMateFixedOrderTargetBlockWeight anchorCoupling K target
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (blockCardinalityWeight_eqv_physicalBlock K target peelSize)))

#print axioms cubeInwardMateFixedOrderTargetBlockEntryWeight_nonnegative
#print axioms cubeInwardMateFullPeelRepresentativeTargetWeight_eqv_blockAtom
#print axioms cubeInwardMateFullPeelTargetBlockWeight_le_physicalBlock

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound
