/-
# Six-root and all-target contraction

The exact `64/425` size-tail estimate holds for each of the six literal cube
roots.  Finite termwise summation therefore gives the strict rational factor
`6 * 64/425 = 384/425` for one bounded physical target.  Summing over the
bounded target carrier and applying the exact fixed-order physical
normalization gives the same factor against the complete extent-one BF4
physical partition.

This module contracts only the nested target/root/size order.  Identification
of that nested sum with the flat exact-Fubini carrier is kept downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetSizeTail

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetRootSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetSizeTail
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphEdgeOrderNorm
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem listQSum_le_termwise_local {A : Type}
    (left right : A -> Q') : forall items : List A,
    (forall item, item ∈ items -> left item <= right item) ->
      listQSum left items <= listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hterm item (List.mem_cons_of_mem head hitem)))

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

/-! ## 1. Six roots over one physical target -/

/-- Nested strict-rate sum over all six literal roots for one physical
target. -/
def cubeInwardMateFullPeelTargetRootsStrictRateWeight
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical)
    (target : EdgeLabelling) : Q' :=
  listQSum
    (cubeInwardMateFullPeelTargetRootSizesStrictRateWeight
      K physical hK hbounded target)
    centralLowerCubeFaceIds

/-- **Six-root contraction for one target.**  The complete root-and-size sum
costs at most `384/425` of the exact physical target block. -/
theorem cubeInwardMateFullPeelTargetRootsStrictRateWeight_le
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (target : EdgeLabelling)
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    cubeInwardMateFullPeelTargetRootsStrictRateWeight
        K physical hK hbounded target <=
      Q'.mkPos 384 425 (by decide) *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let scalar := cubeInwardMateFixedOrderTargetBlockWeight
    anchorCoupling K target
  let rootBound := Q'.mkPos 64 425 (by decide) * scalar
  have hsum :
      listQSum
          (cubeInwardMateFullPeelTargetRootSizesStrictRateWeight
            K physical hK hbounded target)
          centralLowerCubeFaceIds <=
        listQSum (fun _rootFaceId : Nat => rootBound)
          centralLowerCubeFaceIds := by
    apply listQSum_le_termwise_local
    intro rootFaceId _
    exact cubeInwardMateFullPeelTargetRootSizesStrictRateWeight_le
      hphysical target rootFaceId htarget
  have hconstant :
      listQSum (fun _rootFaceId : Nat => rootBound)
          centralLowerCubeFaceIds ≈
        Q'.mkPos 384 425 (by decide) * scalar := by
    refine Q'.eqv_trans _ (Q'.ofNat 6 * rootBound) _
      (Q'.eqv_trans _ _ _
        (listQSum_const_local rootBound centralLowerCubeFaceIds)
        (by
          unfold centralLowerCubeFaceIds
          exact Q'.eqv_refl _)) ?_
    unfold rootBound
    refine Q'.eqv_trans _
      ((Q'.ofNat 6 * Q'.mkPos 64 425 (by decide)) * scalar) _
      (Q'.eqv_symm
        (Q'.mul_assoc_eqv (Q'.ofNat 6)
          (Q'.mkPos 64 425 (by decide)) scalar)) ?_
    exact Q'.mul_eqv_congr_right _ _ scalar
      (by decide : Q'.ofNat 6 * Q'.mkPos 64 425 (by decide) ≈
        Q'.mkPos 384 425 (by decide))
  unfold cubeInwardMateFullPeelTargetRootsStrictRateWeight
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hconstant)

/-! ## 2. All bounded physical targets -/

/-- Nested strict-rate sum over every bounded physical target, its six roots,
and every allowed peel size. -/
def cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
    (K : Nat) (physical : EdgeLabelling)
    (hK : 1 ≤ K) (hbounded : SlabFaceLabellingBounded K 1 physical) : Q' :=
  listQSum
    (cubeInwardMateFullPeelTargetRootsStrictRateWeight
      K physical hK hbounded)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))

/-- **Nested complete congestion bound.**  Summing all physical targets,
literal roots, and peel sizes costs at most `384/425` of the complete
extent-one physical BF4 partition. -/
theorem cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight_le_partition
    {K : Nat} {physical : EdgeLabelling}
    {hK : 1 ≤ K} {hbounded : SlabFaceLabellingBounded K 1 physical}
    (hphysical : physical ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
        K physical hK hbounded <=
      Q'.mkPos 384 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 := by
  let targets := boundedEdgeLabellings K (slabPhysicalFaceEdges 1)
  have hsum :
      listQSum
          (cubeInwardMateFullPeelTargetRootsStrictRateWeight
            K physical hK hbounded) targets <=
        listQSum
          (fun target => Q'.mkPos 384 425 (by decide) *
            cubeInwardMateFixedOrderTargetBlockWeight
              anchorCoupling K target) targets := by
    apply listQSum_le_termwise_local
    intro target htarget
    exact cubeInwardMateFullPeelTargetRootsStrictRateWeight_le
      hphysical target htarget
  have hscale := listQSum_mul_left
    (Q'.mkPos 384 425 (by decide))
    (cubeInwardMateFixedOrderTargetBlockWeight anchorCoupling K) targets
  have htotal := cubeInwardMateFixedOrderPhysicalTargets_weight_total
    anchorCoupling K
  unfold cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hscale
        (Q'.mul_eqv_congr_left
          (Q'.mkPos 384 425 (by decide)) _ _ htotal)))

#print axioms cubeInwardMateFullPeelTargetRootsStrictRateWeight
#print axioms cubeInwardMateFullPeelTargetRootsStrictRateWeight_le
#print axioms cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
#print axioms cubeInwardMateFullPeelAllTargetsRootsStrictRateWeight_le_partition

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetRootSum
