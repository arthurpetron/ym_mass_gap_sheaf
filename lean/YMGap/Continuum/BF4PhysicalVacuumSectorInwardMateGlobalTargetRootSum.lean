/-
# Six-root and all-target global contraction

The global size-tail estimate contributes `64/425` for each of the six literal
cube roots.  Summing roots gives `384/425` for one bounded lowered physical
target; summing targets and using exact fixed-order normalization gives the
same factor against the complete extent-one BF4 physical partition.

This is the nested target/root/size estimate.  Reconciliation with the flat
global coarse-block Fubini and the original source mass remains downstream.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSizeTail

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetRootSum

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4CentralLowerCubePositiveRow
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSizeTail
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
    (left right : A -> Q') : ∀ items : List A,
    (∀ item, item ∈ items -> left item ≤ right item) ->
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hterm =>
      Q'.add_le_add
        (hterm head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem => hterm item (List.mem_cons_of_mem head hitem)))

private theorem listQSum_const_local {A : Type} (constant : Q') :
    ∀ items : List A,
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

/-! ## 1. Six roots over one bounded target -/

/-- Nested global strict-rate sum over all six literal roots for one lowered
physical target. -/
def globalCubeInwardMateFullPeelTargetRootsStrictRateWeight
    (K : Nat) (hK : 1 ≤ K) (target : EdgeLabelling) : Q' :=
  listQSum
    (globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight
      K hK target)
    centralLowerCubeFaceIds

/-- **Global six-root contraction for one target.**  The complete root-and-
size sum costs at most `384/425` of the exact physical target block. -/
theorem globalCubeInwardMateFullPeelTargetRootsStrictRateWeight_le
    {K : Nat} {hK : 1 ≤ K}
    (target : EdgeLabelling)
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    globalCubeInwardMateFullPeelTargetRootsStrictRateWeight K hK target ≤
      Q'.mkPos 384 425 (by decide) *
        cubeInwardMateFixedOrderTargetBlockWeight
          anchorCoupling K target := by
  let scalar := cubeInwardMateFixedOrderTargetBlockWeight
    anchorCoupling K target
  let rootBound := Q'.mkPos 64 425 (by decide) * scalar
  have hsum :
      listQSum
          (globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight
            K hK target)
          centralLowerCubeFaceIds ≤
        listQSum (fun _rootFaceId : Nat => rootBound)
          centralLowerCubeFaceIds := by
    apply listQSum_le_termwise_local
    intro rootFaceId _
    exact globalCubeInwardMateFullPeelTargetRootSizesStrictRateWeight_le
      target rootFaceId htarget
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
  unfold globalCubeInwardMateFullPeelTargetRootsStrictRateWeight
  exact Q'.le_trans' _ _ _ hsum (Q'.le_of_eqv hconstant)

/-! ## 2. All bounded physical targets -/

/-- Nested global strict-rate sum over every bounded lowered physical target,
its six roots, and every allowed peel size. -/
def globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
    (K : Nat) (hK : 1 ≤ K) : Q' :=
  listQSum
    (globalCubeInwardMateFullPeelTargetRootsStrictRateWeight K hK)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))

/-- **Nested complete global congestion bound.**  Summing all lowered physical
targets, roots, and peel sizes costs at most `384/425` of the complete
extent-one physical BF4 partition. -/
theorem globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight_le_partition
    {K : Nat} {hK : 1 ≤ K} :
    globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight K hK ≤
      Q'.mkPos 384 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 := by
  let targets := boundedEdgeLabellings K (slabPhysicalFaceEdges 1)
  have hsum :
      listQSum
          (globalCubeInwardMateFullPeelTargetRootsStrictRateWeight K hK)
          targets ≤
        listQSum
          (fun target => Q'.mkPos 384 425 (by decide) *
            cubeInwardMateFixedOrderTargetBlockWeight
              anchorCoupling K target) targets := by
    apply listQSum_le_termwise_local
    intro target htarget
    exact globalCubeInwardMateFullPeelTargetRootsStrictRateWeight_le
      target htarget
  have hscale := listQSum_mul_left
    (Q'.mkPos 384 425 (by decide))
    (cubeInwardMateFixedOrderTargetBlockWeight anchorCoupling K) targets
  have htotal := cubeInwardMateFixedOrderPhysicalTargets_weight_total
    anchorCoupling K
  unfold globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_of_eqv
      (Q'.eqv_trans _ _ _ hscale
        (Q'.mul_eqv_congr_left
          (Q'.mkPos 384 425 (by decide)) _ _ htotal)))

#print axioms globalCubeInwardMateFullPeelTargetRootsStrictRateWeight
#print axioms globalCubeInwardMateFullPeelTargetRootsStrictRateWeight_le
#print axioms globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight
#print axioms globalCubeInwardMateFullPeelAllTargetsRootsStrictRateWeight_le_partition

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetRootSum
