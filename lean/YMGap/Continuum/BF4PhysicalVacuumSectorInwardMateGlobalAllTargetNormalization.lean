/-
# Normalize the distinct global all-target atoms

Within one bounded physical-target block, every distinct realized all-target
atom has the common heat weight of that physical target.  The proved carrier
injection bounds its cardinality by the genuine heterogeneous SU(2) tuple
multiplicity, so its weight is at most the exact BF4 physical block weight.

An exact deterministic Fubini over all bounded physical targets then gives

  sum(distinct realized target weights) <= physical partition.

Combining this normalization with the earlier source-side Fubini transport
and the `41/425` successful-event lower bound isolates a positive retained
target mass behind the explicit factor `64 * 32,000,000^6`.

The coupling is the fixed anchor `1/400`; no beta- or lattice-spacing-uniform
claim is made.  This is not yet a same-object posterior-variance, OS form,
spectral-gap, or continuum theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSuccessFraction
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetNormalization

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockPartition
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetBlockWeightBound
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateCubeSourceFullTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetCarrier
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetFubini
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetPhysical
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetWeight
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalSourceNormalization
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalTargetSuccessFraction
open YMGap.Continuum.CayleyPruferInjection
open YMGap.Continuum.CompactDualSlabExpandedTargetKey
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphActualOperator
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4BoundedEdgeLabellingNodup
open YMGap.Continuum.Z4HalfTimeReflectionFaceReindex
open YMGap.Continuum.Z4HalfTimeReflectionPartition
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Weighted contraction of one physical-target block -/

/-- Every representative in one physical target block has the common genuine
BF4 target-tuple entry weight. -/
theorem GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_blockEntry
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK)
    (hrepresentative : representative ∈
      globalInwardMateTargetPhysicalBlockRepresentatives K hK target) :
    GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight representative ≈
      cubeInwardMateFixedOrderTargetBlockEntryWeight
        anchorCoupling K target := by
  have hphysical :=
    globalInwardMateTargetPhysicalBlockRepresentative_targetPhysical_eq
      htarget representative hrepresentative
  refine Q'.eqv_trans _
    (slabParametricKPhysicalFaceFactor anchorCoupling K 1
      (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
        representative)) _
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_faceFactor
      representative) ?_
  rw [hphysical]
  unfold cubeInwardMateFixedOrderTargetBlockEntryWeight
  exact Q'.eqv_symm
    (Q'.mul_one_eqv
      (slabParametricKPhysicalFaceFactor anchorCoupling K 1 target))

private theorem listQSum_le_length_mul_local {A : Type}
    (value : A → Q') (bound : Q') : ∀ items : List A,
    (0 : Q') ≤ bound →
    (∀ item, item ∈ items → value item ≤ bound) →
      listQSum value items ≤ Q'.ofNat items.length * bound
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

private theorem targetTupleCardinalityWeight_eqv_targetBlock
    (K : Nat) (target : EdgeLabelling) :
    Q'.ofNat (cubeInwardMateFixedOrderTargetTuples K target).length *
        cubeInwardMateFixedOrderTargetBlockEntryWeight
          anchorCoupling K target ≈
      cubeInwardMateFixedOrderTargetBlockWeight
        anchorCoupling K target := by
  unfold cubeInwardMateFixedOrderTargetBlockWeight
  exact Q'.eqv_symm
    (listQSum_const_local
      (cubeInwardMateFixedOrderTargetBlockEntryWeight
        anchorCoupling K target)
      (cubeInwardMateFixedOrderTargetTuples K target))

/-- Target weight carried by one physical block of exact representatives. -/
def globalInwardMateTargetPhysicalBlockWeight
    (K : Nat) (hK : 1 ≤ K) (target : EdgeLabelling) : Q' :=
  listQSum
    GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
    (globalInwardMateTargetPhysicalBlockRepresentatives K hK target)

/-- **Weighted genuine-target block contraction.**  Distinct realized target
atoms over one physical field weigh no more than its exact SU2 target-tuple
block. -/
theorem globalInwardMateTargetPhysicalBlockWeight_le_targetBlock
    {K : Nat} {hK : 1 ≤ K} {target : EdgeLabelling}
    (htarget : target ∈
      boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) :
    globalInwardMateTargetPhysicalBlockWeight K hK target ≤
      cubeInwardMateFixedOrderTargetBlockWeight
        anchorCoupling K target := by
  let block :=
    globalInwardMateTargetPhysicalBlockRepresentatives K hK target
  let atom := cubeInwardMateFixedOrderTargetBlockEntryWeight
    anchorCoupling K target
  have hatom0 : (0 : Q') ≤ atom :=
    cubeInwardMateFixedOrderTargetBlockEntryWeight_nonnegative K target
  have hsum :
      listQSum
          GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight block ≤
        Q'.ofNat block.length * atom := by
    apply listQSum_le_length_mul_local
    · exact hatom0
    · intro representative hrepresentative
      exact Q'.le_of_eqv
        (GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_blockEntry
          htarget representative hrepresentative)
  have hlength :=
    globalInwardMateTargetPhysicalBlock_length_le_targetTuples
      (K := K) (hK := hK) (target := target) htarget
  have hlengthQ : Q'.ofNat block.length ≤
      Q'.ofNat (cubeInwardMateFixedOrderTargetTuples K target).length :=
    CReal.ofNat_le_ofNat hlength
  have hscaled :=
    Q'.mul_le_mul_of_nonneg_right _ _ atom hlengthQ hatom0
  change
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight block ≤
      cubeInwardMateFixedOrderTargetBlockWeight anchorCoupling K target
  exact Q'.le_trans' _ _ _ hsum
    (Q'.le_trans' _ _ _ hscaled
      (Q'.le_of_eqv
        (targetTupleCardinalityWeight_eqv_targetBlock K target)))

/-! ## 2. Exact physical-target Fubini -/

/-- The finite physical word of a distinct exact target representative. -/
def globalInwardMateTargetRepresentativePhysicalKey
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    List Nat :=
  finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)
    (GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
      representative)

private theorem range_nodup_local :
    ∀ count : Nat, (List.range count).Nodup
  | 0 => List.nodup_nil
  | count + 1 => by
      rw [List.range_succ]
      exact List.nodup_append.mpr
        ⟨range_nodup_local count,
          List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩,
          fun item hitem member hmember => by
            have hmemberEq : member = count := List.mem_singleton.mp hmember
            subst member
            exact Nat.ne_of_lt (List.mem_range.mp hitem)⟩

theorem boundedPhysicalTargetWords_nodup (K : Nat) :
    ((boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).map
      (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1))).Nodup := by
  apply nodup_map_of_injOn
  · apply boundedEdgeLabellings_nodup
    unfold slabPhysicalFaceEdges
    exact range_nodup_local _
  · intro left hleft right hright hword
    apply edgeLabelling_eq_of_word_eq_of_supported
      (slabPhysicalFaceEdges 1)
    · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
        left hleft).2
    · exact (boundedEdgeLabellings_sound K (slabPhysicalFaceEdges 1)
        right hright).2
    · exact hword

theorem globalInwardMateTargetRepresentativePhysicalKey_mem
    {K : Nat} {hK : 1 ≤ K}
    (representative : GlobalCubeInwardMateCertifiedTargetFullSource K hK) :
    globalInwardMateTargetRepresentativePhysicalKey representative ∈
      (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)).map
        (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1)) := by
  apply List.mem_map.mpr
  exact ⟨GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical
      representative,
    GlobalCubeInwardMateCertifiedTargetFullSource.targetPhysical_mem
      representative,
    rfl⟩

/-- The deterministic physical-word fiber is literally the displayed target
block. -/
theorem globalInwardMateTargetPhysicalBlock_fiberWeight_eq
    {K : Nat} {hK : 1 ≤ K} (target : EdgeLabelling) :
    fiberWeight
        (globalInwardMateTargetRepresentatives K hK)
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        globalInwardMateTargetRepresentativePhysicalKey
        (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1) target) =
      globalInwardMateTargetPhysicalBlockWeight K hK target := by
  unfold fiberWeight globalInwardMateTargetPhysicalBlockWeight
    globalInwardMateTargetPhysicalBlockRepresentatives
    globalInwardMateTargetRepresentativePhysicalKey
  apply congrArg
    (listQSum GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight)
  apply List.filter_congr
  intro representative _
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hword
    apply decide_eq_true
    exact (of_decide_eq_true hword).symm
  · intro hword
    apply decide_eq_true
    exact (of_decide_eq_true hword).symm

/-- Summing the literal physical target blocks exactly recovers the distinct
representative target weight. -/
theorem globalInwardMateTargetPhysicalBlocks_weight_total
    (K : Nat) (hK : 1 ≤ K) :
    listQSum (globalInwardMateTargetPhysicalBlockWeight K hK)
        (boundedEdgeLabellings K (slabPhysicalFaceEdges 1)) ≈
      listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        (globalInwardMateTargetRepresentatives K hK) := by
  apply finiteCoordinateFiberWeight_total
    (globalInwardMateTargetRepresentatives K hK)
    GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    globalInwardMateTargetRepresentativePhysicalKey
    (finiteEdgeLabellingWord (slabPhysicalFaceEdges 1))
    (globalInwardMateTargetPhysicalBlockWeight K hK)
  · exact boundedPhysicalTargetWords_nodup K
  · intro representative _
    exact globalInwardMateTargetRepresentativePhysicalKey_mem representative
  · intro target _
    exact Q'.eqv_of_eq
      (globalInwardMateTargetPhysicalBlock_fiberWeight_eq target).symm

private theorem listQSum_le_termwise_local
    {A : Type} (left right : A → Q') : ∀ items : List A,
    (∀ item, item ∈ items → left item ≤ right item) →
      listQSum left items ≤ listQSum right items
  | [], _ => Q'.le_refl' 0
  | head :: tail, hpoint =>
      Q'.add_le_add
        (hpoint head List.mem_cons_self)
        (listQSum_le_termwise_local left right tail
          (fun item hitem =>
            hpoint item (List.mem_cons_of_mem head hitem)))

/-- **Complete distinct-target normalization.**  One copy of every realized
all-target atom weighs at most the genuine BF4 physical partition. -/
theorem globalInwardMateTargetRepresentatives_weight_le_physicalPartition
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
        (globalInwardMateTargetRepresentatives K hK) ≤
      slabParametricKPhysicalPartition anchorCoupling K 1 := by
  have htotal := globalInwardMateTargetPhysicalBlocks_weight_total K hK
  have hblocks := listQSum_le_termwise_local
    (globalInwardMateTargetPhysicalBlockWeight K hK)
    (cubeInwardMateFixedOrderTargetBlockWeight anchorCoupling K)
    (boundedEdgeLabellings K (slabPhysicalFaceEdges 1))
    (fun target htarget =>
      globalInwardMateTargetPhysicalBlockWeight_le_targetBlock htarget)
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm htotal))
    (Q'.le_trans' _ _ _ hblocks
      (Q'.le_of_eqv
        (cubeInwardMateFixedOrderPhysicalTargets_weight_total
          anchorCoupling K)))

/-! ## 3. The normalized source-to-target transport inequality -/

/-- The complete successful-source mass is bounded by the explicit transport
cost times the genuine physical partition. -/
theorem globalInwardMateSuccessfulSourceWeight_le_physicalPartition
    (K : Nat) (hK : 1 ≤ K) :
    listQSum
        GlobalCubeInwardMateCertifiedTargetFullSource.weight
        (globalCubeInwardMateCertifiedTargetFullSources K hK) ≤
      Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          slabParametricKPhysicalPartition anchorCoupling K 1) := by
  have htarget :=
    globalInwardMateTargetRepresentatives_weight_le_physicalPartition K hK
  have hcost0 : (0 : Q') ≤ anchorInwardMateCost ^ 6 :=
    Q'.pow_nonneg anchorInwardMateCost (by
      unfold anchorInwardMateCost
      decide) 6
  have hcostScaled := Q'.mul_le_mul_of_nonneg_left _ _ _ htarget hcost0
  have hsixtyFour0 : (0 : Q') ≤ Q'.ofNat 64 := by decide
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ _
    hcostScaled hsixtyFour0
  exact Q'.le_trans' _ _ _
    (globalInwardMateSuccessfulSourceWeight_le_representativeTargets K hK)
    hscaled

/-- **Retained target-mass inequality.**  The explicit `41/425` successful
event must feed the sum of distinct target atoms after paying at most the
proved six-bit and six-face transport cost. -/
theorem globalInwardMateSuccessRate_partition_le_transportCost_mul_targets
    (K : Nat) (hK : 1 ≤ K) :
    Q'.mkPos 41 425 (by decide) *
        slabParametricKPhysicalPartition anchorCoupling K 1 ≤
      Q'.ofNat 64 *
        (anchorInwardMateCost ^ 6 *
          listQSum
            GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight
            (globalInwardMateTargetRepresentatives K hK)) := by
  exact Q'.le_trans' _ _ _
    (globalCubeInwardMateCertifiedTargetFullSources_weight_ge_partition K hK)
    (globalInwardMateSuccessfulSourceWeight_le_representativeTargets K hK)

#print axioms GlobalCubeInwardMateCertifiedTargetFullSource.targetWeight_eqv_blockEntry
#print axioms globalInwardMateTargetPhysicalBlockWeight_le_targetBlock
#print axioms globalInwardMateTargetRepresentativePhysicalKey
#print axioms boundedPhysicalTargetWords_nodup
#print axioms globalInwardMateTargetRepresentativePhysicalKey_mem
#print axioms globalInwardMateTargetPhysicalBlock_fiberWeight_eq
#print axioms globalInwardMateTargetPhysicalBlocks_weight_total
#print axioms globalInwardMateTargetRepresentatives_weight_le_physicalPartition
#print axioms globalInwardMateSuccessfulSourceWeight_le_physicalPartition
#print axioms globalInwardMateSuccessRate_partition_le_transportCost_mul_targets

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllTargetNormalization
