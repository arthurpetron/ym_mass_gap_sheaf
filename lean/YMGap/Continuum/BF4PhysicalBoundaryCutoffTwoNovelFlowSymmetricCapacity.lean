/-
# Symmetric novel-flow capacity compiler

The symmetric novel load preserves the routed Dirichlet form exactly and
turns the new-to-old capacity inequality into the reverse of the old-to-new
inequality.  This module carries that reduction through the entire finite
coercivity and completed vacuum-sector contraction pipeline.

A three-field local certificate pays the old--old, old-to-new, and new--new
blocks.  Load and physical-capacity symmetry synthesize the omitted
new-to-old field.  The four block estimates then control the exact symmetric
loaded form, hence the original novel pairwise variance.  Combining this with
the already proved old-block coercivity constructs the existing full-sector
coercivity datum.  A cofinal family compiles to completed strict contraction.

The local capacity fields are not inhabited here.  In particular no uniform
new--new estimate, thermodynamic/continuum construction, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity

set_option maxRecDepth 1000000
set_option maxHeartbeats 1000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCanonicalCrossEdgeLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowCapacityRatio
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricLoad
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. Every retained endpoint lies in exactly one capacity block -/

private theorem cutoffTwoFullState_mem_old_or_new
    {later state : Nat}
    (hlater : 2 ≤ later)
    (hstate : state ∈ cutoffTwoEdgeLoadFullStates later) :
    state ∈ cutoffTwoEdgeLoadOldStates later ∨
      state ∈ cutoffTwoEdgeLoadNewStates later := by
  by_cases himage : state ∈
      centralPhysicalFiniteEmbeddedVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) 2 later 0
  · left
    exact
      (mem_centralPhysicalFiniteVacuumSectorOldBlockIndices_iff
        (w := cutoffTwoHalfCoupling) (hw := by decide)
        (half := 0) hlater).2 himage
  · right
    exact
      (mem_centralPhysicalFiniteVacuumSectorNewBlockIndices_iff
        (w := cutoffTwoHalfCoupling) (hw := by decide)
        (base := 2) (later := later) (half := 0) (index := state)).2
        ⟨hstate, himage⟩

namespace CutoffTwoNovelSymmetricOrientedCapacityAt

/-- The three oriented block fields imply the pointwise symmetric capacity
inequality on the whole retained carrier. -/
theorem full_capacity
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (hlater : 2 ≤ later)
    (source : Nat)
    (hsource : source ∈ cutoffTwoEdgeLoadFullStates later)
    (target : Nat)
    (htarget : target ∈ cutoffTwoEdgeLoadFullStates later) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricEdgeLoad later source target ≤
      cutoffTwoNovelAllocatedKernel later source target := by
  rcases cutoffTwoFullState_mem_old_or_new hlater hsource with
    hsourceOld | hsourceNew
  · rcases cutoffTwoFullState_mem_old_or_new hlater htarget with
      htargetOld | htargetNew
    · exact capacity.old_old source hsourceOld target htargetOld
    · exact capacity.old_new source hsourceOld target htargetNew
  · rcases cutoffTwoFullState_mem_old_or_new hlater htarget with
      htargetOld | htargetNew
    · exact capacity.new_old source hsourceNew target htargetOld
    · exact capacity.new_new source hsourceNew target htargetNew

end CutoffTwoNovelSymmetricOrientedCapacityAt

/-! ## 2. Exact four-block decomposition of the symmetric loaded form -/

def cutoffTwoNovelSymmetricLoadedOldOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadOldStates later)
    coefficient (cutoffTwoNovelSymmetricEdgeLoad later)

def cutoffTwoNovelSymmetricLoadedOldNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadNewStates later)
    coefficient (cutoffTwoNovelSymmetricEdgeLoad later)

def cutoffTwoNovelSymmetricLoadedNewOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadOldStates later)
    coefficient (cutoffTwoNovelSymmetricEdgeLoad later)

def cutoffTwoNovelSymmetricLoadedNewNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadNewStates later)
    coefficient (cutoffTwoNovelSymmetricEdgeLoad later)

theorem cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_four_blocks
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelSymmetricRawLoadedDirichlet later coefficient ≈
      (cutoffTwoNovelSymmetricLoadedOldOldDirichlet later coefficient +
        cutoffTwoNovelSymmetricLoadedOldNewDirichlet later coefficient) +
      (cutoffTwoNovelSymmetricLoadedNewOldDirichlet later coefficient +
        cutoffTwoNovelSymmetricLoadedNewNewDirichlet later coefficient) := by
  unfold cutoffTwoNovelSymmetricRawLoadedDirichlet
    cutoffTwoNovelSymmetricLoadedOldOldDirichlet
    cutoffTwoNovelSymmetricLoadedOldNewDirichlet
    cutoffTwoNovelSymmetricLoadedNewOldDirichlet
    cutoffTwoNovelSymmetricLoadedNewNewDirichlet
    cutoffTwoEdgeLoadFullStates cutoffTwoEdgeLoadOldStates
    cutoffTwoEdgeLoadNewStates
  change finiteJointDirichletEnergy
      (centralPhysicalFiniteVacuumSectorIndices
        cutoffTwoHalfCoupling (by decide) later 0)
      coefficient _ ≈ _
  exact finiteJointDirichletEnergy_filter_four_blocks
    (centralPhysicalFiniteVacuumSectorIndices
      cutoffTwoHalfCoupling (by decide) later 0)
    (centralPhysicalFiniteEmbeddedVacuumSectorB
      cutoffTwoHalfCoupling (by decide) 2 later 0)
    coefficient _

private theorem finiteJointDirichletBlock_scale_joint_local
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftStates rightStates coefficient
        (fun left right => scale * joint left right) ≈
      scale * finiteJointDirichletBlock
        leftStates rightStates coefficient joint := by
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left =>
        scale * listQSum
          (fun right =>
            joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right)))
          rightStates)
      leftStates) _ ?_ ?_
  · apply listQSum_congr
    intro left
    refine Q'.eqv_trans _
      (listQSum
        (fun right =>
          scale *
            (joint left right *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right))))
        rightStates) _ ?_ ?_
    · apply listQSum_congr
      intro right
      exact Q'.mul_assoc_eqv _ _ _
    · exact listQSum_mul_left scale _ rightStates
  · exact listQSum_mul_left scale _ leftStates

/-! ## 3. The three oriented fields pay all four physical blocks -/

namespace CutoffTwoNovelSymmetricOrientedCapacityAt

theorem loaded_oldOld_le_half_physical
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricLoadedOldOldDirichlet later coefficient ≤
      HalfPow.half * cutoffTwoOldOldDirichlet later coefficient := by
  have h := scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadOldStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelSymmetricEdgeLoad later)
    (fun source target =>
      HalfPow.half * cutoffTwoEdgeLoadKernel later source target)
    (fun source hsource target htarget => by
      have hcapacity := capacity.old_old source hsource target htarget
      unfold cutoffTwoNovelAllocatedKernel at hcapacity
      rw [dif_pos ⟨hsource, htarget⟩] at hcapacity
      exact hcapacity)
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv (by
      unfold cutoffTwoOldOldDirichlet cutoffTwoEdgeLoadOldStates
        cutoffTwoEdgeLoadKernel
      exact finiteJointDirichletBlock_scale_joint_local
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0)
        (centralPhysicalFiniteVacuumSectorOldBlockIndices
          cutoffTwoHalfCoupling (by decide) 2 later 0)
        coefficient HalfPow.half
        (centralPhysicalFiniteKernel
          cutoffTwoHalfCoupling (by decide) later 0)))

theorem loaded_oldNew_le_physical
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricLoadedOldNewDirichlet later coefficient ≤
      cutoffTwoOldNewDirichlet later coefficient := by
  exact scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadNewStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelSymmetricEdgeLoad later)
    (cutoffTwoEdgeLoadKernel later)
    (fun source hsource target htarget => by
      have hcapacity := capacity.old_new source hsource target htarget
      unfold cutoffTwoNovelAllocatedKernel at hcapacity
      have htargetNotOld :
          target ∉ cutoffTwoEdgeLoadOldStates later := by
        intro htargetOld
        unfold cutoffTwoEdgeLoadOldStates at htargetOld
        unfold cutoffTwoEdgeLoadNewStates at htarget
        have holdDecision := (List.mem_filter.mp htargetOld).2
        have hnewDecision := (List.mem_filter.mp htarget).2
        simp only [holdDecision, Bool.not_true] at hnewDecision
        exact Bool.noConfusion hnewDecision
      rw [dif_neg (fun h => htargetNotOld h.2)] at hcapacity
      exact hcapacity)

theorem loaded_newOld_le_physical
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricLoadedNewOldDirichlet later coefficient ≤
      cutoffTwoNewOldDirichlet later coefficient := by
  exact scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadOldStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelSymmetricEdgeLoad later)
    (cutoffTwoEdgeLoadKernel later)
    (fun source hsource target htarget => by
      have hcapacity := capacity.new_old source hsource target htarget
      unfold cutoffTwoNovelAllocatedKernel at hcapacity
      have hsourceNotOld :
          source ∉ cutoffTwoEdgeLoadOldStates later := by
        intro hsourceOld
        unfold cutoffTwoEdgeLoadOldStates at hsourceOld
        unfold cutoffTwoEdgeLoadNewStates at hsource
        have holdDecision := (List.mem_filter.mp hsourceOld).2
        have hnewDecision := (List.mem_filter.mp hsource).2
        simp only [holdDecision, Bool.not_true] at hnewDecision
        exact Bool.noConfusion hnewDecision
      rw [dif_neg (fun h => hsourceNotOld h.1)] at hcapacity
      exact hcapacity)

theorem loaded_newNew_le_physical
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricLoadedNewNewDirichlet later coefficient ≤
      cutoffTwoNewNewDirichlet later coefficient := by
  exact scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadNewStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelSymmetricEdgeLoad later)
    (cutoffTwoEdgeLoadKernel later)
    (fun source hsource target htarget => by
      have hcapacity := capacity.new_new source hsource target htarget
      unfold cutoffTwoNovelAllocatedKernel at hcapacity
      have hsourceNotOld :
          source ∉ cutoffTwoEdgeLoadOldStates later := by
        intro hsourceOld
        unfold cutoffTwoEdgeLoadOldStates at hsourceOld
        unfold cutoffTwoEdgeLoadNewStates at hsource
        have holdDecision := (List.mem_filter.mp hsourceOld).2
        have hnewDecision := (List.mem_filter.mp hsource).2
        simp only [holdDecision, Bool.not_true] at hnewDecision
        exact Bool.noConfusion hnewDecision
      rw [dif_neg (fun h => hsourceNotOld h.1)] at hcapacity
      exact hcapacity)

theorem scaled_symmetricRawLoaded_le_allocated_physical
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSymmetricRawLoadedDirichlet later coefficient ≤
      (HalfPow.half * cutoffTwoOldOldDirichlet later coefficient +
        cutoffTwoOldNewDirichlet later coefficient) +
      (cutoffTwoNewOldDirichlet later coefficient +
        cutoffTwoNewNewDirichlet later coefficient) := by
  have hblocks := Q'.add_le_add
    (Q'.add_le_add
      (loaded_oldOld_le_half_physical capacity coefficient)
      (loaded_oldNew_le_physical capacity coefficient))
    (Q'.add_le_add
      (loaded_newOld_le_physical capacity coefficient)
      (loaded_newNew_le_physical capacity coefficient))
  refine Q'.le_trans' _ _ _ ?_ hblocks
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
        ((cutoffTwoNovelSymmetricLoadedOldOldDirichlet later coefficient +
            cutoffTwoNovelSymmetricLoadedOldNewDirichlet later coefficient) +
          (cutoffTwoNovelSymmetricLoadedNewOldDirichlet later coefficient +
            cutoffTwoNovelSymmetricLoadedNewNewDirichlet later coefficient))) _
      (Q'.mul_eqv_congr_left cutoffTwoNovelSimpleFlowCoercivityFloor _ _
        (cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_four_blocks
          later coefficient))
      (Q'.eqv_trans _
        (cutoffTwoNovelSimpleFlowCoercivityFloor *
              (cutoffTwoNovelSymmetricLoadedOldOldDirichlet later coefficient +
                cutoffTwoNovelSymmetricLoadedOldNewDirichlet later coefficient) +
          cutoffTwoNovelSimpleFlowCoercivityFloor *
              (cutoffTwoNovelSymmetricLoadedNewOldDirichlet later coefficient +
                cutoffTwoNovelSymmetricLoadedNewNewDirichlet later coefficient)) _
        (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv _ _ _)
          (Q'.mul_add_eqv _ _ _))))

theorem floor_mul_novelPairwiseVariance_le_allocated_physical
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelPairwiseVariance later coefficient ≤
      (HalfPow.half * cutoffTwoOldOldDirichlet later coefficient +
        cutoffTwoOldNewDirichlet later coefficient) +
      (cutoffTwoNewOldDirichlet later coefficient +
        cutoffTwoNewNewDirichlet later coefficient) := by
  have hraw :=
    cutoffTwoNovelPairwiseVariance_le_symmetricRawLoadedDirichlet
      later coefficient
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _
    cutoffTwoNovelSimpleFlowCoercivityFloor hraw
    (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
  exact Q'.le_trans' _ _ _ hscale
    (scaled_symmetricRawLoaded_le_allocated_physical capacity coefficient)

/-! ## 4. Full-sector and completed-gap compilers -/

private theorem fullPairwise_eqv_oldOld_add_novel
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoFullSectorPairwiseVariance later coefficient ≈
      cutoffTwoOldOldPairwiseVariance later coefficient +
        cutoffTwoNovelPairwiseVariance later coefficient := by
  refine Q'.eqv_trans _
    ((cutoffTwoOldOldPairwiseVariance later coefficient +
        cutoffTwoNewNewPairwiseVariance later coefficient) +
      cutoffTwoCrossBlockPairwiseVariance later coefficient) _
    (cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross
      later coefficient) ?_
  refine Q'.eqv_trans _
    (cutoffTwoOldOldPairwiseVariance later coefficient +
      (cutoffTwoNewNewPairwiseVariance later coefficient +
        cutoffTwoCrossBlockPairwiseVariance later coefficient)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  exact Q'.add_eqv_congr_left _ _ _
    (Q'.eqv_symm
      (cutoffTwoNovelPairwiseVariance_eqv_newNew_add_cross
        later coefficient))

private theorem floor_mul_oldOldPairwise_le_half_physical
    {later : Nat}
    (hlater : cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoOldOldPairwiseVariance later coefficient ≤
      HalfPow.half * cutoffTwoOldOldDirichlet later coefficient := by
  have hold :=
    cutoffTwoUniformOldBlockCoercivityFloor_mul_oldOldPairwise_le_Dirichlet
      later hlater coefficient
  have hscaled := Q'.mul_le_mul_of_nonneg_left _ _ HalfPow.half hold
    HalfPow.half_nonneg
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (by
      unfold cutoffTwoNovelSimpleFlowCoercivityFloor
      exact Q'.mul_assoc_eqv _ _ _))
    hscaled

private theorem two_half_old_allocations_eqv_full
    (oldOld oldNew newOld newNew : Q') :
    HalfPow.half * oldOld +
        ((HalfPow.half * oldOld + oldNew) + (newOld + newNew)) ≈
      (oldOld + oldNew) + (newOld + newNew) := by
  refine Q'.eqv_trans _
    ((HalfPow.half * oldOld + (HalfPow.half * oldOld + oldNew)) +
      (newOld + newNew)) _
    (Q'.eqv_symm
      (Q'.add_assoc_eqv
        (HalfPow.half * oldOld)
        (HalfPow.half * oldOld + oldNew)
        (newOld + newNew))) ?_
  refine Q'.eqv_trans _
    (((HalfPow.half * oldOld + HalfPow.half * oldOld) + oldNew) +
      (newOld + newNew)) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.eqv_symm
        (Q'.add_assoc_eqv
          (HalfPow.half * oldOld) (HalfPow.half * oldOld) oldNew))
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.add_eqv_congr_right _ _ oldNew
        (ExpNeg.two_halves oldOld))

/-- The symmetry-reduced local certificate, old-block coercivity, and mass
floor compile to the standard full-sector coercivity datum. -/
def toFullSectorDirichletCoercivityAt
    {later : Nat}
    (capacity : CutoffTwoNovelSymmetricOrientedCapacityAt later)
    (hlaterFloor :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (hlaterMass :
      cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later) :
    CutoffTwoFullSectorDirichletCoercivityAt later
      cutoffTwoNovelSimpleFlowCoercivityFloor
      cutoffTwoUniformVacuumSectorMassFloor where
  later_ge := Nat.le_trans
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
    hlaterFloor
  mass_floor_le := cutoffTwoUniformVacuumSectorMassFloor_le hlaterMass
  full_coercivity := by
    intro coefficient
    have hsum := Q'.add_le_add
      (floor_mul_oldOldPairwise_le_half_physical
        hlaterFloor coefficient)
      (floor_mul_novelPairwiseVariance_le_allocated_physical
        capacity coefficient)
    refine Q'.le_trans'
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoFullSectorPairwiseVariance later coefficient)
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoOldOldPairwiseVariance later coefficient +
        cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelPairwiseVariance later coefficient)
      (cutoffTwoFullSectorDirichlet later coefficient) ?_ ?_
    · exact Q'.le_of_eqv
        (Q'.eqv_trans _
          (cutoffTwoNovelSimpleFlowCoercivityFloor *
            (cutoffTwoOldOldPairwiseVariance later coefficient +
              cutoffTwoNovelPairwiseVariance later coefficient)) _
          (Q'.mul_eqv_congr_left cutoffTwoNovelSimpleFlowCoercivityFloor _ _
            (fullPairwise_eqv_oldOld_add_novel later coefficient))
          (Q'.mul_add_eqv _ _ _))
    refine Q'.le_trans' _ _ _ hsum ?_
    refine Q'.le_trans' _
      ((cutoffTwoOldOldDirichlet later coefficient +
          cutoffTwoOldNewDirichlet later coefficient) +
        (cutoffTwoNewOldDirichlet later coefficient +
          cutoffTwoNewNewDirichlet later coefficient)) _ ?_ ?_
    · exact Q'.le_of_eqv
        (two_half_old_allocations_eqv_full _ _ _ _)
    · exact Q'.ge_of_eqv
        (cutoffTwoFullSectorDirichlet_four_blocks later coefficient)

end CutoffTwoNovelSymmetricOrientedCapacityAt

/-! ## 5. Cofinal orientation-reduced capacity reaches completion -/

structure CutoffTwoCofinalNovelSymmetricOrientedCapacity : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  capacity : ∀ request,
    CutoffTwoNovelSymmetricOrientedCapacityAt (anchor request)

namespace CutoffTwoCofinalNovelSymmetricOrientedCapacity

def toFiniteStrictGap
    (family : CutoffTwoCofinalNovelSymmetricOrientedCapacity) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      cutoffTwoHalfCoupling (by decide) 0
      (cutoffTwoDirichletGluingRate
        cutoffTwoNovelSimpleFlowCoercivityFloor
        cutoffTwoUniformVacuumSectorMassFloor
        cutoffTwoNovelSimpleFlowCoercivityFloor_pos
        cutoffTwoUniformVacuumSectorMassFloor_pos) where
  rate_nonnegative := cutoffTwoDirichletGluingRate_nonnegative
    cutoffTwoNovelSimpleFlowCoercivityFloor_pos
    cutoffTwoUniformVacuumSectorMassFloor_pos
  rate_lt_one := cutoffTwoDirichletGluingRate_lt_one
    cutoffTwoNovelSimpleFlowCoercivityFloor_pos
    cutoffTwoUniformVacuumSectorMassFloor_pos
  anchor := family.anchor
  anchor_ge := by
    intro request
    have hfamily := family.anchor_ge request
    have htwo := cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
    omega
  sectorGap := by
    intro request coefficient hcenter
    have hanchor := family.anchor_ge request
    have hfloor :
        cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤
          family.anchor request :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hanchor)
    have hmass :
        cutoffTwoUniformVacuumSectorMassFloorAnchor ≤
          family.anchor request :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_trans (Nat.le_max_left _ _) hanchor)
    exact
      YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.CutoffTwoNovelSymmetricOrientedCapacityAt.toFullSectorDirichletCoercivityAt
        (family.capacity request) hfloor hmass
      |>.abs_matrix_le_rate_mul_diagonal
        cutoffTwoNovelSimpleFlowCoercivityFloor_pos
        cutoffTwoUniformVacuumSectorMassFloor_pos
        coefficient hcenter

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelSymmetricOrientedCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    family.toFiniteStrictGap

end CutoffTwoCofinalNovelSymmetricOrientedCapacity

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.CutoffTwoNovelSymmetricOrientedCapacityAt.full_capacity
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.cutoffTwoNovelSymmetricRawLoadedDirichlet_eqv_four_blocks
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.CutoffTwoNovelSymmetricOrientedCapacityAt.loaded_oldOld_le_half_physical
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.CutoffTwoNovelSymmetricOrientedCapacityAt.floor_mul_novelPairwiseVariance_le_allocated_physical
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.CutoffTwoNovelSymmetricOrientedCapacityAt.toFullSectorDirichletCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelFlowSymmetricCapacity.CutoffTwoCofinalNovelSymmetricOrientedCapacity.toCompletedStrictContractionData
