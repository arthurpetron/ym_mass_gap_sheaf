/-
# Novel simple-flow capacity compiles to the full cutoff-two gap

The fixed cutoff-two old block has a constructed uniform coercivity floor.
The preceding floor-free flow module controls every stationary endpoint pair
with at least one genuinely new endpoint by one explicit raw directed-edge
load.  This module spends half of the old-block physical energy on the old
variance and reserves the other half for paths of novel endpoint pairs.

Consequently one coefficient-independent pointwise capacity certificate,

  delta * novelLoad(edge) <= allocatedPhysicalKernel(edge),

where old-old edges receive half capacity and all other edges receive full
capacity, compiles to full-sector Dirichlet coercivity.  A constructively
cofinal family of these finite certificates then reaches the already proved
completed vacuum-sector strict contraction.

The pointwise capacity family is not inhabited here.  No thermodynamic or
continuum limit, continuum QFT construction, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlow

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity

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
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEdgeLoad
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

/-! ## 1. The explicit half-strength and exact block forms -/

/-- Half of the already constructed uniform old-block floor.  The first half
pays for old endpoint variance; the second half of old physical capacity is
available to novel paths that traverse old-old edges. -/
def cutoffTwoNovelSimpleFlowCoercivityFloor : Q' :=
  HalfPow.half * cutoffTwoUniformOldBlockCoercivityFloor

theorem cutoffTwoNovelSimpleFlowCoercivityFloor_pos :
    (0 : Q') < cutoffTwoNovelSimpleFlowCoercivityFloor := by
  unfold cutoffTwoNovelSimpleFlowCoercivityFloor
  exact ExpNeg.half_mul_pos _
    cutoffTwoUniformOldBlockCoercivityFloor_pos

private def cutoffTwoNovelRawLoadedJoint
    (later : Nat) : Nat → Nat → Q' :=
  fun source target =>
    cutoffTwoNovelSimpleEdgeLoad later source target * 1

def cutoffTwoNovelRawLoadedOldOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadOldStates later)
    coefficient (cutoffTwoNovelRawLoadedJoint later)

def cutoffTwoNovelRawLoadedOldNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadNewStates later)
    coefficient (cutoffTwoNovelRawLoadedJoint later)

def cutoffTwoNovelRawLoadedNewOldDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadOldStates later)
    coefficient (cutoffTwoNovelRawLoadedJoint later)

def cutoffTwoNovelRawLoadedNewNewDirichlet
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteJointDirichletBlock
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadNewStates later)
    coefficient (cutoffTwoNovelRawLoadedJoint later)

/-- Exact old/new partition of the regrouped raw novel flow. -/
theorem cutoffTwoNovelRawLoadedDirichlet_eqv_four_blocks
    (later : Nat) (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleRawLoadedDirichlet later coefficient ≈
      (cutoffTwoNovelRawLoadedOldOldDirichlet later coefficient +
        cutoffTwoNovelRawLoadedOldNewDirichlet later coefficient) +
      (cutoffTwoNovelRawLoadedNewOldDirichlet later coefficient +
        cutoffTwoNovelRawLoadedNewNewDirichlet later coefficient) := by
  unfold cutoffTwoNovelSimpleRawLoadedDirichlet
    finiteWeightedOccurrenceLoadedDirichlet
  change finiteJointDirichletEnergy
      (cutoffTwoEdgeLoadFullStates later) coefficient
      (cutoffTwoNovelRawLoadedJoint later) ≈ _
  unfold cutoffTwoNovelRawLoadedOldOldDirichlet
    cutoffTwoNovelRawLoadedOldNewDirichlet
    cutoffTwoNovelRawLoadedNewOldDirichlet
    cutoffTwoNovelRawLoadedNewNewDirichlet
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

/-! ## 2. Pointwise joint domination scales a finite Dirichlet block -/

private theorem finiteJointDirichletBlock_scale_joint
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

/-- A pointwise comparison after scaling the loaded joint controls the whole
finite Dirichlet block.  This formulation compares load directly to physical
capacity and does not divide by a possibly tiny kernel entry. -/
theorem scale_mul_finiteJointDirichletBlock_le_of_joint_le
    {State : Type}
    (leftStates rightStates : List State)
    (coefficient : State → Q')
    (scale : Q') (load kernel : State → State → Q')
    (hjoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        scale * load left right ≤ kernel left right) :
    scale * finiteJointDirichletBlock
        leftStates rightStates coefficient load ≤
      finiteJointDirichletBlock
        leftStates rightStates coefficient kernel := by
  have hsum :
      finiteJointDirichletBlock leftStates rightStates coefficient
          (fun left right => scale * load left right) ≤
        finiteJointDirichletBlock leftStates rightStates coefficient kernel := by
    unfold finiteJointDirichletBlock
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact Q'.mul_le_mul_of_nonneg_right _ _ _
      (hjoint left hleft right hright)
      (SumOfSquares.q_mul_self_nonneg
        (coefficient left + -coefficient right))
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.eqv_symm
        (finiteJointDirichletBlock_scale_joint
          leftStates rightStates coefficient scale load)))
    hsum

/-! ## 3. One local capacity certificate controls all novel variance -/

/-- Coefficient-independent capacity comparison for the one explicit novel
flow.  Old-old edges receive the half of their physical capacity not spent
on the proved old-block variance; every other edge receives full capacity. -/
structure CutoffTwoNovelSimpleFlowCapacityAt (later : Nat) : Type 1 where
  later_ge_pulled_floor :
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later
  later_ge_mass_floor :
    cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later
  old_old : ∀ source, source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        HalfPow.half * cutoffTwoEdgeLoadKernel later source target
  old_new : ∀ source, source ∈ cutoffTwoEdgeLoadOldStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        cutoffTwoEdgeLoadKernel later source target
  new_old : ∀ source, source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadOldStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        cutoffTwoEdgeLoadKernel later source target
  new_new : ∀ source, source ∈ cutoffTwoEdgeLoadNewStates later →
    ∀ target, target ∈ cutoffTwoEdgeLoadNewStates later →
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤
        cutoffTwoEdgeLoadKernel later source target

namespace CutoffTwoNovelSimpleFlowCapacityAt

private theorem scaled_loaded_joint_le_of_capacity
    {later source target : Nat}
    (upper : Q')
    (hcapacity :
      cutoffTwoNovelSimpleFlowCoercivityFloor *
          cutoffTwoNovelSimpleEdgeLoad later source target ≤ upper) :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelRawLoadedJoint later source target ≤ upper := by
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left
        cutoffTwoNovelSimpleFlowCoercivityFloor _ _
        (Q'.mul_one_eqv
          (cutoffTwoNovelSimpleEdgeLoad later source target))))
    hcapacity

theorem loaded_oldOld_le_half_physical
    {later : Nat} (capacity : CutoffTwoNovelSimpleFlowCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelRawLoadedOldOldDirichlet later coefficient ≤
      HalfPow.half * cutoffTwoOldOldDirichlet later coefficient := by
  have h := scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadOldStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelRawLoadedJoint later)
    (fun source target =>
      HalfPow.half * cutoffTwoEdgeLoadKernel later source target)
    (fun source hsource target htarget =>
      scaled_loaded_joint_le_of_capacity _
        (capacity.old_old source hsource target htarget))
  exact Q'.le_trans' _ _ _ h
    (Q'.le_of_eqv
      (finiteJointDirichletBlock_scale_joint
        (cutoffTwoEdgeLoadOldStates later)
        (cutoffTwoEdgeLoadOldStates later) coefficient HalfPow.half
        (cutoffTwoEdgeLoadKernel later)))

theorem loaded_oldNew_le_physical
    {later : Nat} (capacity : CutoffTwoNovelSimpleFlowCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelRawLoadedOldNewDirichlet later coefficient ≤
      cutoffTwoOldNewDirichlet later coefficient := by
  exact scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadOldStates later)
    (cutoffTwoEdgeLoadNewStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelRawLoadedJoint later)
    (cutoffTwoEdgeLoadKernel later)
    (fun source hsource target htarget =>
      scaled_loaded_joint_le_of_capacity _
        (capacity.old_new source hsource target htarget))

theorem loaded_newOld_le_physical
    {later : Nat} (capacity : CutoffTwoNovelSimpleFlowCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelRawLoadedNewOldDirichlet later coefficient ≤
      cutoffTwoNewOldDirichlet later coefficient := by
  exact scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadOldStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelRawLoadedJoint later)
    (cutoffTwoEdgeLoadKernel later)
    (fun source hsource target htarget =>
      scaled_loaded_joint_le_of_capacity _
        (capacity.new_old source hsource target htarget))

theorem loaded_newNew_le_physical
    {later : Nat} (capacity : CutoffTwoNovelSimpleFlowCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelRawLoadedNewNewDirichlet later coefficient ≤
      cutoffTwoNewNewDirichlet later coefficient := by
  exact scale_mul_finiteJointDirichletBlock_le_of_joint_le
    (cutoffTwoEdgeLoadNewStates later)
    (cutoffTwoEdgeLoadNewStates later) coefficient
    cutoffTwoNovelSimpleFlowCoercivityFloor
    (cutoffTwoNovelRawLoadedJoint later)
    (cutoffTwoEdgeLoadKernel later)
    (fun source hsource target htarget =>
      scaled_loaded_joint_le_of_capacity _
        (capacity.new_new source hsource target htarget))

/-- The four local capacity inequalities control the whole novel loaded form
while reserving exactly half of the old-old energy. -/
theorem scaled_rawLoaded_le_allocated_physical
    {later : Nat} (capacity : CutoffTwoNovelSimpleFlowCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelSimpleRawLoadedDirichlet later coefficient ≤
      (HalfPow.half * cutoffTwoOldOldDirichlet later coefficient +
        cutoffTwoOldNewDirichlet later coefficient) +
      (cutoffTwoNewOldDirichlet later coefficient +
        cutoffTwoNewNewDirichlet later coefficient) := by
  have hblocks := Q'.add_le_add
    (Q'.add_le_add
      (capacity.loaded_oldOld_le_half_physical coefficient)
      (capacity.loaded_oldNew_le_physical coefficient))
    (Q'.add_le_add
      (capacity.loaded_newOld_le_physical coefficient)
      (capacity.loaded_newNew_le_physical coefficient))
  refine Q'.le_trans' _ _ _ ?_ hblocks
  exact Q'.le_of_eqv
    (Q'.eqv_trans _
      (cutoffTwoNovelSimpleFlowCoercivityFloor *
        ((cutoffTwoNovelRawLoadedOldOldDirichlet later coefficient +
            cutoffTwoNovelRawLoadedOldNewDirichlet later coefficient) +
          (cutoffTwoNovelRawLoadedNewOldDirichlet later coefficient +
            cutoffTwoNovelRawLoadedNewNewDirichlet later coefficient))) _
      (Q'.mul_eqv_congr_left cutoffTwoNovelSimpleFlowCoercivityFloor _ _
        (cutoffTwoNovelRawLoadedDirichlet_eqv_four_blocks
          later coefficient))
      (Q'.eqv_trans _
        (cutoffTwoNovelSimpleFlowCoercivityFloor *
              (cutoffTwoNovelRawLoadedOldOldDirichlet later coefficient +
                cutoffTwoNovelRawLoadedOldNewDirichlet later coefficient) +
          cutoffTwoNovelSimpleFlowCoercivityFloor *
              (cutoffTwoNovelRawLoadedNewOldDirichlet later coefficient +
                cutoffTwoNovelRawLoadedNewNewDirichlet later coefficient)) _
        (Q'.mul_add_eqv _ _ _)
        (Q'.add_eqv_congr'
          (Q'.mul_add_eqv _ _ _)
          (Q'.mul_add_eqv _ _ _))))

/-- The local capacity certificate gives coercivity for exactly the endpoint
pairs not already controlled by the fixed old block. -/
theorem floor_mul_novelPairwiseVariance_le_allocated_physical
    {later : Nat} (capacity : CutoffTwoNovelSimpleFlowCapacityAt later)
    (coefficient : Nat → Q') :
    cutoffTwoNovelSimpleFlowCoercivityFloor *
        cutoffTwoNovelPairwiseVariance later coefficient ≤
      (HalfPow.half * cutoffTwoOldOldDirichlet later coefficient +
        cutoffTwoOldNewDirichlet later coefficient) +
      (cutoffTwoNewOldDirichlet later coefficient +
        cutoffTwoNewNewDirichlet later coefficient) := by
  have hraw := cutoffTwoNovelPairwiseVariance_le_rawLoadedDirichlet
    later coefficient
  have hscale := Q'.mul_le_mul_of_nonneg_left _ _
    cutoffTwoNovelSimpleFlowCoercivityFloor hraw
    (Q'.le_of_lt cutoffTwoNovelSimpleFlowCoercivityFloor_pos)
  exact Q'.le_trans' _ _ _ hscale
    (capacity.scaled_rawLoaded_le_allocated_physical coefficient)

/-! ## 4. Combine the fixed old block with the novel flow -/

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

/-- The pointwise flow-capacity certificate, the constructed old coercivity,
and the constructed mass floor compile to the minimal full-sector coercivity
interface at the explicit positive half-strength. -/
def toFullSectorDirichletCoercivityAt
    {later : Nat} (capacity : CutoffTwoNovelSimpleFlowCapacityAt later) :
    CutoffTwoFullSectorDirichletCoercivityAt later
      cutoffTwoNovelSimpleFlowCoercivityFloor
      cutoffTwoUniformVacuumSectorMassFloor where
  later_ge := Nat.le_trans
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
    capacity.later_ge_pulled_floor
  mass_floor_le := cutoffTwoUniformVacuumSectorMassFloor_le
    capacity.later_ge_mass_floor
  full_coercivity := by
    intro coefficient
    have hsum := Q'.add_le_add
      (floor_mul_oldOldPairwise_le_half_physical
        capacity.later_ge_pulled_floor coefficient)
      (capacity.floor_mul_novelPairwiseVariance_le_allocated_physical
        coefficient)
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

end CutoffTwoNovelSimpleFlowCapacityAt

/-! ## 5. A cofinal local-capacity family reaches completion -/

/-- The sole remaining finite analytic input is a constructively cofinal
family of the explicit coefficient-independent edge-capacity comparisons. -/
structure CutoffTwoCofinalNovelSimpleFlowCapacity : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  capacity : ∀ request,
    CutoffTwoNovelSimpleFlowCapacityAt (anchor request)

namespace CutoffTwoCofinalNovelSimpleFlowCapacity

def toFiniteStrictGap
    (family : CutoffTwoCofinalNovelSimpleFlowCapacity) :
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
    exact (family.capacity request).toFullSectorDirichletCoercivityAt
      |>.abs_matrix_le_rate_mul_diagonal
        cutoffTwoNovelSimpleFlowCoercivityFloor_pos
        cutoffTwoUniformVacuumSectorMassFloor_pos
        coefficient hcenter

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNovelSimpleFlowCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    family.toFiniteStrictGap

end CutoffTwoCofinalNovelSimpleFlowCapacity

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity.cutoffTwoNovelSimpleFlowCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity.scale_mul_finiteJointDirichletBlock_le_of_joint_le
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity.CutoffTwoNovelSimpleFlowCapacityAt.floor_mul_novelPairwiseVariance_le_allocated_physical
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity.CutoffTwoNovelSimpleFlowCapacityAt.toFullSectorDirichletCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoNovelSimpleFlowCapacity.CutoffTwoCofinalNovelSimpleFlowCapacity.toCompletedStrictContractionData
