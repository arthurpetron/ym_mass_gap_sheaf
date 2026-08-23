/-
# Uniform coercivity on the embedded cutoff-two block

The growing canonical vacuum sector contains an exact embedded copy of the
cutoff-two component.  The transported cutoff-two canonical paths already
have a constructed cutoff-uniform positive edge floor.  Summing their
endpoint estimates against the pulled stationary weights, using that the
pulled mass is at most one, and dividing by the fixed positive path ceiling
gives one explicit positive coercivity floor for arbitrary coefficients on
that fixed carrier.  No centering assumption is needed because pairwise
variance is shift invariant.

This module then transports both the stationary-product pairwise variance
and physical Dirichlet energy through the exact cutoff index embedding.  It
therefore constructs the old-old part of the later full-sector gluing
certificate.  The remaining cofinal input has only two analytic fields:
coercivity on genuinely new pairs and coercivity across the old/new cut.

No such new/cross family is inhabited here.  In particular no uniform full
gap, thermodynamic/continuum limit, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorOldPullbackResidual
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformSectorMassFloor
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

private theorem divPos_mul_right_eqv_local
    (scale value denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (scale * value) denominator hdenominator ≈
      Q'.divPos scale denominator hdenominator * value := by
  unfold Q'.divPos
  q_ring

/-! ## 1. Shift-invariant coercivity on the pulled fixed carrier -/

/-- The fixed positive path edges control pulled pairwise variance by the
fixed path ceiling times pulled Dirichlet energy, for every coefficient and
without a centering hypothesis. -/
theorem pulledFloor_mul_pairwiseVariance_le_ceiling_mul_Dirichlet
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    certificate.floor *
        finiteWeightedPairwiseVariance
          cutoffTwoPulledStates (cutoffTwoPulledWeightAt later) coefficient ≤
      cutoffTwoPulledCanonicalPathCeiling *
        finiteJointDirichletEnergy
          cutoffTwoPulledStates coefficient (cutoffTwoPulledKernelAt later) := by
  let mass := cutoffTwoPulledMassAt later
  let energy := finiteJointDirichletEnergy
    cutoffTwoPulledStates coefficient (cutoffTwoPulledKernelAt later)
  have htwoLater : 2 ≤ later :=
    Nat.le_trans certificate.start_ge_two hlater
  have hraw : certificate.floor *
        finiteWeightedPairwiseVariance
          cutoffTwoPulledStates (cutoffTwoPulledWeightAt later) coefficient ≤
      (mass * mass) *
        (cutoffTwoPulledCanonicalPathCeiling * energy) := by
    exact floor_mul_finiteWeightedPairwiseVariance_le
      cutoffTwoPulledStates (cutoffTwoPulledWeightAt later) coefficient
      certificate.floor cutoffTwoPulledCanonicalPathCeiling energy
      (fun state _hstate => by
        unfold cutoffTwoPulledWeightAt
        exact centralPhysicalFinitePulledWeight_nonnegative
          cutoffTwoHalfCoupling (by decide) 2 later 0 state)
      (fun left hleft right hright =>
        certificate.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
          later hlater coefficient left right hleft hright)
  have hmass0 : (0 : Q') ≤ mass :=
    Q'.le_of_lt (cutoffTwoPulledMassAt_pos later)
  have hmass1 : mass ≤ 1 := cutoffTwoPulledMassAt_le_one later htwoLater
  have hmassSquare : mass * mass ≤ 1 := by
    have hfirst : mass * mass ≤ 1 * mass :=
      Q'.mul_le_mul_of_nonneg_right _ _ _ hmass1 hmass0
    have hsecond : 1 * mass ≤ 1 * 1 :=
      Q'.mul_le_mul_of_nonneg_left _ _ _ hmass1
        (by decide : (0 : Q') ≤ 1)
    exact Q'.le_trans' _ _ _ hfirst
      (Q'.le_trans' _ _ _ hsecond
        (Q'.le_of_eqv (Q'.one_mul_eqv 1)))
  have hkernel : ∀ source target,
      (0 : Q') ≤ cutoffTwoPulledKernelAt later source target := by
    intro source target
    unfold cutoffTwoPulledKernelAt centralPhysicalFinitePulledKernel
      centralPhysicalFiniteKernel
    exact centralNormalizedPhysicalReflectedKernel_nonnegative
      (by decide) later 0 _ _
  have henergy0 : (0 : Q') ≤ energy :=
    finiteJointDirichletEnergy_nonnegative
      cutoffTwoPulledStates coefficient (cutoffTwoPulledKernelAt later)
      hkernel
  have hscaled0 : (0 : Q') ≤
      cutoffTwoPulledCanonicalPathCeiling * energy :=
    Q'.mul_nonneg _ _
      (Q'.le_of_lt cutoffTwoPulledCanonicalPathCeiling_pos) henergy0
  have hmassScaled :
      (mass * mass) *
          (cutoffTwoPulledCanonicalPathCeiling * energy) ≤
        1 * (cutoffTwoPulledCanonicalPathCeiling * energy) :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hmassSquare hscaled0
  exact Q'.le_trans' _ _ _ hraw
    (Q'.le_trans' _ _ _ hmassScaled
      (Q'.le_of_eqv
        (Q'.one_mul_eqv (cutoffTwoPulledCanonicalPathCeiling * energy))))

/-- Divide the constructed pulled edge floor by the fixed positive path
ceiling.  This is the explicit cutoff-independent old-block coercivity
constant used below. -/
def cutoffTwoUniformOldBlockCoercivityFloor : Q' :=
  Q'.divPos
    cutoffTwoPulledUniformBasePositiveEdgeFloor.floor
    cutoffTwoPulledCanonicalPathCeiling
    cutoffTwoPulledCanonicalPathCeiling_pos

theorem cutoffTwoUniformOldBlockCoercivityFloor_pos :
    (0 : Q') < cutoffTwoUniformOldBlockCoercivityFloor := by
  unfold cutoffTwoUniformOldBlockCoercivityFloor
  exact Q'.divPos_pos _ _ cutoffTwoPulledCanonicalPathCeiling_pos
    cutoffTwoPulledUniformBasePositiveEdgeFloor.floor_pos

/-- The constructed normalized floor controls arbitrary pulled pairwise
variance directly by pulled Dirichlet energy. -/
theorem cutoffTwoUniformOldBlockCoercivityFloor_mul_pulledPairwise_le_Dirichlet
    (later : Nat)
    (hlater : cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (coefficient : Nat → Q') :
    cutoffTwoUniformOldBlockCoercivityFloor *
        finiteWeightedPairwiseVariance
          cutoffTwoPulledStates (cutoffTwoPulledWeightAt later) coefficient ≤
      finiteJointDirichletEnergy
        cutoffTwoPulledStates coefficient (cutoffTwoPulledKernelAt later) := by
  let pairwise := finiteWeightedPairwiseVariance
    cutoffTwoPulledStates (cutoffTwoPulledWeightAt later) coefficient
  let energy := finiteJointDirichletEnergy
    cutoffTwoPulledStates coefficient (cutoffTwoPulledKernelAt later)
  have hraw := pulledFloor_mul_pairwiseVariance_le_ceiling_mul_Dirichlet
    cutoffTwoPulledUniformBasePositiveEdgeFloor later hlater coefficient
  have hcommuted :
      cutoffTwoPulledUniformBasePositiveEdgeFloor.floor * pairwise ≤
        energy * cutoffTwoPulledCanonicalPathCeiling :=
    Q'.le_trans' _ _ _ hraw
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv cutoffTwoPulledCanonicalPathCeiling energy))
  have hquot :
      Q'.divPos
          (cutoffTwoPulledUniformBasePositiveEdgeFloor.floor * pairwise)
          cutoffTwoPulledCanonicalPathCeiling
          cutoffTwoPulledCanonicalPathCeiling_pos ≤ energy :=
    Q'.divPos_le_of_le_mul _ _ cutoffTwoPulledCanonicalPathCeiling_pos
      hcommuted
  refine Q'.le_trans' _ _ _ ?_ hquot
  exact Q'.le_of_eqv
    (Q'.eqv_symm
      (divPos_mul_right_eqv_local
        cutoffTwoPulledUniformBasePositiveEdgeFloor.floor pairwise
        cutoffTwoPulledCanonicalPathCeiling
        cutoffTwoPulledCanonicalPathCeiling_pos))

/-! ## 2. Exact transport from the pulled carrier to the old block -/

private theorem listQSum_perm_local {A : Type} (value : A → Q') :
    ∀ {left right : List A}, left.Perm right →
      listQSum value left ≈ listQSum value right
  | _, _, List.Perm.nil => Q'.eqv_refl 0
  | _, _, List.Perm.cons _ hperm =>
      Q'.add_eqv_congr_left _ _ _ (listQSum_perm_local value hperm)
  | _, _, List.Perm.swap first second rest => by
      change value second + (value first + listQSum value rest) ≈
        value first + (value second + listQSum value rest)
      refine Q'.eqv_trans _
        ((value second + value first) + listQSum value rest) _
        (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
      refine Q'.eqv_trans _
        ((value first + value second) + listQSum value rest) _
        (Q'.add_eqv_congr_right _ _ _
          (Q'.add_comm_eqv _ _)) ?_
      exact Q'.add_assoc_eqv _ _ _
  | _, _, List.Perm.trans hleft hright =>
      Q'.eqv_trans _ _ _
        (listQSum_perm_local value hleft)
        (listQSum_perm_local value hright)

private theorem listQSum_map_local
    {A B : Type} (value : B → Q') (map : A → B) :
    ∀ items : List A,
      listQSum value (items.map map) =
        listQSum (fun item => value (map item)) items
  | [] => rfl
  | _ :: tail => by
      simp only [List.map, listQSum]
      rw [listQSum_map_local value map tail]

private theorem finiteJointDirichletBlock_perm_local
    {State : Type}
    {leftOld leftNew rightOld rightNew : List State}
    (hleft : leftOld.Perm leftNew) (hright : rightOld.Perm rightNew)
    (coefficient : State → Q') (joint : State → State → Q') :
    finiteJointDirichletBlock leftOld rightOld coefficient joint ≈
      finiteJointDirichletBlock leftNew rightNew coefficient joint := by
  let entry := fun left right =>
    joint left right *
      ((coefficient left + -coefficient right) *
        (coefficient left + -coefficient right))
  unfold finiteJointDirichletBlock
  refine Q'.eqv_trans _
    (listQSum
      (fun left => listQSum (entry left) rightOld)
      leftNew) _ ?_ ?_
  · exact listQSum_perm_local _ hleft
  · apply listQSum_congr_on
    intro left _hleft
    exact listQSum_perm_local (entry left) hright

private theorem finiteJointDirichletBlock_map_eqv_local
    {Source Target : Type}
    (source : List Source) (map : Source → Target)
    (targetCoefficient : Target → Q')
    (sourceCoefficient : Source → Q')
    (targetJoint : Target → Target → Q')
    (sourceJoint : Source → Source → Q')
    (hentry : ∀ left, left ∈ source → ∀ right, right ∈ source →
      targetJoint (map left) (map right) *
          ((targetCoefficient (map left) + -targetCoefficient (map right)) *
            (targetCoefficient (map left) + -targetCoefficient (map right))) ≈
        sourceJoint left right *
          ((sourceCoefficient left + -sourceCoefficient right) *
            (sourceCoefficient left + -sourceCoefficient right))) :
    finiteJointDirichletBlock (source.map map) (source.map map)
        targetCoefficient targetJoint ≈
      finiteJointDirichletEnergy source sourceCoefficient sourceJoint := by
  unfold finiteJointDirichletBlock finiteJointDirichletEnergy
  rw [listQSum_map_local]
  apply listQSum_congr_on
  intro left hleft
  rw [listQSum_map_local]
  apply listQSum_congr_on
  intro right hright
  exact hentry left hleft right hright

/-- The later old-old stationary-product variance is exactly the pulled
cutoff-two pairwise variance of the restricted coefficient. -/
theorem cutoffTwoOldOldPairwiseVariance_eqv_pulled
    {later : Nat} (hlater : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoOldOldPairwiseVariance later coefficient ≈
      finiteWeightedPairwiseVariance
        cutoffTwoPulledStates (cutoffTwoPulledWeightAt later)
        (cutoffTwoOldCoefficientPullback later coefficient) := by
  let old := centralPhysicalFiniteVacuumSectorOldBlockIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let embedded := centralPhysicalFiniteEmbeddedVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let indexMap := centralPhysicalFiniteCutoffIndexMap
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let targetJoint := finiteStationaryProductJoint
    (centralPhysicalFiniteWeight cutoffTwoHalfCoupling (by decide) later 0)
  let sourceJoint := finiteStationaryProductJoint
    (cutoffTwoPulledWeightAt later)
  have hperm : old.Perm embedded :=
    centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded hlater
  unfold cutoffTwoOldOldPairwiseVariance finiteWeightedPairwiseVariance
  refine Q'.eqv_trans _
    (finiteJointDirichletBlock embedded embedded coefficient targetJoint) _ ?_ ?_
  · exact finiteJointDirichletBlock_perm_local hperm hperm _ _
  · unfold embedded centralPhysicalFiniteEmbeddedVacuumSectorIndices
    apply finiteJointDirichletBlock_map_eqv_local
    intro left _hleft right _hright
    unfold finiteStationaryProductJoint
      cutoffTwoPulledWeightAt centralPhysicalFinitePulledWeight
      cutoffTwoOldCoefficientPullback
    exact Q'.eqv_refl _

/-- The later old-old physical energy is exactly the pulled cutoff-two
Dirichlet energy of the restricted coefficient. -/
theorem cutoffTwoOldOldDirichlet_eqv_pulled
    {later : Nat} (hlater : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoOldOldDirichlet later coefficient ≈
      finiteJointDirichletEnergy cutoffTwoPulledStates
        (cutoffTwoOldCoefficientPullback later coefficient)
        (cutoffTwoPulledKernelAt later) := by
  let old := centralPhysicalFiniteVacuumSectorOldBlockIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let embedded := centralPhysicalFiniteEmbeddedVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let indexMap := centralPhysicalFiniteCutoffIndexMap
    cutoffTwoHalfCoupling (by decide) 2 later 0
  let targetJoint := centralPhysicalFiniteKernel
    cutoffTwoHalfCoupling (by decide) later 0
  let sourceJoint := cutoffTwoPulledKernelAt later
  have hperm : old.Perm embedded :=
    centralPhysicalFiniteVacuumSectorOldBlockIndices_perm_embedded hlater
  unfold cutoffTwoOldOldDirichlet
  refine Q'.eqv_trans _
    (finiteJointDirichletBlock embedded embedded coefficient targetJoint) _ ?_ ?_
  · exact finiteJointDirichletBlock_perm_local hperm hperm _ _
  · unfold embedded centralPhysicalFiniteEmbeddedVacuumSectorIndices
    apply finiteJointDirichletBlock_map_eqv_local
    intro left _hleft right _hright
    unfold cutoffTwoPulledKernelAt
      centralPhysicalFinitePulledKernel
      cutoffTwoOldCoefficientPullback
    exact Q'.eqv_refl _

/-- The old-old portion of every sufficiently late full sector has the same
explicit, strictly positive coercivity floor. -/
theorem cutoffTwoUniformOldBlockCoercivityFloor_mul_oldOldPairwise_le_Dirichlet
    (later : Nat)
    (hlater : cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later)
    (coefficient : Nat → Q') :
    cutoffTwoUniformOldBlockCoercivityFloor *
        cutoffTwoOldOldPairwiseVariance later coefficient ≤
      cutoffTwoOldOldDirichlet later coefficient := by
  have htwoLater : 2 ≤ later := Nat.le_trans
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two hlater
  have hpulled :=
    cutoffTwoUniformOldBlockCoercivityFloor_mul_pulledPairwise_le_Dirichlet
      later hlater (cutoffTwoOldCoefficientPullback later coefficient)
  have hpairwise :=
    cutoffTwoOldOldPairwiseVariance_eqv_pulled htwoLater coefficient
  have hdirichlet :=
    cutoffTwoOldOldDirichlet_eqv_pulled htwoLater coefficient
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv
      (Q'.mul_eqv_congr_left cutoffTwoUniformOldBlockCoercivityFloor
        _ _ hpairwise))
    (Q'.le_trans' _ _ _ hpulled (Q'.ge_of_eqv hdirichlet))

/-! ## 3. The strictly smaller new/new plus cross frontier -/

/-- After old-old coercivity and the sector-mass floor have been constructed,
only new-new and old/new-cross coercivity remain at one later cutoff. -/
structure CutoffTwoNewAndCrossCoercivityAt (later : Nat) : Type 1 where
  later_ge_pulled_floor :
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start ≤ later
  later_ge_mass_floor :
    cutoffTwoUniformVacuumSectorMassFloorAnchor ≤ later
  new_new_coercivity : ∀ coefficient,
    cutoffTwoUniformOldBlockCoercivityFloor *
        cutoffTwoNewNewPairwiseVariance later coefficient ≤
      cutoffTwoNewNewDirichlet later coefficient
  cross_coercivity : ∀ coefficient,
    cutoffTwoUniformOldBlockCoercivityFloor *
        cutoffTwoCrossBlockPairwiseVariance later coefficient ≤
      cutoffTwoCrossBlockDirichlet later coefficient

namespace CutoffTwoNewAndCrossCoercivityAt

/-- Insert the constructed old-old and mass bounds into the full two-block
gluing interface. -/
def toFullSectorDirichletGluingAt
    {later : Nat} (certificate : CutoffTwoNewAndCrossCoercivityAt later) :
    CutoffTwoFullSectorDirichletGluingAt later
      cutoffTwoUniformOldBlockCoercivityFloor
      cutoffTwoUniformVacuumSectorMassFloor where
  later_ge := Nat.le_trans
    cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
    certificate.later_ge_pulled_floor
  mass_floor_le := cutoffTwoUniformVacuumSectorMassFloor_le
    certificate.later_ge_mass_floor
  within_coercivity := by
    intro coefficient
    have hsum := Q'.add_le_add
      (cutoffTwoUniformOldBlockCoercivityFloor_mul_oldOldPairwise_le_Dirichlet
        later certificate.later_ge_pulled_floor coefficient)
      (certificate.new_new_coercivity coefficient)
    unfold cutoffTwoWithinBlockPairwiseVariance
      cutoffTwoWithinBlockDirichlet
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_add_eqv cutoffTwoUniformOldBlockCoercivityFloor _ _))
      hsum
  cross_coercivity := certificate.cross_coercivity

end CutoffTwoNewAndCrossCoercivityAt

/-- A constructively cofinal family of only the genuinely new and cross
coercivity estimates.  The old-old and mass fields are no longer inputs. -/
structure CutoffTwoCofinalNewAndCrossCoercivity : Type 1 where
  anchor : Nat → Nat
  anchor_ge : ∀ request,
    max
        (max cutoffTwoPulledUniformBasePositiveEdgeFloor.start
          cutoffTwoUniformVacuumSectorMassFloorAnchor)
        request ≤ anchor request
  residual : ∀ request, CutoffTwoNewAndCrossCoercivityAt (anchor request)

namespace CutoffTwoCofinalNewAndCrossCoercivity

def toCofinalFullSectorDirichletGluing
    (family : CutoffTwoCofinalNewAndCrossCoercivity) :
    CutoffTwoCofinalFullSectorDirichletGluing
      cutoffTwoUniformOldBlockCoercivityFloor
      cutoffTwoUniformVacuumSectorMassFloor where
  floor_pos := cutoffTwoUniformOldBlockCoercivityFloor_pos
  mass_floor_pos := cutoffTwoUniformVacuumSectorMassFloor_pos
  anchor := family.anchor
  anchor_ge := by
    intro request
    have hfamily := family.anchor_ge request
    have htwo := cutoffTwoPulledUniformBasePositiveEdgeFloor.start_ge_two
    omega
  gluing := by
    intro request
    exact (family.residual request).toFullSectorDirichletGluingAt

def toCompletedStrictContractionData
    (family : CutoffTwoCofinalNewAndCrossCoercivity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalFullSectorDirichletGluing
    |>.toCompletedStrictContractionData

end CutoffTwoCofinalNewAndCrossCoercivity

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.pulledFloor_mul_pairwiseVariance_le_ceiling_mul_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.cutoffTwoUniformOldBlockCoercivityFloor_pos
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.cutoffTwoUniformOldBlockCoercivityFloor_mul_pulledPairwise_le_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.cutoffTwoOldOldPairwiseVariance_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.cutoffTwoOldOldDirichlet_eqv_pulled
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.cutoffTwoUniformOldBlockCoercivityFloor_mul_oldOldPairwise_le_Dirichlet
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.CutoffTwoNewAndCrossCoercivityAt.toFullSectorDirichletGluingAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoUniformOldBlockCoercivity.CutoffTwoCofinalNewAndCrossCoercivity.toCompletedStrictContractionData
