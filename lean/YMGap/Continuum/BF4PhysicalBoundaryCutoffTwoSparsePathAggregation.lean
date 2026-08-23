/-
# Sparse path aggregation across the cutoff-two boundary

The old/new support graph need not be complete bipartite.  Nevertheless every
old/new endpoint pair lies in the same finite physical vacuum component and
therefore has an explicit positive-kernel path.  This module sums the actual
canonical path energies over the two directed rectangular endpoint blocks.

The finite positive edge floor then proves that the stationary cross-block
pairwise variance is bounded by this canonical aggregate path budget.  A
separate congestion certificate may bound that aggregate by an allocated
share of within-block energy plus cross-block energy; this is exactly the
input needed by the allocated Dirichlet gluing compiler.

No uniform congestion certificate or cofinal family is inhabited here.  In
particular no uniform lattice gap, thermodynamic/continuum limit, or Clay
conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPositiveConnectivity
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "q_ring" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.add_zero, Int.zero_add];
             try ac_rfl))

/-! ## 1. Generic rectangular endpoint-budget summation -/

/-- Stationary pair weights applied to an arbitrary nonnegative endpoint
budget and summed over a directed rectangular block. -/
def finiteWeightedRectangularEndpointBudget {State : Type}
    (leftStates rightStates : List State)
    (weight : State → Q') (endpointBudget : State → State → Q') : Q' :=
  listQSum
    (fun left => listQSum
      (fun right =>
        (weight left * weight right) * endpointBudget left right)
      rightStates)
    leftStates

/-- Pointwise endpoint control sums without losing the actual rectangular
weights.  Unlike the older common-ceiling theorem, the right-hand side keeps
the selected endpoint budget and can therefore be analyzed by path
congestion rather than by multiplying one global energy by the number of
pairs. -/
theorem floor_mul_finiteStationaryRectangularVariance_le_endpointBudget
    {State : Type}
    (leftStates rightStates : List State)
    (weight coefficient : State → Q')
    (floor : Q') (endpointBudget : State → State → Q')
    (hleftWeight : ∀ state, state ∈ leftStates →
      (0 : Q') ≤ weight state)
    (hrightWeight : ∀ state, state ∈ rightStates →
      (0 : Q') ≤ weight state)
    (hendpoint : ∀ left, left ∈ leftStates →
      ∀ right, right ∈ rightStates →
        floor *
            ((coefficient left + -coefficient right) *
              (coefficient left + -coefficient right)) ≤
          endpointBudget left right) :
    floor * finiteJointDirichletBlock
        leftStates rightStates coefficient
        (finiteStationaryProductJoint weight) ≤
      finiteWeightedRectangularEndpointBudget
        leftStates rightStates weight endpointBudget := by
  let square : State → State → Q' := fun left right =>
    (coefficient left + -coefficient right) *
      (coefficient left + -coefficient right)
  let lowerSum := listQSum
    (fun left => listQSum
      (fun right =>
        (weight left * weight right) * (floor * square left right))
      rightStates)
    leftStates
  have hsums : lowerSum ≤
      finiteWeightedRectangularEndpointBudget
        leftStates rightStates weight endpointBudget := by
    unfold lowerSum finiteWeightedRectangularEndpointBudget
    apply listQSum_mono
    intro left hleft
    apply listQSum_mono
    intro right hright
    exact Q'.mul_le_mul_of_nonneg_left _ _ _
      (hendpoint left hleft right hright)
      (Q'.mul_nonneg _ _
        (hleftWeight left hleft) (hrightWeight right hright))
  have hlower : lowerSum ≈
      floor * finiteJointDirichletBlock
        leftStates rightStates coefficient
        (finiteStationaryProductJoint weight) := by
    unfold lowerSum finiteJointDirichletBlock
      finiteStationaryProductJoint square
    refine Q'.eqv_trans _
      (listQSum
        (fun left => floor *
          listQSum
            (fun right =>
              (weight left * weight right) *
                ((coefficient left + -coefficient right) *
                  (coefficient left + -coefficient right)))
            rightStates)
        leftStates) _ ?_ ?_
    · apply listQSum_congr
      intro left
      refine Q'.eqv_trans _
        (listQSum
          (fun right => floor *
            ((weight left * weight right) *
              ((coefficient left + -coefficient right) *
                (coefficient left + -coefficient right))))
          rightStates) _ ?_ ?_
      · apply listQSum_congr
        intro right
        q_ring
      · exact listQSum_mul_left floor _ rightStates
    · exact listQSum_mul_left floor _ leftStates
  exact Q'.le_trans' _ _ _
    (Q'.le_of_eqv (Q'.eqv_symm hlower)) hsums

/-! ## 2. Actual canonical path budgets on the physical old/new blocks -/

private def cutoffTwoFullStates (later : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorIndices
    cutoffTwoHalfCoupling (by decide) later 0

private def cutoffTwoOldStates (later : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorOldBlockIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0

private def cutoffTwoNewStates (later : Nat) : List Nat :=
  centralPhysicalFiniteVacuumSectorNewBlockIndices
    cutoffTwoHalfCoupling (by decide) 2 later 0

private def cutoffTwoWeight (later : Nat) : Nat → Q' :=
  centralPhysicalFiniteWeight
    cutoffTwoHalfCoupling (by decide) later 0

private def cutoffTwoKernel (later : Nat) : Nat → Nat → Q' :=
  centralPhysicalFiniteKernel
    cutoffTwoHalfCoupling (by decide) later 0

theorem cutoffTwoOldState_mem_full
    {later index : Nat} (hindex : index ∈ cutoffTwoOldStates later) :
    index ∈ cutoffTwoFullStates later := by
  exact (List.mem_filter.mp hindex).1

theorem cutoffTwoNewState_mem_full
    {later index : Nat} (hindex : index ∈ cutoffTwoNewStates later) :
    index ∈ cutoffTwoFullStates later := by
  exact (List.mem_filter.mp hindex).1

/-- Totalized energy of the actual canonical full-sector path.  Outside the
finite sector it is defined as zero; every application below supplies the
membership proofs and therefore selects the path branch. -/
def cutoffTwoCanonicalFullPathEnergy
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat) : Q' :=
  if hleft : left ∈ cutoffTwoFullStates later then
    if hright : right ∈ cutoffTwoFullStates later then
      PositiveKernelChainIn.amplifiedEnergy coefficient
        (centralPhysicalFiniteVacuumSectorPositivePath
          cutoffTwoHalfCoupling (by decide) later 0
          left right hleft hright)
    else 0
  else 0

def cutoffTwoOldNewCanonicalPathBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedRectangularEndpointBudget
    (cutoffTwoOldStates later) (cutoffTwoNewStates later)
    (cutoffTwoWeight later)
    (cutoffTwoCanonicalFullPathEnergy later coefficient)

def cutoffTwoNewOldCanonicalPathBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  finiteWeightedRectangularEndpointBudget
    (cutoffTwoNewStates later) (cutoffTwoOldStates later)
    (cutoffTwoWeight later)
    (cutoffTwoCanonicalFullPathEnergy later coefficient)

def cutoffTwoCanonicalCrossPathBudget
    (later : Nat) (coefficient : Nat → Q') : Q' :=
  cutoffTwoOldNewCanonicalPathBudget later coefficient +
    cutoffTwoNewOldCanonicalPathBudget later coefficient

private theorem cutoffTwoWeight_nonnegative
    (later state : Nat) : (0 : Q') ≤ cutoffTwoWeight later state := by
  unfold cutoffTwoWeight
  exact centralPhysicalRowMarginal_nonnegative
    (by decide) later 0
    (centralPhysicalFiniteStateAt
      cutoffTwoHalfCoupling (by decide) later 0 state)

private theorem cutoffTwo_edgeFloor_endpoint
    (later : Nat) (coefficient : Nat → Q')
    (left right : Nat)
    (hleft : left ∈ cutoffTwoFullStates later)
    (hright : right ∈ cutoffTwoFullStates later) :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        ((coefficient left + -coefficient right) *
          (coefficient left + -coefficient right)) ≤
      cutoffTwoCanonicalFullPathEnergy
        later coefficient left right := by
  unfold cutoffTwoCanonicalFullPathEnergy
  rw [dif_pos hleft, dif_pos hright]
  exact
    centralPhysicalFiniteVacuumSector_edgeFloor_mul_endpoint_sq_le_pathEnergy
      cutoffTwoHalfCoupling (by decide) later 0 coefficient
      left right hleft hright

theorem cutoffTwo_edgeFloor_mul_oldNewVariance_le_pathBudget
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoOldNewPairwiseVariance later coefficient ≤
      cutoffTwoOldNewCanonicalPathBudget later coefficient := by
  unfold cutoffTwoOldNewPairwiseVariance
    cutoffTwoOldNewCanonicalPathBudget
  exact floor_mul_finiteStationaryRectangularVariance_le_endpointBudget
    (cutoffTwoOldStates later) (cutoffTwoNewStates later)
    (cutoffTwoWeight later) coefficient
    (centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0)
    (cutoffTwoCanonicalFullPathEnergy later coefficient)
    (fun state _ => cutoffTwoWeight_nonnegative later state)
    (fun state _ => cutoffTwoWeight_nonnegative later state)
    (fun left hleft right hright =>
      cutoffTwo_edgeFloor_endpoint later coefficient left right
        (cutoffTwoOldState_mem_full hleft)
        (cutoffTwoNewState_mem_full hright))

theorem cutoffTwo_edgeFloor_mul_newOldVariance_le_pathBudget
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoNewOldPairwiseVariance later coefficient ≤
      cutoffTwoNewOldCanonicalPathBudget later coefficient := by
  unfold cutoffTwoNewOldPairwiseVariance
    cutoffTwoNewOldCanonicalPathBudget
  exact floor_mul_finiteStationaryRectangularVariance_le_endpointBudget
    (cutoffTwoNewStates later) (cutoffTwoOldStates later)
    (cutoffTwoWeight later) coefficient
    (centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0)
    (cutoffTwoCanonicalFullPathEnergy later coefficient)
    (fun state _ => cutoffTwoWeight_nonnegative later state)
    (fun state _ => cutoffTwoWeight_nonnegative later state)
    (fun left hleft right hright =>
      cutoffTwo_edgeFloor_endpoint later coefficient left right
        (cutoffTwoNewState_mem_full hleft)
        (cutoffTwoOldState_mem_full hright))

/-- The two actual directed canonical path families control the complete
cross-block stationary pairwise variance. -/
theorem cutoffTwo_edgeFloor_mul_crossVariance_le_canonicalPathBudget
    (later : Nat) (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoCrossBlockPairwiseVariance later coefficient ≤
      cutoffTwoCanonicalCrossPathBudget later coefficient := by
  have hsum := Q'.add_le_add
    (cutoffTwo_edgeFloor_mul_oldNewVariance_le_pathBudget later coefficient)
    (cutoffTwo_edgeFloor_mul_newOldVariance_le_pathBudget later coefficient)
  refine Q'.le_trans' _
    (centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoOldNewPairwiseVariance later coefficient +
      centralPhysicalFiniteVacuumSectorEdgeFloor
          cutoffTwoHalfCoupling (by decide) later 0 *
        cutoffTwoNewOldPairwiseVariance later coefficient) _ ?_ ?_
  · exact Q'.le_of_eqv
      (Q'.mul_add_eqv _ _ _)
  · exact hsum

/-! ## 3. Congestion certificates compile to allocated gluing -/

/-- The remaining sparse analytic input at one cutoff.  All paths and their
edge floor are canonical; the certificate only has to control their aggregate
congestion by the declared energy allocation. -/
structure CutoffTwoSparsePathAllocatedGluingAt
    (later : Nat) (floor massFloor withinShare crossShare : Q') : Type 1 where
  later_ge : 2 ≤ later
  floor_nonnegative : (0 : Q') ≤ floor
  within_share_nonnegative : (0 : Q') ≤ withinShare
  cross_share_nonnegative : (0 : Q') ≤ crossShare
  shares_sum_one : withinShare + crossShare ≈ 1
  floor_le_edgeFloor :
    floor ≤ centralPhysicalFiniteVacuumSectorEdgeFloor
      cutoffTwoHalfCoupling (by decide) later 0
  mass_floor_le :
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
  within_budget : ∀ coefficient,
    floor * cutoffTwoWithinBlockPairwiseVariance later coefficient ≤
      withinShare * cutoffTwoWithinBlockDirichlet later coefficient
  cross_path_congestion : ∀ coefficient,
    cutoffTwoCanonicalCrossPathBudget later coefficient ≤
      crossShare * cutoffTwoWithinBlockDirichlet later coefficient +
        cutoffTwoCrossBlockDirichlet later coefficient

namespace CutoffTwoSparsePathAllocatedGluingAt

/-- Actual canonical path aggregation discharges the cross budget of the
allocated gluing interface. -/
def toAllocatedDirichletGluingAt
    {later : Nat} {floor massFloor withinShare crossShare : Q'}
    (certificate : CutoffTwoSparsePathAllocatedGluingAt
      later floor massFloor withinShare crossShare) :
    CutoffTwoAllocatedDirichletGluingAt
      later floor massFloor withinShare crossShare where
  later_ge := certificate.later_ge
  within_share_nonnegative := certificate.within_share_nonnegative
  cross_share_nonnegative := certificate.cross_share_nonnegative
  shares_sum_one := certificate.shares_sum_one
  mass_floor_le := certificate.mass_floor_le
  within_budget := certificate.within_budget
  cross_budget := by
    intro coefficient
    have hvariance0 : (0 : Q') ≤
        cutoffTwoCrossBlockPairwiseVariance later coefficient :=
      cutoffTwoCrossBlockPairwiseVariance_nonnegative later coefficient
    have hfloorScale :
        floor * cutoffTwoCrossBlockPairwiseVariance later coefficient ≤
          centralPhysicalFiniteVacuumSectorEdgeFloor
              cutoffTwoHalfCoupling (by decide) later 0 *
            cutoffTwoCrossBlockPairwiseVariance later coefficient :=
      Q'.mul_le_mul_of_nonneg_right _ _ _
        certificate.floor_le_edgeFloor hvariance0
    exact Q'.le_trans' _ _ _ hfloorScale
      (Q'.le_trans' _ _ _
        (cutoffTwo_edgeFloor_mul_crossVariance_le_canonicalPathBudget
          later coefficient)
        (certificate.cross_path_congestion coefficient))

end CutoffTwoSparsePathAllocatedGluingAt

/-- A cofinal uniform sparse-path family.  Its only extra content relative to
the allocated compiler is the explicit canonical-path congestion bound. -/
structure CutoffTwoCofinalSparsePathAllocatedGluing
    (floor massFloor withinShare crossShare : Q') : Type 1 where
  floor_pos : (0 : Q') < floor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  sparse : ∀ request,
    CutoffTwoSparsePathAllocatedGluingAt
      (anchor request) floor massFloor withinShare crossShare

namespace CutoffTwoCofinalSparsePathAllocatedGluing

def toCofinalAllocatedDirichletGluing
    {floor massFloor withinShare crossShare : Q'}
    (family : CutoffTwoCofinalSparsePathAllocatedGluing
      floor massFloor withinShare crossShare) :
    CutoffTwoCofinalAllocatedDirichletGluing
      floor massFloor withinShare crossShare where
  floor_pos := family.floor_pos
  mass_floor_pos := family.mass_floor_pos
  anchor := family.anchor
  anchor_ge := family.anchor_ge
  allocated := fun request =>
    (family.sparse request).toAllocatedDirichletGluingAt

def toCompletedStrictContractionData
    {floor massFloor withinShare crossShare : Q'}
    (family : CutoffTwoCofinalSparsePathAllocatedGluing
      floor massFloor withinShare crossShare) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  family.toCofinalAllocatedDirichletGluing
    |>.toCompletedStrictContractionData

end CutoffTwoCofinalSparsePathAllocatedGluing

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.floor_mul_finiteStationaryRectangularVariance_le_endpointBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.cutoffTwo_edgeFloor_mul_oldNewVariance_le_pathBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.cutoffTwo_edgeFloor_mul_newOldVariance_le_pathBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.cutoffTwo_edgeFloor_mul_crossVariance_le_canonicalPathBudget
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.CutoffTwoSparsePathAllocatedGluingAt.toAllocatedDirichletGluingAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoSparsePathAggregation.CutoffTwoCofinalSparsePathAllocatedGluing.toCompletedStrictContractionData
