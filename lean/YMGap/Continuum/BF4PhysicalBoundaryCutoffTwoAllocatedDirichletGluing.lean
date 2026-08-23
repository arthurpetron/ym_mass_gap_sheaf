/-
# Allocated two-block Dirichlet gluing

Sparse old/new support need not make the physical cross energy dominate the
entire stationary cross variance by itself.  A path from an arbitrary old
state to an arbitrary new state may first spend energy inside one or both
blocks before crossing a genuine bridge edge.

This module therefore weakens matched block coercivity to an allocated
certificate.  A common variance floor is split between:

* internal variance paid by a declared share of within-block energy; and
* cross variance paid by the complementary share of within-block energy plus
  all cross-block energy.

When the two shares add exactly to one, the estimates recombine to a global
Dirichlet coercivity inequality with no hidden loss.  A positive total-mass
floor then yields the same explicit strict rate and cofinal completed transfer
contraction as before.

No allocated certificate or cofinal family is inhabited here.  In particular
no uniform lattice gap, thermodynamic/continuum limit, or Clay conclusion is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoCrossMeanCoercivity

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletBlocks
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorGapPersistence
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap

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

/-! ## 1. Global coercivity is the minimal downstream interface -/

/-- One full stationary-product versus physical-kernel Dirichlet estimate,
plus the mass lower bound needed to convert centered pairwise variance into a
strict transfer rate. -/
structure CutoffTwoFullSectorDirichletCoercivityAt
    (later : Nat) (floor massFloor : Q') : Type 1 where
  later_ge : 2 ≤ later
  mass_floor_le :
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
  full_coercivity : ∀ coefficient,
    floor * cutoffTwoFullSectorPairwiseVariance later coefficient ≤
      cutoffTwoFullSectorDirichlet later coefficient

namespace CutoffTwoFullSectorDirichletCoercivityAt

private theorem ofNat_two_mul_eqv_local (value : Q') :
    Q'.ofNat 2 * value ≈ value + value := by
  show (Q'.ofNat 2 * value).num * ((value + value).den : Int) =
      (value + value).num * ((Q'.ofNat 2 * value).den : Int)
  have hn : (Q'.ofNat 2 * value).num = (2 : Int) * value.num := rfl
  have hd2 : ((Q'.ofNat 2 * value).den : Int) =
      (value.den : Int) := by
    show (((Q'.ofNat 2).den * value.den - 1 + 1 : Nat) : Int) =
      (value.den : Int)
    rw [show (Q'.ofNat 2).den = 1 from rfl, Nat.one_mul,
      Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.pos_iff_ne_zero.mp (Q'.den_pos value)))]
  have hxxn : (value + value).num =
      value.num * (value.den : Int) +
        value.num * (value.den : Int) := rfl
  have hxxd : ((value + value).den : Int) =
      (value.den : Int) * (value.den : Int) := by
    show (((value.den * value.den - 1) + 1 : Nat) : Int) =
      (value.den : Int) * (value.den : Int)
    rw [Nat.sub_add_cancel
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.pos_iff_ne_zero.mp
          (Nat.mul_pos (Q'.den_pos value) (Q'.den_pos value)))),
      Int.natCast_mul]
  rw [hn, hd2, hxxn, hxxd]
  rw [Int.add_mul, Int.two_mul, Int.add_mul]
  rw [Int.mul_assoc value.num (value.den : Int) (value.den : Int)]

private theorem twice_floor_mass_diagonal_eqv
    (floor mass diagonal : Q') :
    Q'.ofNat 2 * ((floor * mass) * diagonal) ≈
      floor * (mass * diagonal + mass * diagonal) := by
  refine Q'.eqv_trans _
    (((floor * mass) * diagonal) +
      ((floor * mass) * diagonal)) _
    (ofNat_two_mul_eqv_local ((floor * mass) * diagonal)) ?_
  q_ring

private theorem twice_deficit_eqv
    (diagonal matrix : Q') :
    (diagonal + diagonal) + -(matrix + matrix) ≈
      Q'.ofNat 2 * (diagonal + -matrix) := by
  refine Q'.eqv_trans _
    ((diagonal + -matrix) + (diagonal + -matrix)) _ ?_ ?_
  · q_ring
  · exact Q'.eqv_symm
      (ofNat_two_mul_eqv_local (diagonal + -matrix))

/-- Global Dirichlet coercivity and exact centering give the Poincare deficit
bound. -/
theorem strength_mul_diagonal_le_deficit
    {later : Nat} {floor massFloor : Q'}
    (certificate : CutoffTwoFullSectorDirichletCoercivityAt
      later floor massFloor)
    (hfloor : (0 : Q') ≤ floor)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    (floor * massFloor) * cutoffTwoFullSectorDiagonal later coefficient ≤
      cutoffTwoFullSectorDiagonal later coefficient +
        -cutoffTwoFullSectorMatrix later coefficient := by
  let mass := centralPhysicalFiniteVacuumSectorMass
    cutoffTwoHalfCoupling (by decide) later 0
  let diagonal := cutoffTwoFullSectorDiagonal later coefficient
  let matrix := cutoffTwoFullSectorMatrix later coefficient
  let pairwise := cutoffTwoFullSectorPairwiseVariance later coefficient
  let energy := cutoffTwoFullSectorDirichlet later coefficient
  have hdiagonal : (0 : Q') ≤ diagonal := by
    unfold diagonal cutoffTwoFullSectorDiagonal
    exact centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
      cutoffTwoHalfCoupling (by decide) later 0 coefficient
  have hmassTerm : massFloor * diagonal ≤ mass * diagonal :=
    Q'.mul_le_mul_of_nonneg_right _ _ diagonal
      certificate.mass_floor_le hdiagonal
  have hmassTwice :
      massFloor * diagonal + massFloor * diagonal ≤
        mass * diagonal + mass * diagonal :=
    Q'.add_le_add hmassTerm hmassTerm
  have hfloorMass :
      floor * (massFloor * diagonal + massFloor * diagonal) ≤
        floor * (mass * diagonal + mass * diagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ floor hmassTwice hfloor
  have hcenterPhysical :
      centralPhysicalFiniteVacuumSectorWeightedMean
        cutoffTwoHalfCoupling (by decide) later 0 coefficient ≈ 0 := by
    exact hcenter
  have hpairwise : pairwise ≈
      mass * diagonal + mass * diagonal := by
    unfold pairwise mass diagonal
      cutoffTwoFullSectorPairwiseVariance cutoffTwoFullSectorDiagonal
    exact centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
      cutoffTwoHalfCoupling (by decide) later 0 coefficient hcenterPhysical
  have hfloorPairwise :
      floor * (mass * diagonal + mass * diagonal) ≤ floor * pairwise :=
    Q'.le_of_eqv
      (Q'.mul_eqv_congr_left floor _ _ (Q'.eqv_symm hpairwise))
  have hglued :
      floor * (massFloor * diagonal + massFloor * diagonal) ≤ energy :=
    Q'.le_trans' _ _ _ hfloorMass
      (Q'.le_trans' _ _ _ hfloorPairwise
        (certificate.full_coercivity coefficient))
  have henergy : energy ≈
      (diagonal + diagonal) + -(matrix + matrix) := by
    unfold energy diagonal matrix
    exact cutoffTwoFullSectorDirichlet_eqv_twice_deficit later coefficient
  have htwice :
      Q'.ofNat 2 * ((floor * massFloor) * diagonal) ≤
        Q'.ofNat 2 * (diagonal + -matrix) :=
    Q'.le_trans' _
      (floor * (massFloor * diagonal + massFloor * diagonal)) _
      (Q'.le_of_eqv
        (twice_floor_mass_diagonal_eqv floor massFloor diagonal))
      (Q'.le_trans' _ energy _ hglued
        (Q'.le_trans' _
          ((diagonal + diagonal) + -(matrix + matrix)) _
          (Q'.le_of_eqv henergy)
          (Q'.le_of_eqv (twice_deficit_eqv diagonal matrix))))
  exact Q'.le_of_mul_le_mul_left htwice (Q'.ofNat_succ_pos 1)

private theorem denominator_mul_matrix_eqv
    (strength matrix : Q') :
    (1 + strength) * matrix ≈ strength * matrix + matrix := by
  q_ring

private theorem sub_add_cancel_eqv (diagonal matrix : Q') :
    (diagonal + -matrix) + matrix ≈ diagonal := by
  refine Q'.eqv_trans _
    (diagonal + (-matrix + matrix)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (diagonal + 0) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_self_eqv matrix)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem divPos_one_mul_right_eqv
    (diagonal denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos diagonal denominator hdenominator ≈
      Q'.divPos 1 denominator hdenominator * diagonal := by
  unfold Q'.divPos
  q_ring

/-- A positive global coercivity floor gives the explicit one-sided strict
rate already calibrated by the two-block gluing module. -/
theorem matrix_le_rate_mul_diagonal
    {later : Nat} {floor massFloor : Q'}
    (certificate : CutoffTwoFullSectorDirichletCoercivityAt
      later floor massFloor)
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    cutoffTwoFullSectorMatrix later coefficient ≤
      cutoffTwoDirichletGluingRate floor massFloor hfloor hmass *
        cutoffTwoFullSectorDiagonal later coefficient := by
  let strength := cutoffTwoDirichletGluingStrength floor massFloor
  let denominator := cutoffTwoDirichletGluingDenominator floor massFloor
  let diagonal := cutoffTwoFullSectorDiagonal later coefficient
  let matrix := cutoffTwoFullSectorMatrix later coefficient
  have hstrength0 : (0 : Q') ≤ strength :=
    Q'.le_of_lt (cutoffTwoDirichletGluingStrength_pos hfloor hmass)
  have hpoincare : strength * diagonal ≤ diagonal + -matrix := by
    unfold strength cutoffTwoDirichletGluingStrength diagonal matrix
    exact certificate.strength_mul_diagonal_le_deficit
      (Q'.le_of_lt hfloor) coefficient hcenter
  have hmatrixDiagonal : matrix ≤ diagonal := by
    unfold matrix diagonal cutoffTwoFullSectorMatrix
      cutoffTwoFullSectorDiagonal
    exact centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
      cutoffTwoHalfCoupling (by decide) later 0 coefficient
  have hstrengthMatrix : strength * matrix ≤ strength * diagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ strength
      hmatrixDiagonal hstrength0
  have hfirst : strength * matrix + matrix ≤
      strength * diagonal + matrix :=
    Q'.add_le_add_right _ _ matrix hstrengthMatrix
  have hpoincareAdded : strength * diagonal + matrix ≤
      (diagonal + -matrix) + matrix :=
    Q'.add_le_add_right _ _ matrix hpoincare
  have hsecond : strength * diagonal + matrix ≤ diagonal :=
    Q'.le_trans' _ _ _ hpoincareAdded
      (Q'.le_of_eqv (sub_add_cancel_eqv diagonal matrix))
  have hdenominatorMatrix : denominator * matrix ≤ diagonal := by
    unfold denominator cutoffTwoDirichletGluingDenominator
    exact Q'.le_trans' _ (strength * matrix + matrix) _
      (Q'.le_of_eqv (denominator_mul_matrix_eqv strength matrix))
      (Q'.le_trans' _ _ _ hfirst hsecond)
  have hcommuted : matrix * denominator ≤ diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv matrix denominator))
      hdenominatorMatrix
  have hdivision := Q'.le_divPos_of_mul_le diagonal denominator
    (cutoffTwoDirichletGluingDenominator_pos hfloor hmass) hcommuted
  exact Q'.le_trans' _ _ _ hdivision
    (Q'.le_of_eqv
      (Q'.eqv_trans _
        (Q'.divPos 1 denominator
          (cutoffTwoDirichletGluingDenominator_pos hfloor hmass) *
            diagonal) _
        (divPos_one_mul_right_eqv diagonal denominator
          (cutoffTwoDirichletGluingDenominator_pos hfloor hmass))
        (Q'.eqv_refl _)))

theorem abs_matrix_le_rate_mul_diagonal
    {later : Nat} {floor massFloor : Q'}
    (certificate : CutoffTwoFullSectorDirichletCoercivityAt
      later floor massFloor)
    (hfloor : (0 : Q') < floor) (hmass : (0 : Q') < massFloor)
    (coefficient : Nat → Q')
    (hcenter : cutoffTwoFullSectorWeightedMean later coefficient ≈ 0) :
    Q'.abs (cutoffTwoFullSectorMatrix later coefficient) ≤
      cutoffTwoDirichletGluingRate floor massFloor hfloor hmass *
        cutoffTwoFullSectorDiagonal later coefficient := by
  rw [abs_of_nonneg]
  · exact certificate.matrix_le_rate_mul_diagonal
      hfloor hmass coefficient hcenter
  · unfold cutoffTwoFullSectorMatrix
    exact centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      cutoffTwoHalfCoupling (by decide) later 0 coefficient

end CutoffTwoFullSectorDirichletCoercivityAt

/-! ## 2. Allocate within energy between internal and bridge paths -/

/-- Sparse-support gluing at one later cutoff.  The two energy shares are
explicit nonnegative rationals summing to one. -/
structure CutoffTwoAllocatedDirichletGluingAt
    (later : Nat) (floor massFloor withinShare crossShare : Q') : Type 1 where
  later_ge : 2 ≤ later
  within_share_nonnegative : (0 : Q') ≤ withinShare
  cross_share_nonnegative : (0 : Q') ≤ crossShare
  shares_sum_one : withinShare + crossShare ≈ 1
  mass_floor_le :
    massFloor ≤ centralPhysicalFiniteVacuumSectorMass
      cutoffTwoHalfCoupling (by decide) later 0
  within_budget : ∀ coefficient,
    floor * cutoffTwoWithinBlockPairwiseVariance later coefficient ≤
      withinShare * cutoffTwoWithinBlockDirichlet later coefficient
  cross_budget : ∀ coefficient,
    floor * cutoffTwoCrossBlockPairwiseVariance later coefficient ≤
      crossShare * cutoffTwoWithinBlockDirichlet later coefficient +
        cutoffTwoCrossBlockDirichlet later coefficient

namespace CutoffTwoAllocatedDirichletGluingAt

private theorem allocated_energy_eqv_full
    (withinEnergy crossEnergy withinShare crossShare : Q')
    (hshares : withinShare + crossShare ≈ 1) :
    withinShare * withinEnergy +
        (crossShare * withinEnergy + crossEnergy) ≈
      withinEnergy + crossEnergy := by
  refine Q'.eqv_trans _
    ((withinShare * withinEnergy + crossShare * withinEnergy) +
      crossEnergy) _
    (Q'.eqv_symm (Q'.add_assoc_eqv _ _ _)) ?_
  refine Q'.eqv_trans _
    ((withinShare + crossShare) * withinEnergy + crossEnergy) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ crossEnergy
      (Q'.eqv_symm
        (Q'.add_mul_eqv withinShare crossShare withinEnergy))
  refine Q'.eqv_trans _ (1 * withinEnergy + crossEnergy) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ crossEnergy
      (Q'.mul_eqv_congr_right _ _ withinEnergy hshares)
  · exact Q'.add_eqv_congr_right _ _ crossEnergy
      (Q'.one_mul_eqv withinEnergy)

/-- The allocated estimates recombine to the minimal global coercivity
interface. -/
def toFullSectorDirichletCoercivityAt
    {later : Nat} {floor massFloor withinShare crossShare : Q'}
    (certificate : CutoffTwoAllocatedDirichletGluingAt
      later floor massFloor withinShare crossShare) :
    CutoffTwoFullSectorDirichletCoercivityAt
      later floor massFloor where
  later_ge := certificate.later_ge
  mass_floor_le := certificate.mass_floor_le
  full_coercivity := by
    intro coefficient
    have hbudgets := Q'.add_le_add
      (certificate.within_budget coefficient)
      (certificate.cross_budget coefficient)
    refine Q'.le_trans' _
      (floor * cutoffTwoWithinBlockPairwiseVariance later coefficient +
        floor * cutoffTwoCrossBlockPairwiseVariance later coefficient) _ ?_ ?_
    · exact Q'.le_of_eqv
        (Q'.eqv_trans _
          (floor *
            (cutoffTwoWithinBlockPairwiseVariance later coefficient +
              cutoffTwoCrossBlockPairwiseVariance later coefficient)) _
          (Q'.mul_eqv_congr_left floor _ _
            (cutoffTwoFullSectorPairwiseVariance_eqv_within_add_cross
              later coefficient))
          (Q'.mul_add_eqv floor _ _))
    refine Q'.le_trans' _ _ _ hbudgets ?_
    refine Q'.le_trans' _
      (cutoffTwoWithinBlockDirichlet later coefficient +
        cutoffTwoCrossBlockDirichlet later coefficient) _ ?_ ?_
    · exact Q'.le_of_eqv
        (allocated_energy_eqv_full
          (cutoffTwoWithinBlockDirichlet later coefficient)
          (cutoffTwoCrossBlockDirichlet later coefficient)
          withinShare crossShare certificate.shares_sum_one)
    · exact Q'.ge_of_eqv
        (cutoffTwoFullSectorDirichlet_eqv_within_add_cross
          later coefficient)

end CutoffTwoAllocatedDirichletGluingAt

/-! ## 3. Cofinal allocated gluing reaches completion -/

structure CutoffTwoCofinalAllocatedDirichletGluing
    (floor massFloor withinShare crossShare : Q') : Type 1 where
  floor_pos : (0 : Q') < floor
  mass_floor_pos : (0 : Q') < massFloor
  anchor : Nat → Nat
  anchor_ge : ∀ request, max 2 request ≤ anchor request
  allocated : ∀ request,
    CutoffTwoAllocatedDirichletGluingAt
      (anchor request) floor massFloor withinShare crossShare

namespace CutoffTwoCofinalAllocatedDirichletGluing

def toFiniteStrictGap
    {floor massFloor withinShare crossShare : Q'}
    (family : CutoffTwoCofinalAllocatedDirichletGluing
      floor massFloor withinShare crossShare) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      cutoffTwoHalfCoupling (by decide) 0
      (cutoffTwoDirichletGluingRate
        floor massFloor family.floor_pos family.mass_floor_pos) where
  rate_nonnegative := cutoffTwoDirichletGluingRate_nonnegative
    family.floor_pos family.mass_floor_pos
  rate_lt_one := cutoffTwoDirichletGluingRate_lt_one
    family.floor_pos family.mass_floor_pos
  anchor := family.anchor
  anchor_ge := by
    intro request
    exact Nat.le_trans (Nat.le_max_right 2 request)
      (family.anchor_ge request)
  sectorGap := by
    intro request coefficient hcenter
    exact (family.allocated request).toFullSectorDirichletCoercivityAt
      |>.abs_matrix_le_rate_mul_diagonal
        family.floor_pos family.mass_floor_pos coefficient hcenter

def toCompletedStrictContractionData
    {floor massFloor withinShare crossShare : Q'}
    (family : CutoffTwoCofinalAllocatedDirichletGluing
      floor massFloor withinShare crossShare) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    (w := cutoffTwoHalfCoupling) (by decide) (by decide) 0
    family.toFiniteStrictGap

end CutoffTwoCofinalAllocatedDirichletGluing

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing.CutoffTwoFullSectorDirichletCoercivityAt.strength_mul_diagonal_le_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing.CutoffTwoFullSectorDirichletCoercivityAt.abs_matrix_le_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing.CutoffTwoAllocatedDirichletGluingAt.toFullSectorDirichletCoercivityAt
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing.CutoffTwoCofinalAllocatedDirichletGluing.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoAllocatedDirichletGluing.CutoffTwoCofinalAllocatedDirichletGluing.toCompletedStrictContractionData
