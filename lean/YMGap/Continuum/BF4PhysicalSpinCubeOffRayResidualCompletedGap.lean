/-
# Local spin-ray/off-ray capacity compiles to the completed BF4 gap

The global minimum-edge root-linear ratio is not cofinal at half-extent zero.
The viable replacement is the already isolated local route: a cutoff-uniform
spin-ray capacity together with pointwise capacity for the explicit off-ray
residual flow.  That pair gives one cutoff-independent full-sector pairwise
Dirichlet coercivity floor without a global edge minimum.

This module carries that local coercivity through exact centering, the
constructed fixed-nome sector-mass floor, finite Gram positivity, and the
existing completion map.  It produces the actual completed vacuum-sector
strict-contraction datum from either the cofinal residual-coercivity interface
or its stronger pointwise-flow-capacity producer.

No cofinal off-ray residual capacity is inhabited here.  No thermodynamic or
continuum limit, continuum Yang--Mills theory, or Clay conclusion is asserted.
No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing

namespace YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorLocalUpperPSDCofinalBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorCylinderCompletedGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFlowCapacity
open YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualFrontier
open YMGap.Continuum.BF4PhysicalSpinCubeRayCofinalReturnFloor

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

private theorem twice_floor_mass_diagonal_eqv_local
    (floor mass diagonal : Q') :
    Q'.ofNat 2 * ((floor * mass) * diagonal) ≈
      floor * (mass * diagonal + mass * diagonal) := by
  refine Q'.eqv_trans _
    (((floor * mass) * diagonal) +
      ((floor * mass) * diagonal)) _
    (ofNat_two_mul_eqv_local ((floor * mass) * diagonal)) ?_
  q_ring

private theorem twice_deficit_eqv_local
    (diagonal matrix : Q') :
    (diagonal + diagonal) + -(matrix + matrix) ≈
      Q'.ofNat 2 * (diagonal + -matrix) := by
  refine Q'.eqv_trans _
    ((diagonal + -matrix) + (diagonal + -matrix)) _ ?_ ?_
  · q_ring
  · exact Q'.eqv_symm
      (ofNat_two_mul_eqv_local (diagonal + -matrix))

private theorem denominator_mul_matrix_eqv_local
    (strength matrix : Q') :
    (1 + strength) * matrix ≈ strength * matrix + matrix := by
  q_ring

private theorem sub_add_cancel_eqv_local (diagonal matrix : Q') :
    (diagonal + -matrix) + matrix ≈ diagonal := by
  refine Q'.eqv_trans _
    (diagonal + (-matrix + matrix)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _ (diagonal + 0) _
    (Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_self_eqv matrix)) ?_
  exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem divPos_one_mul_right_eqv_local
    (diagonal denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos diagonal denominator hdenominator ≈
      Q'.divPos 1 denominator hdenominator * diagonal := by
  unfold Q'.divPos
  q_ring

/-! ## 1. Generic pairwise coercivity gives a strict centered form -/

/-- Exact centering converts any positive full pairwise Dirichlet coercivity
floor and a sector-mass lower bound into the transfer-deficit estimate. -/
theorem pairwiseCoercivity_strength_mul_diagonal_le_deficit
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    {coercivityFloor massFloor : Q'}
    (hcoercivityFloor : (0 : Q') < coercivityFloor)
    (hmassFloor : massFloor ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) K half)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w (Q'.le_of_lt hw) K half coefficient ≈ 0)
    (hcoercivity :
      coercivityFloor *
          centralPhysicalFiniteVacuumSectorPairwiseVariance
            w (Q'.le_of_lt hw) K half coefficient ≤
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K half)
          coefficient
          (centralPhysicalFiniteKernel
            w (Q'.le_of_lt hw) K half)) :
    (coercivityFloor * massFloor) *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw) K half coefficient ≤
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw) K half coefficient +
        -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw) K half coefficient) := by
  let mass := centralPhysicalFiniteVacuumSectorMass
    w (Q'.le_of_lt hw) K half
  let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w (Q'.le_of_lt hw) K half coefficient
  let matrix := centralPhysicalFiniteVacuumSectorMatrixQuadratic
    w (Q'.le_of_lt hw) K half coefficient
  let pairwise := centralPhysicalFiniteVacuumSectorPairwiseVariance
    w (Q'.le_of_lt hw) K half coefficient
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices
      w (Q'.le_of_lt hw) K half)
    coefficient
    (centralPhysicalFiniteKernel w (Q'.le_of_lt hw) K half)
  have hdiagonal : (0 : Q') ≤ diagonal := by
    unfold diagonal
    exact centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
      w (Q'.le_of_lt hw) K half coefficient
  have hmassTerm : massFloor * diagonal ≤ mass * diagonal :=
    Q'.mul_le_mul_of_nonneg_right _ _ diagonal hmassFloor hdiagonal
  have hmassTwice :
      massFloor * diagonal + massFloor * diagonal ≤
        mass * diagonal + mass * diagonal :=
    Q'.add_le_add hmassTerm hmassTerm
  have hfloorMass :
      coercivityFloor *
          (massFloor * diagonal + massFloor * diagonal) ≤
        coercivityFloor * (mass * diagonal + mass * diagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ coercivityFloor hmassTwice
      (Q'.le_of_lt hcoercivityFloor)
  have hpairwise : pairwise ≈
      mass * diagonal + mass * diagonal := by
    unfold pairwise mass diagonal
    exact centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
      w (Q'.le_of_lt hw) K half coefficient hcenter
  have hfloorPairwise :
      coercivityFloor * (mass * diagonal + mass * diagonal) ≤
        coercivityFloor * pairwise :=
    Q'.le_of_eqv
      (Q'.mul_eqv_congr_left coercivityFloor _ _
        (Q'.eqv_symm hpairwise))
  have hglued :
      coercivityFloor *
          (massFloor * diagonal + massFloor * diagonal) ≤ energy :=
    Q'.le_trans' _ _ _ hfloorMass
      (Q'.le_trans' _ _ _ hfloorPairwise hcoercivity)
  have henergy : energy ≈
      (diagonal + diagonal) + -(matrix + matrix) := by
    unfold energy diagonal matrix
    exact centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
      w (Q'.le_of_lt hw) K half coefficient
  have htwice :
      Q'.ofNat 2 * ((coercivityFloor * massFloor) * diagonal) ≤
        Q'.ofNat 2 * (diagonal + -matrix) :=
    Q'.le_trans' _
      (coercivityFloor *
        (massFloor * diagonal + massFloor * diagonal)) _
      (Q'.le_of_eqv
        (twice_floor_mass_diagonal_eqv_local
          coercivityFloor massFloor diagonal))
      (Q'.le_trans' _ energy _ hglued
        (Q'.le_trans' _
          ((diagonal + diagonal) + -(matrix + matrix)) _
          (Q'.le_of_eqv henergy)
          (Q'.le_of_eqv
            (twice_deficit_eqv_local diagonal matrix))))
  exact Q'.le_of_mul_le_mul_left htwice (Q'.ofNat_succ_pos 1)

/-- The generic finite coercivity inputs give the same explicit strict
rational form rate used by the completed-sector compiler. -/
theorem pairwiseCoercivity_abs_matrix_le_rate_mul_diagonal
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    {coercivityFloor massFloor : Q'}
    (hcoercivityFloor : (0 : Q') < coercivityFloor)
    (hmassPos : (0 : Q') < massFloor)
    (hmassFloor : massFloor ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) K half)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w (Q'.le_of_lt hw) K half coefficient ≈ 0)
    (hcoercivity :
      coercivityFloor *
          centralPhysicalFiniteVacuumSectorPairwiseVariance
            w (Q'.le_of_lt hw) K half coefficient ≤
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices
            w (Q'.le_of_lt hw) K half)
          coefficient
          (centralPhysicalFiniteKernel
            w (Q'.le_of_lt hw) K half)) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw) K half coefficient) ≤
      cutoffTwoDirichletGluingRate
          coercivityFloor massFloor hcoercivityFloor hmassPos *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw) K half coefficient := by
  let strength := cutoffTwoDirichletGluingStrength
    coercivityFloor massFloor
  let denominator := cutoffTwoDirichletGluingDenominator
    coercivityFloor massFloor
  let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w (Q'.le_of_lt hw) K half coefficient
  let matrix := centralPhysicalFiniteVacuumSectorMatrixQuadratic
    w (Q'.le_of_lt hw) K half coefficient
  have hstrength0 : (0 : Q') ≤ strength :=
    Q'.le_of_lt
      (cutoffTwoDirichletGluingStrength_pos hcoercivityFloor hmassPos)
  have hpoincare : strength * diagonal ≤ diagonal + -matrix := by
    unfold strength cutoffTwoDirichletGluingStrength diagonal matrix
    exact pairwiseCoercivity_strength_mul_diagonal_le_deficit
      (hw := hw)
      hcoercivityFloor hmassFloor coefficient hcenter hcoercivity
  have hmatrixDiagonal : matrix ≤ diagonal := by
    unfold matrix diagonal
    exact centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
      w (Q'.le_of_lt hw) K half coefficient
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
      (Q'.le_of_eqv (sub_add_cancel_eqv_local diagonal matrix))
  have hdenominatorMatrix : denominator * matrix ≤ diagonal := by
    unfold denominator cutoffTwoDirichletGluingDenominator
    exact Q'.le_trans' _ (strength * matrix + matrix) _
      (Q'.le_of_eqv
        (denominator_mul_matrix_eqv_local strength matrix))
      (Q'.le_trans' _ _ _ hfirst hsecond)
  have hcommuted : matrix * denominator ≤ diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv matrix denominator))
      hdenominatorMatrix
  have hdivision := Q'.le_divPos_of_mul_le diagonal denominator
    (cutoffTwoDirichletGluingDenominator_pos
      hcoercivityFloor hmassPos) hcommuted
  have hmatrixRate : matrix ≤
      cutoffTwoDirichletGluingRate
          coercivityFloor massFloor hcoercivityFloor hmassPos *
        diagonal :=
    Q'.le_trans' _ _ _ hdivision
      (Q'.le_of_eqv
        (Q'.eqv_trans _
          (Q'.divPos 1 denominator
            (cutoffTwoDirichletGluingDenominator_pos
              hcoercivityFloor hmassPos) * diagonal) _
          (divPos_one_mul_right_eqv_local diagonal denominator
            (cutoffTwoDirichletGluingDenominator_pos
              hcoercivityFloor hmassPos))
          (Q'.eqv_refl _)))
  rw [abs_of_nonneg]
  · exact hmatrixRate
  · exact centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w (Q'.le_of_lt hw) K half coefficient

/-! ## 2. Cofinal local residual coercivity reaches completion -/

namespace FixedNomeCofinalSpinCubeOffRayResidualCoercivity

/-- Cofinal local spin-ray/off-ray coercivity, together with the constructed
uniform mass floor, gives the direct finite strict-gap family. -/
def toFiniteStrictGap
    {w : Q'} (hw1 : w < (1 : Q')) {hw0 : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualCoercivity
        hw0 rayCapacity) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      w (Q'.le_of_lt hw0) 0
      (cutoffTwoDirichletGluingRate
        (HalfPow.half * rayCapacity.delta)
        (centralPhysicalFiniteVacuumSectorUniformMassFloor
          w (Q'.le_of_lt hw0) 0)
        family.sharedFloor_pos
        (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
          w (Q'.le_of_lt hw0) 0)) where
  rate_nonnegative := cutoffTwoDirichletGluingRate_nonnegative
    family.sharedFloor_pos
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
      w (Q'.le_of_lt hw0) 0)
  rate_lt_one := cutoffTwoDirichletGluingRate_lt_one
    family.sharedFloor_pos
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
      w (Q'.le_of_lt hw0) 0)
  anchor := fun request => max request
    (max rayCapacity.start
      (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w 0))
  anchor_ge := fun request => Nat.le_max_left _ _
  sectorGap := by
    intro request coefficient hcenter
    let K := max request
      (max rayCapacity.start
        (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w 0))
    have hstart : rayCapacity.start ≤ K :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_max_right request _)
    have hmassAnchor :
        centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w 0 ≤ K :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right request _)
    exact pairwiseCoercivity_abs_matrix_le_rate_mul_diagonal
      (hw := hw0)
      family.sharedFloor_pos
      (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
        w (Q'.le_of_lt hw0) 0)
      (centralPhysicalFiniteVacuumSectorUniformMassFloor_le
        hw0 hw1 0 hmassAnchor)
      coefficient hcenter
      (family.sharedFloor_mul_fullPairwiseVariance_le_physicalDirichlet
        hstart coefficient)

/-- The viable local residual-coercivity input reaches the actual completed
vacuum-sector strict contraction. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualCoercivity
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    hw0 hw1 0
      (YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toFiniteStrictGap
        hw1 family)

end FixedNomeCofinalSpinCubeOffRayResidualCoercivity

/-! ## 3. The pointwise flow-capacity producer reaches the same target -/

namespace FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity

def toFiniteStrictGap
    {w : Q'} (hw1 : w < (1 : Q')) {hw0 : (0 : Q') < w}
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity
        hw0 rayCapacity) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      w (Q'.le_of_lt hw0) 0
      (cutoffTwoDirichletGluingRate
        (HalfPow.half * rayCapacity.delta)
        (centralPhysicalFiniteVacuumSectorUniformMassFloor
          w (Q'.le_of_lt hw0) 0)
        family.toCofinalResidualCoercivity.sharedFloor_pos
        (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
          w (Q'.le_of_lt hw0) 0)) :=
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toFiniteStrictGap
    hw1 family.toCofinalResidualCoercivity

def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    {rayCapacity : FixedNomeCofinalSpinCubeRayCapacity hw0}
    (family :
      FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity
        hw0 rayCapacity) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 0 :=
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toCompletedStrictContractionData
    hw0 hw1 family.toCofinalResidualCoercivity

end FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity

end YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.pairwiseCoercivity_strength_mul_diagonal_le_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.pairwiseCoercivity_abs_matrix_le_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualCoercivity.toCompletedStrictContractionData
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalSpinCubeOffRayResidualCompletedGap.FixedNomeCofinalSpinCubeOffRayResidualFlowCapacity.toCompletedStrictContractionData
