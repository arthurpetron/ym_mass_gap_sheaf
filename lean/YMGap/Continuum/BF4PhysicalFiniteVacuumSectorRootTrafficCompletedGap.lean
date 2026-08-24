/-
# Uniform root traffic and sector mass compile to the completed BF4 gap

The rooted flow reduces full pairwise variance of one finite physical
observable to a coefficient-independent local traffic.  A cofinal root-traffic
capacity therefore supplies one uniform positive Dirichlet coercivity floor.
The separately constructed fixed-nome sector-mass floor converts that
coercivity into a strict centered transfer rate.

This module performs the exact algebraic join.  It constructs the existing
cofinal finite strict-gap interface and hence the actual completed
vacuum-sector strict-contraction datum from one named analytic input:
`FixedNomeCofinalVacuumRootTrafficCapacity`.

No inhabitant of that cofinal capacity is constructed here.  No
thermodynamic/continuum limit, continuum QFT, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor
import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoFullSectorDirichletGluing

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap

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
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCapacity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorUniformMassFloor

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

/-! ## 1. One local capacity plus one mass floor give a strict finite form -/

/-- Exact centering converts root-traffic coercivity and a sector-mass floor
into a Poincare deficit estimate. -/
theorem rootTraffic_strength_mul_diagonal_le_deficit
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity : CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt
      hw K half)
    {massFloor : Q'}
    (hmassFloor : massFloor ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) K half)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w (Q'.le_of_lt hw) K half coefficient ≈ 0) :
    (capacity.delta * massFloor) *
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
      capacity.delta *
          (massFloor * diagonal + massFloor * diagonal) ≤
        capacity.delta * (mass * diagonal + mass * diagonal) :=
    Q'.mul_le_mul_of_nonneg_left _ _ capacity.delta hmassTwice
      (Q'.le_of_lt capacity.delta_pos)
  have hpairwise : pairwise ≈
      mass * diagonal + mass * diagonal := by
    unfold pairwise mass diagonal
    exact centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
      w (Q'.le_of_lt hw) K half coefficient hcenter
  have hfloorPairwise :
      capacity.delta * (mass * diagonal + mass * diagonal) ≤
        capacity.delta * pairwise :=
    Q'.le_of_eqv
      (Q'.mul_eqv_congr_left capacity.delta _ _
        (Q'.eqv_symm hpairwise))
  have hcoercivity : capacity.delta * pairwise ≤ energy := by
    unfold pairwise energy
    exact capacity.delta_mul_pairwiseVariance_le_physicalDirichlet coefficient
  have hglued :
      capacity.delta *
          (massFloor * diagonal + massFloor * diagonal) ≤ energy :=
    Q'.le_trans' _ _ _ hfloorMass
      (Q'.le_trans' _ _ _ hfloorPairwise hcoercivity)
  have henergy : energy ≈
      (diagonal + diagonal) + -(matrix + matrix) := by
    unfold energy diagonal matrix
    exact centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
      w (Q'.le_of_lt hw) K half coefficient
  have htwice :
      Q'.ofNat 2 * ((capacity.delta * massFloor) * diagonal) ≤
        Q'.ofNat 2 * (diagonal + -matrix) :=
    Q'.le_trans' _
      (capacity.delta *
        (massFloor * diagonal + massFloor * diagonal)) _
      (Q'.le_of_eqv
        (twice_floor_mass_diagonal_eqv
          capacity.delta massFloor diagonal))
      (Q'.le_trans' _ energy _ hglued
        (Q'.le_trans' _
          ((diagonal + diagonal) + -(matrix + matrix)) _
          (Q'.le_of_eqv henergy)
          (Q'.le_of_eqv (twice_deficit_eqv diagonal matrix))))
  exact Q'.le_of_mul_le_mul_left htwice (Q'.ofNat_succ_pos 1)

/-- The same finite inputs give the explicit strict rational rate already used
by the completed-sector compiler. -/
theorem rootTraffic_abs_matrix_le_rate_mul_diagonal
    {w : Q'} {hw : (0 : Q') < w} {K half : Nat}
    (capacity : CentralPhysicalFiniteVacuumSectorRootTrafficCapacityAt
      hw K half)
    {massFloor : Q'} (hmassPos : (0 : Q') < massFloor)
    (hmassFloor : massFloor ≤
      centralPhysicalFiniteVacuumSectorMass
        w (Q'.le_of_lt hw) K half)
    (coefficient : Nat → Q')
    (hcenter : centralPhysicalFiniteVacuumSectorWeightedMean
      w (Q'.le_of_lt hw) K half coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w (Q'.le_of_lt hw) K half coefficient) ≤
      cutoffTwoDirichletGluingRate
          capacity.delta massFloor capacity.delta_pos hmassPos *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w (Q'.le_of_lt hw) K half coefficient := by
  let strength := cutoffTwoDirichletGluingStrength
    capacity.delta massFloor
  let denominator := cutoffTwoDirichletGluingDenominator
    capacity.delta massFloor
  let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w (Q'.le_of_lt hw) K half coefficient
  let matrix := centralPhysicalFiniteVacuumSectorMatrixQuadratic
    w (Q'.le_of_lt hw) K half coefficient
  have hstrength0 : (0 : Q') ≤ strength :=
    Q'.le_of_lt
      (cutoffTwoDirichletGluingStrength_pos capacity.delta_pos hmassPos)
  have hpoincare : strength * diagonal ≤ diagonal + -matrix := by
    unfold strength cutoffTwoDirichletGluingStrength diagonal matrix
    exact rootTraffic_strength_mul_diagonal_le_deficit
      capacity hmassFloor coefficient hcenter
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
    (cutoffTwoDirichletGluingDenominator_pos
      capacity.delta_pos hmassPos) hcommuted
  have hmatrixRate : matrix ≤
      cutoffTwoDirichletGluingRate
          capacity.delta massFloor capacity.delta_pos hmassPos *
        diagonal :=
    Q'.le_trans' _ _ _ hdivision
      (Q'.le_of_eqv
        (Q'.eqv_trans _
          (Q'.divPos 1 denominator
            (cutoffTwoDirichletGluingDenominator_pos
              capacity.delta_pos hmassPos) * diagonal) _
          (divPos_one_mul_right_eqv diagonal denominator
            (cutoffTwoDirichletGluingDenominator_pos
              capacity.delta_pos hmassPos))
          (Q'.eqv_refl _)))
  rw [abs_of_nonneg]
  · exact hmatrixRate
  · exact centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w (Q'.le_of_lt hw) K half coefficient

/-! ## 2. The cofinal root capacity reaches the completed transfer -/

namespace FixedNomeCofinalVacuumRootTrafficCapacity

/-- One common root-traffic capacity, together with the already constructed
fixed-nome sector-mass floor, produces the direct cofinal finite strict gap. -/
def toFiniteStrictGap
    {w : Q'} (hw1 : w < (1 : Q')) {hw0 : (0 : Q') < w}
    {half : Nat}
    (family : FixedNomeCofinalVacuumRootTrafficCapacity hw0 half) :
    FixedNomeCofinalVacuumSectorFiniteStrictGap
      w (Q'.le_of_lt hw0) half
      (cutoffTwoDirichletGluingRate
        family.delta
        (centralPhysicalFiniteVacuumSectorUniformMassFloor
          w (Q'.le_of_lt hw0) half)
        family.delta_pos
        (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
          w (Q'.le_of_lt hw0) half)) where
  rate_nonnegative := cutoffTwoDirichletGluingRate_nonnegative
    family.delta_pos
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
      w (Q'.le_of_lt hw0) half)
  rate_lt_one := cutoffTwoDirichletGluingRate_lt_one
    family.delta_pos
    (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
      w (Q'.le_of_lt hw0) half)
  anchor := fun request => max request
    (max family.start
      (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w half))
  anchor_ge := fun request => Nat.le_max_left _ _
  sectorGap := by
    intro request coefficient hcenter
    let K := max request
      (max family.start
        (centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w half))
    have hstart : family.start ≤ K :=
      Nat.le_trans (Nat.le_max_left _ _)
        (Nat.le_max_right request _)
    have hmassAnchor :
        centralPhysicalFiniteVacuumSectorUniformMassFloorAnchor w half ≤ K :=
      Nat.le_trans (Nat.le_max_right _ _)
        (Nat.le_max_right request _)
    exact rootTraffic_abs_matrix_le_rate_mul_diagonal
      (family.finiteCapacityAt K hstart)
      (centralPhysicalFiniteVacuumSectorUniformMassFloor_pos
        w (Q'.le_of_lt hw0) half)
      (centralPhysicalFiniteVacuumSectorUniformMassFloor_le
        hw0 hw1 half hmassAnchor)
      coefficient hcenter

/-- The same one analytic root-capacity input reaches the already constructed
completed vacuum-sector strict-contraction datum. -/
def toCompletedStrictContractionData
    {w : Q'} (hw0 : (0 : Q') < w) (hw1 : w < (1 : Q'))
    (half : Nat)
    (family : FixedNomeCofinalVacuumRootTrafficCapacity hw0 half) :
    CentralPhysicalVacuumSectorCylinderCompletedStrictContractionData
      hw0 hw1 half :=
  FixedNomeCofinalVacuumSectorFiniteStrictGap.toCompletedStrictContractionData
    hw0 hw1 half (toFiniteStrictGap hw1 family)

end FixedNomeCofinalVacuumRootTrafficCapacity

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap

/-! ## Dependency gates -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap.rootTraffic_strength_mul_diagonal_le_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap.rootTraffic_abs_matrix_le_rate_mul_diagonal
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap.FixedNomeCofinalVacuumRootTrafficCapacity.toFiniteStrictGap
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorRootTrafficCompletedGap.FixedNomeCofinalVacuumRootTrafficCapacity.toCompletedStrictContractionData
