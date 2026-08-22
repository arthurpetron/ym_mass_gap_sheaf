/-
# An explicit strict Poincare gap on every finite BF4 vacuum sector

The centered pairwise identity and its path bound now refer to the same exact
quantity.  This module eliminates that quantity and cancels the positive
factor `2 * sectorMass`, yielding

  edgeFloor * diagonal <= sectorMass * pathCeiling * (diagonal - matrix).

Writing `A = sectorMass * pathCeiling`, nonexpansivity gives

  (A + edgeFloor) * matrix <= A * diagonal.

The explicit rational rate `q = A / (A + edgeFloor)` is nonnegative and
strictly below one, so every exactly centered coefficient vector satisfies the
absolute finite-sector form gap.  The rate is coefficient-independent at the
fixed cutoff, but it is not claimed uniform in cutoff.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance

namespace YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalCutoffFiniteIndexBridge
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorBlockDecomposition
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorEdgeFloor
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorStationaryLaws
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
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

private theorem lt_add_of_pos_right (a b : Q')
    (hb : (0 : Q') < b) : a < a + b := by
  show a.num * ((a + b).den : Int) <
    (a + b).num * (a.den : Int)
  have hbnum : (0 : Int) < b.num := Q'.num_pos_of_pos hb
  show a.num * ((a.den * b.den : Nat) : Int) <
    (a.num * (b.den : Int) + b.num * (a.den : Int)) *
      (a.den : Int)
  have hcast : ((a.den * b.den : Nat) : Int) =
      (a.den : Int) * (b.den : Int) := by
    push_cast
    rfl
  rw [hcast]
  have hadenpos : (0 : Int) < (a.den : Int) := by
    exact_mod_cast a.den_pos
  have key : (0 : Int) <
      b.num * (a.den : Int) * (a.den : Int) :=
    Int.mul_pos (Int.mul_pos hbnum hadenpos) hadenpos
  have hexpand :
      (a.num * (b.den : Int) + b.num * (a.den : Int)) *
          (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) +
          b.num * (a.den : Int) * (a.den : Int) := by
    rw [Int.add_mul]
    have e1 : a.num * (b.den : Int) * (a.den : Int) =
        a.num * ((a.den : Int) * (b.den : Int)) := by
      rw [Int.mul_assoc, Int.mul_comm (b.den : Int) (a.den : Int)]
    rw [e1]
  rw [hexpand]
  omega

private theorem divPos_lt_one_of_lt
    (numerator denominator : Q')
    (hdenominator : (0 : Q') < denominator)
    (hnumerator : numerator < denominator) :
    Q'.divPos numerator denominator hdenominator < (1 : Q') := by
  unfold Q'.divPos
  have hreciprocal : (0 : Q') <
      Q'.recipPos denominator hdenominator :=
    Q'.recipPos_pos denominator hdenominator
  have hscaled :
      Q'.recipPos denominator hdenominator * numerator <
        Q'.recipPos denominator hdenominator * denominator :=
    Q'.mul_lt_mul_of_pos_left hreciprocal hnumerator
  have hleft :
      numerator * Q'.recipPos denominator hdenominator ≈
        Q'.recipPos denominator hdenominator * numerator :=
    Q'.mul_comm_eqv _ _
  have hright :
      Q'.recipPos denominator hdenominator * denominator ≈
        (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv denominator hdenominator)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.le_of_eqv hright)

private theorem poincare_left_identity
    (floor mass diagonal : Q') :
    floor * (mass * diagonal + mass * diagonal) ≈
      (mass + mass) * (floor * diagonal) := by
  q_ring

private theorem poincare_right_identity
    (mass ceiling diagonal matrix : Q') :
    (mass * mass) *
        (ceiling * ((diagonal + diagonal) + -(matrix + matrix))) ≈
      (mass + mass) *
        ((mass * ceiling) * (diagonal + -matrix)) := by
  q_ring

private theorem scale_deficit_cancel
    (scale diagonal matrix : Q') :
    scale * (diagonal + -matrix) + scale * matrix ≈
      scale * diagonal := by
  refine Q'.eqv_trans _
    ((scale * diagonal + scale * (-matrix)) + scale * matrix) _ ?_ ?_
  · exact Q'.add_eqv_congr_right _ _ _
      (Q'.mul_add_eqv scale diagonal (-matrix))
  refine Q'.eqv_trans _
    (scale * diagonal + (scale * (-matrix) + scale * matrix)) _
    (Q'.add_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (scale * diagonal + (-(scale * matrix) + scale * matrix)) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.add_eqv_congr_right _ _ _
        (Q'.mul_neg_eqv scale matrix))
  refine Q'.eqv_trans _ (scale * diagonal + 0) _ ?_ ?_
  · exact Q'.add_eqv_congr_left _ _ _
      (Q'.neg_add_self_eqv (scale * matrix))
  · exact Q'.eqv_of_eq (Q'.add_zero' _)

private theorem divPos_mul_right_eqv
    (scale diagonal denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (scale * diagonal) denominator hdenominator ≈
      Q'.divPos scale denominator hdenominator * diagonal := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (scale *
      (diagonal * Q'.recipPos denominator hdenominator)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (scale *
      (Q'.recipPos denominator hdenominator * diagonal)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left scale _ _
      (Q'.mul_comm_eqv _ _)
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-! ## 1. Positive finite constants and form order -/

theorem centralPhysicalFiniteVacuumSectorMass_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorMass
      w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorMass finiteWeightedMass
  exact centralPhysicalFiniteVacuumSectorWeightSum_pos
    w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorDiagonalQuadratic_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  unfold centralPhysicalFiniteVacuumSectorDiagonalQuadratic
  apply listQSum_nonnegative_on
  intro index _hindex
  exact Q'.mul_nonneg _ _
    (YMGap.Constructive.SumOfSquares.q_mul_self_nonneg
      (coefficient index))
    (centralPhysicalRowMarginal_nonnegative hw cutoff half
      (centralPhysicalFiniteStateAt w hw cutoff half index))

theorem centralPhysicalFiniteVacuumSector_deficit_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient +
        -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) := by
  have henergy : (0 : Q') ≤
      finiteJointDirichletEnergy
        (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
        coefficient
        (centralPhysicalFiniteKernel w hw cutoff half) :=
    finiteJointDirichletEnergy_nonnegative
      (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
      coefficient
      (centralPhysicalFiniteKernel w hw cutoff half)
      (fun source target => by
        unfold centralPhysicalFiniteKernel
        exact centralNormalizedPhysicalReflectedKernel_nonnegative
          hw cutoff half _ _)
  have hhalfEnergy : (0 : Q') ≤
      Q'.mkPos 1 2 (by decide) *
        finiteJointDirichletEnergy
          (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
          coefficient
          (centralPhysicalFiniteKernel w hw cutoff half) :=
    Q'.mul_nonneg _ _ (Q'.le_of_lt (by decide)) henergy
  exact Q'.le_trans' _ _ _ hhalfEnergy
    (Q'.le_of_eqv
      (half_mul_centralPhysicalFiniteVacuumSectorDirichlet_eqv_deficit
        w hw cutoff half coefficient))

theorem centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q') :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient ≤
      centralPhysicalFiniteVacuumSectorDiagonalQuadratic
        w hw cutoff half coefficient := by
  apply Q'.le_of_sub_nonneg
  exact centralPhysicalFiniteVacuumSector_deficit_nonnegative
    w hw cutoff half coefficient

/-! ## 2. The finite Poincare inequality -/

/-- Eliminating pairwise variance and cancelling the positive doubled sector
mass gives a coefficient-independent Poincare constant. -/
theorem centralPhysicalFiniteVacuumSector_poincare
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient ≤
      (centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
          centralPhysicalFiniteVacuumSectorPathCeiling
            w hw cutoff half) *
        (centralPhysicalFiniteVacuumSectorDiagonalQuadratic
            w hw cutoff half coefficient +
          -(centralPhysicalFiniteVacuumSectorMatrixQuadratic
            w hw cutoff half coefficient)) := by
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
    w hw cutoff half
  let mass := centralPhysicalFiniteVacuumSectorMass
    w hw cutoff half
  let ceiling := centralPhysicalFiniteVacuumSectorPathCeiling
    w hw cutoff half
  let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w hw cutoff half coefficient
  let matrix := centralPhysicalFiniteVacuumSectorMatrixQuadratic
    w hw cutoff half coefficient
  let pairwise := centralPhysicalFiniteVacuumSectorPairwiseVariance
    w hw cutoff half coefficient
  let energy := finiteJointDirichletEnergy
    (centralPhysicalFiniteVacuumSectorIndices w hw cutoff half)
    coefficient
    (centralPhysicalFiniteKernel w hw cutoff half)
  have hbound :=
    centralPhysicalFiniteVacuumSector_floor_mul_pairwiseVariance_le
      w hw cutoff half coefficient
  have hpairwise :=
    centralPhysicalFiniteVacuumSectorPairwiseVariance_centered_eqv
      w hw cutoff half coefficient hcenter
  have henergy :=
    centralPhysicalFiniteVacuumSectorDirichlet_eqv_twice_deficit
      w hw cutoff half coefficient
  have hleft : floor * pairwise ≈
      (mass + mass) * (floor * diagonal) := by
    refine Q'.eqv_trans _
      (floor * (mass * diagonal + mass * diagonal)) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left floor _ _ hpairwise
    · exact poincare_left_identity floor mass diagonal
  have hright :
      (mass * mass) * (ceiling * energy) ≈
        (mass + mass) *
          ((mass * ceiling) * (diagonal + -matrix)) := by
    refine Q'.eqv_trans _
      ((mass * mass) *
        (ceiling *
          ((diagonal + diagonal) + -(matrix + matrix)))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left (mass * mass) _ _
        (Q'.mul_eqv_congr_left ceiling _ _ henergy)
    · exact poincare_right_identity mass ceiling diagonal matrix
  have hscaled :
      (mass + mass) * (floor * diagonal) ≤
        (mass + mass) *
          ((mass * ceiling) * (diagonal + -matrix)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hbound (Q'.le_of_eqv hright))
  exact Q'.le_of_mul_le_mul_left hscaled
    (Q'.pos_add_nonneg
      (centralPhysicalFiniteVacuumSectorMass_pos
        w hw cutoff half)
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorMass_pos
          w hw cutoff half)))

/-! ## 3. Explicit strict finite rate -/

def centralPhysicalFiniteVacuumSectorGapScale
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorMass w hw cutoff half *
    centralPhysicalFiniteVacuumSectorPathCeiling w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorGapScale_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorGapScale
      w hw cutoff half :=
  Q'.mul_pos
    (centralPhysicalFiniteVacuumSectorMass_pos w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorPathCeiling_pos
      w hw cutoff half)

def centralPhysicalFiniteVacuumSectorGapDenominator
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  centralPhysicalFiniteVacuumSectorGapScale w hw cutoff half +
    centralPhysicalFiniteVacuumSectorEdgeFloor w hw cutoff half

theorem centralPhysicalFiniteVacuumSectorGapDenominator_pos
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') < centralPhysicalFiniteVacuumSectorGapDenominator
      w hw cutoff half := by
  unfold centralPhysicalFiniteVacuumSectorGapDenominator
  exact Q'.pos_add_nonneg
    (centralPhysicalFiniteVacuumSectorGapScale_pos
      w hw cutoff half)
    (Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
        w hw cutoff half))

/-- The canonical coefficient-independent strict rate at a fixed sector. -/
def centralPhysicalFiniteVacuumSectorPoincareRate
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) : Q' :=
  Q'.divPos
    (centralPhysicalFiniteVacuumSectorGapScale w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGapDenominator w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGapDenominator_pos
      w hw cutoff half)

theorem centralPhysicalFiniteVacuumSectorPoincareRate_nonnegative
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    (0 : Q') ≤ centralPhysicalFiniteVacuumSectorPoincareRate
      w hw cutoff half := by
  exact Q'.le_of_lt (Q'.divPos_pos _ _
    (centralPhysicalFiniteVacuumSectorGapDenominator_pos
      w hw cutoff half)
    (centralPhysicalFiniteVacuumSectorGapScale_pos
      w hw cutoff half))

theorem centralPhysicalFiniteVacuumSectorPoincareRate_lt_one
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat) :
    centralPhysicalFiniteVacuumSectorPoincareRate
        w hw cutoff half < (1 : Q') := by
  apply divPos_lt_one_of_lt
  exact lt_add_of_pos_right _ _
    (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
      w hw cutoff half)

/-- The scaled strict form inequality before division by the positive
denominator. -/
theorem centralPhysicalFiniteVacuumSector_gapDenominator_mul_matrix_le
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorGapDenominator w hw cutoff half *
        centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient ≤
      centralPhysicalFiniteVacuumSectorGapScale w hw cutoff half *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient := by
  let floor := centralPhysicalFiniteVacuumSectorEdgeFloor
    w hw cutoff half
  let scale := centralPhysicalFiniteVacuumSectorGapScale
    w hw cutoff half
  let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w hw cutoff half coefficient
  let matrix := centralPhysicalFiniteVacuumSectorMatrixQuadratic
    w hw cutoff half coefficient
  have hpoincare := centralPhysicalFiniteVacuumSector_poincare
    w hw cutoff half coefficient hcenter
  have hmatrixDiagonal :=
    centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
      w hw cutoff half coefficient
  have hfloorMatrix : floor * matrix ≤ floor * diagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ floor hmatrixDiagonal
      (Q'.le_of_lt
        (centralPhysicalFiniteVacuumSectorEdgeFloor_pos
          w hw cutoff half))
  have hfirst : (scale + floor) * matrix ≤
      scale * matrix + floor * diagonal := by
    refine Q'.le_trans' _
      (scale * matrix + floor * matrix) _ ?_ ?_
    · exact Q'.le_of_eqv (Q'.add_mul_eqv scale floor matrix)
    · exact Q'.add_le_add_left _ _ _ hfloorMatrix
  have hadd := Q'.add_le_add_right
    (floor * diagonal)
    (scale * (diagonal + -matrix))
    (scale * matrix) hpoincare
  have haddFinal :
      floor * diagonal + scale * matrix ≤ scale * diagonal := by
    exact Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (scale_deficit_cancel scale diagonal matrix))
  unfold centralPhysicalFiniteVacuumSectorGapDenominator
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _
      (floor * diagonal + scale * matrix) _
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) haddFinal)

/-- Every exactly centered coefficient vector obeys the explicit strict
finite-sector form rate. -/
theorem centralPhysicalFiniteVacuumSector_matrix_le_poincareRate_mul_diagonal
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    centralPhysicalFiniteVacuumSectorMatrixQuadratic
        w hw cutoff half coefficient ≤
      centralPhysicalFiniteVacuumSectorPoincareRate w hw cutoff half *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient := by
  let denominator := centralPhysicalFiniteVacuumSectorGapDenominator
    w hw cutoff half
  let scale := centralPhysicalFiniteVacuumSectorGapScale
    w hw cutoff half
  let diagonal := centralPhysicalFiniteVacuumSectorDiagonalQuadratic
    w hw cutoff half coefficient
  let matrix := centralPhysicalFiniteVacuumSectorMatrixQuadratic
    w hw cutoff half coefficient
  have hscaled :=
    centralPhysicalFiniteVacuumSector_gapDenominator_mul_matrix_le
      w hw cutoff half coefficient hcenter
  have hcommuted : matrix * denominator ≤ scale * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv matrix denominator)) hscaled
  have hdivision := Q'.le_divPos_of_mul_le
    (scale * diagonal) denominator
    (centralPhysicalFiniteVacuumSectorGapDenominator_pos
      w hw cutoff half) hcommuted
  have hfactor : Q'.divPos (scale * diagonal) denominator
        (centralPhysicalFiniteVacuumSectorGapDenominator_pos
          w hw cutoff half) ≈
      centralPhysicalFiniteVacuumSectorPoincareRate w hw cutoff half *
        diagonal := by
    unfold centralPhysicalFiniteVacuumSectorPoincareRate
    exact divPos_mul_right_eqv scale diagonal denominator
      (centralPhysicalFiniteVacuumSectorGapDenominator_pos
        w hw cutoff half)
  exact Q'.le_trans' _ _ _ hdivision (Q'.le_of_eqv hfactor)

/-- Gram positivity turns the one-sided strict estimate into the absolute
form bound required by the spectral-gap interfaces. -/
theorem centralPhysicalFiniteVacuumSector_abs_matrix_le_poincareRate_mul_diagonal
    (w : Q') (hw : (0 : Q') ≤ w) (cutoff half : Nat)
    (coefficient : Nat → Q')
    (hcenter :
      centralPhysicalFiniteVacuumSectorWeightedMean
        w hw cutoff half coefficient ≈ 0) :
    Q'.abs
        (centralPhysicalFiniteVacuumSectorMatrixQuadratic
          w hw cutoff half coefficient) ≤
      centralPhysicalFiniteVacuumSectorPoincareRate w hw cutoff half *
        centralPhysicalFiniteVacuumSectorDiagonalQuadratic
          w hw cutoff half coefficient := by
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
      w hw cutoff half coefficient)]
  exact centralPhysicalFiniteVacuumSector_matrix_le_poincareRate_mul_diagonal
    w hw cutoff half coefficient hcenter

end YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap.centralPhysicalFiniteVacuumSector_poincare
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap.centralPhysicalFiniteVacuumSectorPoincareRate_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap.centralPhysicalFiniteVacuumSectorPoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap.centralPhysicalFiniteVacuumSector_gapDenominator_mul_matrix_le
#print axioms
  YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap.centralPhysicalFiniteVacuumSector_abs_matrix_le_poincareRate_mul_diagonal
