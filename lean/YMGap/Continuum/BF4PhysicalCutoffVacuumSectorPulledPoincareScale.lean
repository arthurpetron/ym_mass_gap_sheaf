/-
# A reusable positive-scale compiler for pulled BF4 Poincare gaps

The finite path argument produces two logically separate objects: a positive
rational scale and a proof that the persistent edge floor times the moving
diagonal is bounded by that scale times the moving deficit.  This module
packages exactly those data and compiles them, without division by a vector
norm, to a strict rational rate and an absolute moving-form gap.

The package is pointwise in one base carrier.  It does not construct a scale
or rate uniform over expanding carriers and makes no thermodynamic, continuum,
or Clay claim.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity

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

private theorem lt_add_of_pos_right_local (a b : Q')
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

private theorem divPos_lt_one_of_lt_local
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
      Q'.recipPos denominator hdenominator * denominator ≈ (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv denominator hdenominator)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.le_of_eqv hright)

private theorem scale_deficit_cancel_local
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

private theorem divPos_mul_right_eqv_local
    (scale diagonal denominator : Q')
    (hdenominator : (0 : Q') < denominator) :
    Q'.divPos (scale * diagonal) denominator hdenominator ≈
      Q'.divPos scale denominator hdenominator * diagonal := by
  unfold Q'.divPos
  refine Q'.eqv_trans _
    (scale * (diagonal * Q'.recipPos denominator hdenominator)) _
    (Q'.mul_assoc_eqv _ _ _) ?_
  refine Q'.eqv_trans _
    (scale * (Q'.recipPos denominator hdenominator * diagonal)) _ ?_ ?_
  · exact Q'.mul_eqv_congr_left scale _ _
      (Q'.mul_comm_eqv _ _)
  · exact Q'.eqv_symm (Q'.mul_assoc_eqv _ _ _)

/-! ## 1. Positive scale data -/

/-- A positive rational scale carrying the exact mass-free Poincare estimate
on all later head-centered pulled forms of one base carrier. -/
structure FixedBasePulledPoincareScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Type 1 where
  scale : Q'
  scale_pos : (0 : Q') < scale
  floor_mul_diagonal_le_scale_mul_deficit :
    ∀ later : Nat, certificate.start ≤ later →
    ∀ coefficient : Nat → Q',
      let moving :=
        centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w hw base later half coefficient
      certificate.floor *
          centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving ≤
        scale *
          (centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
              w hw base later half moving +
            -centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
              w hw base later half moving)

namespace FixedBasePulledPoincareScaleData

/-! ## 2. The denominator and strict rate -/

def denominator
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate) : Q' :=
  data.scale + certificate.floor

theorem denominator_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate) :
    (0 : Q') < data.denominator := by
  unfold denominator
  exact Q'.pos_add_nonneg data.scale_pos
    (Q'.le_of_lt certificate.floor_pos)

def rate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate) : Q' :=
  Q'.divPos data.scale data.denominator data.denominator_pos

theorem rate_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate) :
    (0 : Q') ≤ data.rate :=
  Q'.le_of_lt (Q'.divPos_pos _ _ data.denominator_pos data.scale_pos)

theorem rate_lt_one
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate) :
    data.rate < (1 : Q') := by
  apply divPos_lt_one_of_lt_local
  exact lt_add_of_pos_right_local _ _ certificate.floor_pos

/-- For a fixed positive edge floor, the compiled rate `scale/(scale+floor)`
is monotone in the supplied positive Poincare scale. -/
theorem rate_le_of_scale_le
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (left right : FixedBasePulledPoincareScaleData certificate)
    (hscale : left.scale ≤ right.scale) :
    left.rate ≤ right.rate := by
  have hfloor0 : (0 : Q') ≤ certificate.floor :=
    Q'.le_of_lt certificate.floor_pos
  have hcrossTerm : left.scale * certificate.floor ≤
      right.scale * certificate.floor :=
    Q'.mul_le_mul_of_nonneg_right _ _ _ hscale hfloor0
  have hcross : left.scale * right.denominator ≤
      right.scale * left.denominator := by
    unfold denominator
    have hsum : left.scale * right.scale +
          left.scale * certificate.floor ≤
        left.scale * right.scale + right.scale * certificate.floor :=
      Q'.add_le_add_left _ _ _ hcrossTerm
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_add_eqv left.scale right.scale certificate.floor))
      (Q'.le_trans' _ _ _ hsum
        (Q'.le_of_eqv
          (Q'.eqv_trans _
            (right.scale * left.scale +
              right.scale * certificate.floor) _
            (Q'.add_eqv_congr_right _ _ _
              (Q'.mul_comm_eqv left.scale right.scale))
            (Q'.eqv_symm
              (Q'.mul_add_eqv
                right.scale left.scale certificate.floor)))))
  have hdivided : left.scale ≤
      Q'.divPos (right.scale * left.denominator)
        right.denominator right.denominator_pos :=
    Q'.le_divPos_of_mul_le _ _ right.denominator_pos hcross
  have hfactor :
      Q'.divPos (right.scale * left.denominator)
          right.denominator right.denominator_pos ≈
        Q'.divPos right.scale right.denominator right.denominator_pos *
          left.denominator :=
    divPos_mul_right_eqv_local
      right.scale left.denominator right.denominator right.denominator_pos
  have hscaled : left.scale ≤
      Q'.divPos right.scale right.denominator right.denominator_pos *
        left.denominator :=
    Q'.le_trans' _ _ _ hdivided (Q'.le_of_eqv hfactor)
  change Q'.divPos left.scale left.denominator left.denominator_pos ≤
    Q'.divPos right.scale right.denominator right.denominator_pos
  exact Q'.divPos_le_of_le_mul
    left.scale left.denominator left.denominator_pos hscaled

/-! ## 3. Division-free and divided form bounds -/

theorem denominator_mul_movingMatrix_le
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    data.denominator *
        centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w hw base later half moving ≤
      data.scale *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let diagonal := centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    w hw base later half moving
  let matrix := centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    w hw base later half moving
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  have hpoincare := data.floor_mul_diagonal_le_scale_mul_deficit
    later hlater coefficient
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
    (w := w) (hw := hw) base later half hbaseLater coefficient
  have hfloorMatrix : certificate.floor * matrix ≤
      certificate.floor * diagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmatrixDiagonal
      (Q'.le_of_lt certificate.floor_pos)
  have hfirst : (data.scale + certificate.floor) * matrix ≤
      data.scale * matrix + certificate.floor * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.add_mul_eqv data.scale certificate.floor matrix))
      (Q'.add_le_add_left _ _ _ hfloorMatrix)
  have hadd := Q'.add_le_add_right
    (certificate.floor * diagonal)
    (data.scale * (diagonal + -matrix))
    (data.scale * matrix) hpoincare
  have haddFinal : certificate.floor * diagonal + data.scale * matrix ≤
      data.scale * diagonal :=
    Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (scale_deficit_cancel_local data.scale diagonal matrix))
  unfold denominator
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _
      (certificate.floor * diagonal + data.scale * matrix) _
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) haddFinal)

theorem movingMatrix_le_rate_mul_diagonal
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half moving ≤
      data.rate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let diagonal := centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    w hw base later half moving
  let matrix := centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    w hw base later half moving
  have hscaled := data.denominator_mul_movingMatrix_le
    later hlater coefficient
  have hcommuted : matrix * data.denominator ≤ data.scale * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv matrix data.denominator)) hscaled
  have hdivision := Q'.le_divPos_of_mul_le
    (data.scale * diagonal) data.denominator data.denominator_pos hcommuted
  exact Q'.le_trans' _ _ _ hdivision
    (Q'.le_of_eqv
      (divPos_mul_right_eqv_local data.scale diagonal
        data.denominator data.denominator_pos))

theorem moving_abs_gap
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledPoincareScaleData certificate)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w hw base later half moving) ≤
      data.rate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving := by
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  dsimp only
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (fixedBasePulledMovingMatrix_nonnegative
      (w := w) (hw := hw)
      base later half hbaseLater coefficient)]
  exact data.movingMatrix_le_rate_mul_diagonal later hlater coefficient

end FixedBasePulledPoincareScaleData

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale.FixedBasePulledPoincareScaleData.rate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale.FixedBasePulledPoincareScaleData.rate_le_of_scale_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale.FixedBasePulledPoincareScaleData.denominator_mul_movingMatrix_le
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale.FixedBasePulledPoincareScaleData.moving_abs_gap
