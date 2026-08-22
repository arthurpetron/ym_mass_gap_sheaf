/-
# A strict later-uniform Poincare gap on every fixed BF4 vacuum carrier

For an arbitrary fixed base vacuum component, sum the persistent endpoint
estimate against the later pulled stationary weights.  Exact moving centering
turns pairwise variance into twice mass times the pulled diagonal form, while
the old-block Dirichlet embedding bounds the energy by twice the pulled
diagonal-minus-transfer deficit.  Positive mass cancels and normalization by
one removes it from the final constant.

Thus each fixed component has an explicit rational rate below one, uniform in
all later cutoffs and all coefficient vectors.  The rate is built from that
base component's floor and path ceiling and may vary with the base.  This is
not a cofinal uniform gap.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMass
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMass
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathEnergy
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
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
      Q'.recipPos denominator hdenominator * denominator ≈
        (1 : Q') :=
    Q'.eqv_trans _ _ _ (Q'.mul_comm_eqv _ _)
      (Q'.mul_recipPos_eqv denominator hdenominator)
  exact YMGap.Continuum.ContinuumClosureProgram.q'_lt_of_lt_of_le
    (Q'.lt_of_le_of_lt (Q'.le_of_eqv hleft) hscaled)
    (Q'.le_of_eqv hright)

private theorem pulled_poincare_left_identity
    (floor mass diagonal : Q') :
    floor * (mass * diagonal + mass * diagonal) ≈
      (mass + mass) * (floor * diagonal) := by
  q_ring

private theorem pulled_poincare_right_identity
    (mass ceiling diagonal matrix : Q') :
    (mass * mass) *
        (ceiling * ((diagonal + diagonal) + -(matrix + matrix))) ≈
      (mass + mass) *
        ((mass * ceiling) * (diagonal + -matrix)) := by
  q_ring

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

/-! ## 1. Moving-form order inherited from the later component -/

theorem fixedBasePulledMovingMatrix_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later)
    (coefficient : Nat → Q') :
    (0 : Q') ≤
      centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w hw base later half coefficient) := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w hw base later half moving
  have hfull := centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
    w hw later half extension
  have hrecode :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hlater coefficient
  exact Q'.le_trans' _ _ _ hfull (Q'.le_of_eqv hrecode)

theorem fixedBasePulledMovingMatrix_le_diagonal
    {w : Q'} {hw : (0 : Q') ≤ w}
    (base later half : Nat) (hlater : base ≤ later)
    (coefficient : Nat → Q') :
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w hw base later half coefficient) ≤
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
        w hw base later half
        (centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
          w hw base later half coefficient) := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    w hw base later half moving
  have hfull := centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
    w hw later half extension
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hlater coefficient
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
      (w := w) (hw := hw) (base := base) (later := later)
      (half := half) hlater coefficient
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hmatrix)
    (Q'.le_trans' _ _ _ hfull (Q'.le_of_eqv hdiagonal))

/-! ## 2. Mass-free Poincare inequality -/

namespace FixedBasePulledPositiveEdgeFloor

theorem floor_mul_movingDiagonal_le_ceiling_mul_deficit
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    certificate.floor *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving ≤
      centralPhysicalFiniteVacuumSectorPathCeiling w hw base half *
        (centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
            w hw base later half moving +
          -centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
            w hw base later half moving) := by
  let states := centralPhysicalFiniteVacuumSectorIndices w hw base half
  let weight := centralPhysicalFinitePulledWeight w hw base later half
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let mass := fixedBasePulledMass w hw base later half
  let diagonal := centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    w hw base later half moving
  let matrix := centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    w hw base later half moving
  let ceiling := centralPhysicalFiniteVacuumSectorPathCeiling
    w hw base half
  let pairwise := finiteWeightedPairwiseVariance states weight moving
  let energy := finiteJointDirichletEnergy states moving
    (centralPhysicalFinitePulledKernel w hw base later half)
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  have hweight : ∀ state, state ∈ states →
      (0 : Q') ≤ weight state := by
    intro state _hstate
    exact centralPhysicalFinitePulledWeight_nonnegative
      w hw base later half state
  have hendpoint : ∀ left, left ∈ states →
      ∀ right, right ∈ states →
      certificate.floor *
          ((moving left + -moving right) *
            (moving left + -moving right)) ≤
        ceiling * energy := by
    intro left hleft right hright
    exact
      BF4PhysicalCutoffVacuumSectorPulledPathEnergy.FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
        certificate later hlater moving left right hleft hright
  have hbound : certificate.floor * pairwise ≤
      (mass * mass) * (ceiling * energy) := by
    exact floor_mul_finiteWeightedPairwiseVariance_le
      states weight moving certificate.floor ceiling energy
      hweight hendpoint
  have hcenter : finiteListWeightedMean states weight moving ≈ 0 :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
      w hw base later half coefficient
  have hpairwiseGeneric :=
    finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal
      states weight moving hcenter
  have hdiagonal : finiteWeightedSquare states weight moving ≈
      diagonal := by
    unfold finiteWeightedSquare diagonal
      centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    apply listQSum_congr
    intro state
    exact Q'.mul_comm_eqv _ _
  have hpairwise : pairwise ≈
      mass * diagonal + mass * diagonal :=
    Q'.eqv_trans _ _ _ hpairwiseGeneric
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left mass _ _ hdiagonal)
        (Q'.mul_eqv_congr_left mass _ _ hdiagonal))
  have henergy : energy ≤
      (diagonal + diagonal) + -(matrix + matrix) :=
    fixedBasePulledDirichlet_le_twice_moving_deficit
      base later half hbaseLater coefficient
  have hmass0 : (0 : Q') ≤ mass :=
    Q'.le_of_lt (fixedBasePulledMass_pos w hw base later half)
  have hceiling0 : (0 : Q') ≤ ceiling :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorPathCeiling_pos
        w hw base half)
  have henergyScaled :
      (mass * mass) * (ceiling * energy) ≤
        (mass * mass) *
          (ceiling * ((diagonal + diagonal) + -(matrix + matrix))) := by
    apply Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ henergy hceiling0)
    exact Q'.mul_nonneg _ _ hmass0 hmass0
  have hleft : certificate.floor * pairwise ≈
      (mass + mass) * (certificate.floor * diagonal) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left certificate.floor _ _ hpairwise)
      (pulled_poincare_left_identity
        certificate.floor mass diagonal)
  have hright :
      (mass * mass) *
          (ceiling * ((diagonal + diagonal) + -(matrix + matrix))) ≈
        (mass + mass) *
          ((mass * ceiling) * (diagonal + -matrix)) :=
    pulled_poincare_right_identity mass ceiling diagonal matrix
  have hscaled :
      (mass + mass) * (certificate.floor * diagonal) ≤
        (mass + mass) *
          ((mass * ceiling) * (diagonal + -matrix)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_trans' _ _ _ henergyScaled (Q'.le_of_eqv hright)))
  have hmassPoincare : certificate.floor * diagonal ≤
      (mass * ceiling) * (diagonal + -matrix) :=
    Q'.le_of_mul_le_mul_left hscaled
      (Q'.pos_add_nonneg
        (fixedBasePulledMass_pos w hw base later half) hmass0)
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
    (w := w) (hw := hw) base later half hbaseLater coefficient
  have hdeficit0 : (0 : Q') ≤ diagonal + -matrix :=
    Q'.sub_nonneg_of_le hmatrixDiagonal
  have hmassCeiling : mass * ceiling ≤ ceiling := by
    exact Q'.le_trans' _ ((1 : Q') * ceiling) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (fixedBasePulledMass_le_one base later half hbaseLater)
        hceiling0)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hmassPoincare
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hmassCeiling hdeficit0)

/-! ## 3. The explicit base-indexed strict rate -/

def uniformGapDenominator
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Q' :=
  centralPhysicalFiniteVacuumSectorPathCeiling w hw base half +
    certificate.floor

theorem uniformGapDenominator_pos
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    (0 : Q') < uniformGapDenominator certificate := by
  unfold uniformGapDenominator
  exact Q'.pos_add_nonneg
    (centralPhysicalFiniteVacuumSectorPathCeiling_pos w hw base half)
    (Q'.le_of_lt certificate.floor_pos)

def uniformPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Q' :=
  Q'.divPos
    (centralPhysicalFiniteVacuumSectorPathCeiling w hw base half)
    (uniformGapDenominator certificate)
    (uniformGapDenominator_pos certificate)

theorem uniformPoincareRate_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    (0 : Q') ≤ uniformPoincareRate certificate := by
  exact Q'.le_of_lt (Q'.divPos_pos _ _
    (uniformGapDenominator_pos certificate)
    (centralPhysicalFiniteVacuumSectorPathCeiling_pos
      w hw base half))

theorem uniformPoincareRate_lt_one
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    uniformPoincareRate certificate < (1 : Q') := by
  apply divPos_lt_one_of_lt_local
  exact lt_add_of_pos_right_local _ _ certificate.floor_pos

theorem uniformGapDenominator_mul_movingMatrix_le
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    uniformGapDenominator certificate *
        centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w hw base later half moving ≤
      centralPhysicalFiniteVacuumSectorPathCeiling w hw base half *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let diagonal := centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    w hw base later half moving
  let matrix := centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    w hw base later half moving
  let ceiling := centralPhysicalFiniteVacuumSectorPathCeiling
    w hw base half
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  have hpoincare := floor_mul_movingDiagonal_le_ceiling_mul_deficit
    certificate later hlater coefficient
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
    (w := w) (hw := hw) base later half hbaseLater coefficient
  have hfloorMatrix : certificate.floor * matrix ≤
      certificate.floor * diagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmatrixDiagonal
      (Q'.le_of_lt certificate.floor_pos)
  have hfirst : (ceiling + certificate.floor) * matrix ≤
      ceiling * matrix + certificate.floor * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.add_mul_eqv ceiling certificate.floor matrix))
      (Q'.add_le_add_left _ _ _ hfloorMatrix)
  have hadd := Q'.add_le_add_right
    (certificate.floor * diagonal)
    (ceiling * (diagonal + -matrix))
    (ceiling * matrix) hpoincare
  have haddFinal : certificate.floor * diagonal + ceiling * matrix ≤
      ceiling * diagonal :=
    Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (scale_deficit_cancel_local ceiling diagonal matrix))
  unfold uniformGapDenominator
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _
      (certificate.floor * diagonal + ceiling * matrix) _
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) haddFinal)

theorem movingMatrix_le_uniformPoincareRate_mul_diagonal
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
        w hw base later half moving ≤
      uniformPoincareRate certificate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving := by
  let moving :=
    centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
      w hw base later half coefficient
  let diagonal := centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
    w hw base later half moving
  let matrix := centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
    w hw base later half moving
  let ceiling := centralPhysicalFiniteVacuumSectorPathCeiling
    w hw base half
  have hscaled := uniformGapDenominator_mul_movingMatrix_le
    certificate later hlater coefficient
  have hcommuted : matrix * uniformGapDenominator certificate ≤
      ceiling * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv matrix (uniformGapDenominator certificate)))
      hscaled
  have hdivision := Q'.le_divPos_of_mul_le
    (ceiling * diagonal)
    (uniformGapDenominator certificate)
    (uniformGapDenominator_pos certificate) hcommuted
  exact Q'.le_trans' _ _ _ hdivision
    (Q'.le_of_eqv
      (divPos_mul_right_eqv_local ceiling diagonal
        (uniformGapDenominator certificate)
        (uniformGapDenominator_pos certificate)))

theorem moving_abs_gap_at_uniformPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    Q'.abs
        (centralPhysicalFinitePulledVacuumSectorMatrixQuadratic
          w hw base later half moving) ≤
      uniformPoincareRate certificate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving := by
  have hbaseLater : base ≤ later :=
    Nat.le_trans certificate.start_ge_base hlater
  dsimp only
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (fixedBasePulledMovingMatrix_nonnegative
      (w := w) (hw := hw)
      base later half hbaseLater coefficient)]
  exact movingMatrix_le_uniformPoincareRate_mul_diagonal
    certificate later hlater coefficient

end FixedBasePulledPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap.fixedBasePulledMovingMatrix_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap.FixedBasePulledPositiveEdgeFloor.floor_mul_movingDiagonal_le_ceiling_mul_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap.FixedBasePulledPositiveEdgeFloor.uniformPoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap.FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate
