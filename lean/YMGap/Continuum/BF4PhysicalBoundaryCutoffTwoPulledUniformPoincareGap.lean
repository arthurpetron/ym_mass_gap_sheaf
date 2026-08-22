/-
# A uniform finite BF4 Poincare gap from the fixed pulled edge floor

On the fixed cutoff-two vacuum carrier, sum the uniform endpoint estimate
against the later pulled stationary weights.  Exact centering converts the
pairwise variance into twice mass times the moving diagonal, while the pulled
Dirichlet embedding bounds the energy by twice the moving deficit.  The
positive mass cancels and its normalized upper bound removes it from the
constant.

Consequently, the one common positive-edge-floor certificate supplies an
explicit cutoff-independent rational rate strictly below one for every later
moving centered form.  The certificate itself is not inhabited here.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass
import YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap

namespace YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledDirichletEmbedding
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledEntryPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledMass
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledRecenteringPerturbation
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPathEnergy
open YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoVacuumLocalFactors
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorGramPositivity
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
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

/-! ## 1. Moving-form order inherited from the full later vacuum sector -/

theorem cutoffTwoPulledMovingMatrix_nonnegative
    (later : Nat) (hlater : 2 ≤ later) (coefficient : Nat → Q') :
    (0 : Q') ≤
      cutoffTwoPulledMatrixAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let moving := cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    cutoffTwoHalfCoupling (by decide) 2 later 0 moving
  have hfull := centralPhysicalFiniteVacuumSectorMatrixQuadratic_nonnegative
    cutoffTwoHalfCoupling (by decide) later 0 extension
  have hrecode :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (base := 2) (later := later) (half := 0) hlater coefficient
  exact Q'.le_trans' _ _ _ hfull (Q'.le_of_eqv hrecode)

theorem cutoffTwoPulledMovingMatrix_le_diagonal
    (later : Nat) (hlater : 2 ≤ later) (coefficient : Nat → Q') :
    cutoffTwoPulledMatrixAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) ≤
      cutoffTwoPulledDiagonalAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let moving := cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let extension := centralPhysicalFiniteVacuumSectorCoefficientExtension
    cutoffTwoHalfCoupling (by decide) 2 later 0 moving
  have hfull := centralPhysicalFiniteVacuumSectorMatrix_le_diagonal
    cutoffTwoHalfCoupling (by decide) later 0 extension
  have hmatrix :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionMatrix_eqv_pulled
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (base := 2) (later := later) (half := 0) hlater coefficient
  have hdiagonal :=
    centralPhysicalFiniteVacuumSectorHeadCenteredExtensionDiagonal_eqv_pulled
      (w := cutoffTwoHalfCoupling) (hw := by decide)
      (base := 2) (later := later) (half := 0) hlater coefficient
  exact Q'.le_trans' _ _ _ (Q'.ge_of_eqv hmatrix)
    (Q'.le_trans' _ _ _ hfull (Q'.le_of_eqv hdiagonal))

/-! ## 2. The mass-free uniform Poincare inequality -/

namespace CutoffTwoPulledUniformBasePositiveEdgeFloor

theorem floor_mul_movingDiagonal_le_ceiling_mul_deficit
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    certificate.floor *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) ≤
      cutoffTwoPulledCanonicalPathCeiling *
        (cutoffTwoPulledDiagonalAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) +
          -cutoffTwoPulledMatrixAt later
            (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) := by
  let states := cutoffTwoPulledStates
  let weight := cutoffTwoPulledWeightAt later
  let moving := cutoffTwoPulledMovingCenteredCoefficientAt later coefficient
  let mass := cutoffTwoPulledMassAt later
  let diagonal := cutoffTwoPulledDiagonalAt later moving
  let matrix := cutoffTwoPulledMatrixAt later moving
  let pairwise := finiteWeightedPairwiseVariance states weight moving
  let energy := finiteJointDirichletEnergy states moving
    (cutoffTwoPulledKernelAt later)
  have htwoLater : 2 ≤ later :=
    Nat.le_trans certificate.start_ge_two hlater
  have hweight : ∀ state, state ∈ states → (0 : Q') ≤ weight state := by
    intro state _hstate
    unfold weight cutoffTwoPulledWeightAt
    exact centralPhysicalFinitePulledWeight_nonnegative
      cutoffTwoHalfCoupling (by decide) 2 later 0 state
  have hendpoint : ∀ left, left ∈ states → ∀ right, right ∈ states →
      certificate.floor *
          ((moving left + -moving right) *
            (moving left + -moving right)) ≤
        cutoffTwoPulledCanonicalPathCeiling * energy := by
    intro left hleft right hright
    exact certificate.floor_mul_endpoint_sq_le_ceiling_mul_pulledDirichlet
      later hlater moving left right hleft hright
  have hbound : certificate.floor * pairwise ≤
      (mass * mass) *
        (cutoffTwoPulledCanonicalPathCeiling * energy) := by
    exact floor_mul_finiteWeightedPairwiseVariance_le
      states weight moving certificate.floor
      cutoffTwoPulledCanonicalPathCeiling energy hweight hendpoint
  have hcenter : finiteListWeightedMean states weight moving ≈ 0 := by
    exact centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient_meanZero
      cutoffTwoHalfCoupling (by decide) 2 later 0 coefficient
  have hpairwiseGeneric :=
    finiteWeightedPairwiseVariance_centered_eqv_twice_mass_diagonal
      states weight moving hcenter
  have hdiagonal : finiteWeightedSquare states weight moving ≈ diagonal := by
    unfold finiteWeightedSquare diagonal cutoffTwoPulledDiagonalAt
    apply listQSum_congr
    intro state
    exact Q'.mul_comm_eqv _ _
  have hpairwise : pairwise ≈
      mass * diagonal + mass * diagonal := by
    exact Q'.eqv_trans _ _ _ hpairwiseGeneric
      (Q'.add_eqv_congr'
        (Q'.mul_eqv_congr_left mass _ _ hdiagonal)
        (Q'.mul_eqv_congr_left mass _ _ hdiagonal))
  have henergy : energy ≤
      (diagonal + diagonal) + -(matrix + matrix) := by
    exact cutoffTwoPulledDirichlet_le_twice_moving_deficit
      later htwoLater coefficient
  have hmass0 : (0 : Q') ≤ mass :=
    Q'.le_of_lt (cutoffTwoPulledMassAt_pos later)
  have hceiling0 : (0 : Q') ≤ cutoffTwoPulledCanonicalPathCeiling :=
    Q'.le_of_lt cutoffTwoPulledCanonicalPathCeiling_pos
  have henergyScaled :
      (mass * mass) *
          (cutoffTwoPulledCanonicalPathCeiling * energy) ≤
        (mass * mass) *
          (cutoffTwoPulledCanonicalPathCeiling *
            ((diagonal + diagonal) + -(matrix + matrix))) := by
    apply Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ henergy hceiling0)
    exact Q'.mul_nonneg _ _ hmass0 hmass0
  have hleft : certificate.floor * pairwise ≈
      (mass + mass) * (certificate.floor * diagonal) := by
    exact Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left certificate.floor _ _ hpairwise)
      (pulled_poincare_left_identity
        certificate.floor mass diagonal)
  have hright :
      (mass * mass) *
          (cutoffTwoPulledCanonicalPathCeiling *
            ((diagonal + diagonal) + -(matrix + matrix))) ≈
        (mass + mass) *
          ((mass * cutoffTwoPulledCanonicalPathCeiling) *
            (diagonal + -matrix)) :=
    pulled_poincare_right_identity mass
      cutoffTwoPulledCanonicalPathCeiling diagonal matrix
  have hscaled :
      (mass + mass) * (certificate.floor * diagonal) ≤
        (mass + mass) *
          ((mass * cutoffTwoPulledCanonicalPathCeiling) *
            (diagonal + -matrix)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_trans' _ _ _ henergyScaled (Q'.le_of_eqv hright)))
  have hmassPoincare : certificate.floor * diagonal ≤
      (mass * cutoffTwoPulledCanonicalPathCeiling) *
        (diagonal + -matrix) :=
    Q'.le_of_mul_le_mul_left hscaled
      (Q'.pos_add_nonneg (cutoffTwoPulledMassAt_pos later) hmass0)
  have hmatrixDiagonal := cutoffTwoPulledMovingMatrix_le_diagonal
    later htwoLater coefficient
  have hdeficit0 : (0 : Q') ≤ diagonal + -matrix :=
    Q'.sub_nonneg_of_le hmatrixDiagonal
  have hmassCeiling :
      mass * cutoffTwoPulledCanonicalPathCeiling ≤
        cutoffTwoPulledCanonicalPathCeiling := by
    exact Q'.le_trans' _
      ((1 : Q') * cutoffTwoPulledCanonicalPathCeiling) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (cutoffTwoPulledMassAt_le_one later htwoLater) hceiling0)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hmassPoincare
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hmassCeiling hdeficit0)

/-! ## 3. One explicit cutoff-independent strict rate -/

def uniformGapDenominator
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor) : Q' :=
  cutoffTwoPulledCanonicalPathCeiling + certificate.floor

theorem uniformGapDenominator_pos
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor) :
    (0 : Q') < uniformGapDenominator certificate := by
  unfold uniformGapDenominator
  exact Q'.pos_add_nonneg cutoffTwoPulledCanonicalPathCeiling_pos
    (Q'.le_of_lt certificate.floor_pos)

def uniformPoincareRate
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor) : Q' :=
  Q'.divPos cutoffTwoPulledCanonicalPathCeiling
    (uniformGapDenominator certificate)
    (uniformGapDenominator_pos certificate)

theorem uniformPoincareRate_nonnegative
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor) :
    (0 : Q') ≤ uniformPoincareRate certificate := by
  exact Q'.le_of_lt (Q'.divPos_pos _ _
    (uniformGapDenominator_pos certificate)
    cutoffTwoPulledCanonicalPathCeiling_pos)

theorem uniformPoincareRate_lt_one
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor) :
    uniformPoincareRate certificate < (1 : Q') := by
  apply divPos_lt_one_of_lt_local
  exact lt_add_of_pos_right_local _ _ certificate.floor_pos

theorem uniformGapDenominator_mul_movingMatrix_le
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    uniformGapDenominator certificate *
        cutoffTwoPulledMatrixAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) ≤
      cutoffTwoPulledCanonicalPathCeiling *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let diagonal := cutoffTwoPulledDiagonalAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  let matrix := cutoffTwoPulledMatrixAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  have htwoLater : 2 ≤ later :=
    Nat.le_trans certificate.start_ge_two hlater
  have hpoincare := floor_mul_movingDiagonal_le_ceiling_mul_deficit
    certificate later hlater coefficient
  have hmatrixDiagonal := cutoffTwoPulledMovingMatrix_le_diagonal
    later htwoLater coefficient
  have hfloorMatrix : certificate.floor * matrix ≤
      certificate.floor * diagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmatrixDiagonal
      (Q'.le_of_lt certificate.floor_pos)
  have hfirst :
      (cutoffTwoPulledCanonicalPathCeiling + certificate.floor) * matrix ≤
        cutoffTwoPulledCanonicalPathCeiling * matrix +
          certificate.floor * diagonal := by
    exact Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.add_mul_eqv cutoffTwoPulledCanonicalPathCeiling
          certificate.floor matrix))
      (Q'.add_le_add_left _ _ _ hfloorMatrix)
  have hadd := Q'.add_le_add_right
    (certificate.floor * diagonal)
    (cutoffTwoPulledCanonicalPathCeiling * (diagonal + -matrix))
    (cutoffTwoPulledCanonicalPathCeiling * matrix) hpoincare
  have haddFinal :
      certificate.floor * diagonal +
          cutoffTwoPulledCanonicalPathCeiling * matrix ≤
        cutoffTwoPulledCanonicalPathCeiling * diagonal :=
    Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv
        (scale_deficit_cancel_local
          cutoffTwoPulledCanonicalPathCeiling diagonal matrix))
  unfold uniformGapDenominator
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _
      (certificate.floor * diagonal +
        cutoffTwoPulledCanonicalPathCeiling * matrix) _
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) haddFinal)

theorem movingMatrix_le_uniformPoincareRate_mul_diagonal
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    cutoffTwoPulledMatrixAt later
        (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) ≤
      uniformPoincareRate certificate *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  let diagonal := cutoffTwoPulledDiagonalAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  let matrix := cutoffTwoPulledMatrixAt later
    (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)
  have hscaled := uniformGapDenominator_mul_movingMatrix_le
    certificate later hlater coefficient
  have hcommuted : matrix * uniformGapDenominator certificate ≤
      cutoffTwoPulledCanonicalPathCeiling * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv
        (Q'.mul_comm_eqv matrix (uniformGapDenominator certificate)))
      hscaled
  have hdivision := Q'.le_divPos_of_mul_le
    (cutoffTwoPulledCanonicalPathCeiling * diagonal)
    (uniformGapDenominator certificate)
    (uniformGapDenominator_pos certificate) hcommuted
  exact Q'.le_trans' _ _ _ hdivision
    (Q'.le_of_eqv
      (divPos_mul_right_eqv_local
        cutoffTwoPulledCanonicalPathCeiling diagonal
        (uniformGapDenominator certificate)
        (uniformGapDenominator_pos certificate)))

theorem moving_abs_gap_at_uniformPoincareRate
    (certificate : CutoffTwoPulledUniformBasePositiveEdgeFloor)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    Q'.abs
        (cutoffTwoPulledMatrixAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient)) ≤
      uniformPoincareRate certificate *
        cutoffTwoPulledDiagonalAt later
          (cutoffTwoPulledMovingCenteredCoefficientAt later coefficient) := by
  have htwoLater : 2 ≤ later :=
    Nat.le_trans certificate.start_ge_two hlater
  rw [YMGap.Constructive.ExpNeg.abs_of_nonneg
    (cutoffTwoPulledMovingMatrix_nonnegative
      later htwoLater coefficient)]
  exact movingMatrix_le_uniformPoincareRate_mul_diagonal
    certificate later hlater coefficient

end CutoffTwoPulledUniformBasePositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap.cutoffTwoPulledMovingMatrix_nonnegative
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap.CutoffTwoPulledUniformBasePositiveEdgeFloor.floor_mul_movingDiagonal_le_ceiling_mul_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap.CutoffTwoPulledUniformBasePositiveEdgeFloor.uniformPoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalBoundaryCutoffTwoPulledUniformPoincareGap.CutoffTwoPulledUniformBasePositiveEdgeFloor.moving_abs_gap_at_uniformPoincareRate
