/-
# A sharper maximum-path Poincare rate on each pulled BF4 carrier

The located maximum of the base carrier's canonical path scales replaces the
earlier sum of all scales.  Combining that maximum with the already
constructed persistent edge floor yields a positive Poincare-scale datum and
therefore a strict rational moving-form rate on every fixed base carrier.

The new scale is proved no larger than the earlier sum ceiling.  It may still
grow with the base and the edge floor may still shrink, so no all-base common
rate, completed spectral gap, thermodynamic/continuum limit, or Clay result is
asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathMaximum
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap

set_option maxRecDepth 1000000
set_option maxHeartbeats 15000000

open YMGap.Constructive
open YMGap.Continuum.BF4PhysicalCutoffEmbeddedEntryCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorFormPushforward
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCentering
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorHeadCorrectionCauchy
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledBaseEdgeFloor
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledDirichletEmbedding
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMass
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathMaximum
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathMaximum
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPoincareGap
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

private theorem maximum_poincare_left_identity
    (floor mass diagonal : Q') :
    floor * (mass * diagonal + mass * diagonal) ≈
      (mass + mass) * (floor * diagonal) := by
  q_ring

private theorem maximum_poincare_right_identity
    (mass scale diagonal matrix : Q') :
    (mass * mass) *
        (scale * ((diagonal + diagonal) + -(matrix + matrix))) ≈
      (mass + mass) *
        ((mass * scale) * (diagonal + -matrix)) := by
  q_ring

namespace FixedBasePulledPositiveEdgeFloor

/-! ## 1. Maximum-path mass-free Poincare inequality -/

theorem floor_mul_movingDiagonal_le_maximum_mul_deficit
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
      centralPhysicalFiniteVacuumSectorPathMaximum w hw base half *
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
  let scale := centralPhysicalFiniteVacuumSectorPathMaximum w hw base half
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
        scale * energy := by
    intro left hleft right hright
    exact
      FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_maximum_mul_pulledDirichlet
        certificate later hlater moving left right hleft hright
  have hbound : certificate.floor * pairwise ≤
      (mass * mass) * (scale * energy) :=
    floor_mul_finiteWeightedPairwiseVariance_le
      states weight moving certificate.floor scale energy
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
  have hscale0 : (0 : Q') ≤ scale :=
    Q'.le_of_lt
      (centralPhysicalFiniteVacuumSectorPathMaximum_pos
        w hw base half)
  have henergyScaled :
      (mass * mass) * (scale * energy) ≤
        (mass * mass) *
          (scale * ((diagonal + diagonal) + -(matrix + matrix))) := by
    apply Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ henergy hscale0)
    exact Q'.mul_nonneg _ _ hmass0 hmass0
  have hleft : certificate.floor * pairwise ≈
      (mass + mass) * (certificate.floor * diagonal) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left certificate.floor _ _ hpairwise)
      (maximum_poincare_left_identity
        certificate.floor mass diagonal)
  have hright :
      (mass * mass) *
          (scale * ((diagonal + diagonal) + -(matrix + matrix))) ≈
        (mass + mass) *
          ((mass * scale) * (diagonal + -matrix)) :=
    maximum_poincare_right_identity mass scale diagonal matrix
  have hscaled :
      (mass + mass) * (certificate.floor * diagonal) ≤
        (mass + mass) *
          ((mass * scale) * (diagonal + -matrix)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_trans' _ _ _ henergyScaled (Q'.le_of_eqv hright)))
  have hmassPoincare : certificate.floor * diagonal ≤
      (mass * scale) * (diagonal + -matrix) :=
    Q'.le_of_mul_le_mul_left hscaled
      (Q'.pos_add_nonneg
        (fixedBasePulledMass_pos w hw base later half) hmass0)
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
    (w := w) (hw := hw) base later half hbaseLater coefficient
  have hdeficit0 : (0 : Q') ≤ diagonal + -matrix :=
    Q'.sub_nonneg_of_le hmatrixDiagonal
  have hmassScale : mass * scale ≤ scale :=
    Q'.le_trans' _ ((1 : Q') * scale) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (fixedBasePulledMass_le_one base later half hbaseLater)
        hscale0)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hmassPoincare
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hmassScale hdeficit0)

/-! ## 2. The constructed maximum-scale datum -/

/-- The path maximum and persistent edge floor inhabit the reusable positive
Poincare-scale compiler on every fixed base carrier. -/
def maximumPoincareScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    FixedBasePulledPoincareScaleData certificate where
  scale := centralPhysicalFiniteVacuumSectorPathMaximum w hw base half
  scale_pos := centralPhysicalFiniteVacuumSectorPathMaximum_pos
    w hw base half
  floor_mul_diagonal_le_scale_mul_deficit :=
    floor_mul_movingDiagonal_le_maximum_mul_deficit certificate

/-- The sharper fixed-base rational rate. -/
def maximumPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Q' :=
  (maximumPoincareScaleData certificate).rate

theorem maximumPoincareRate_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    (0 : Q') ≤ maximumPoincareRate certificate :=
  (maximumPoincareScaleData certificate).rate_nonnegative

theorem maximumPoincareRate_lt_one
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    maximumPoincareRate certificate < (1 : Q') :=
  (maximumPoincareScaleData certificate).rate_lt_one

/-- The earlier sum ceiling, expressed through the same reusable compiler. -/
def ceilingPoincareScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    FixedBasePulledPoincareScaleData certificate where
  scale := centralPhysicalFiniteVacuumSectorPathCeiling w hw base half
  scale_pos := centralPhysicalFiniteVacuumSectorPathCeiling_pos
    w hw base half
  floor_mul_diagonal_le_scale_mul_deficit :=
    FixedBasePulledPositiveEdgeFloor.floor_mul_movingDiagonal_le_ceiling_mul_deficit
      certificate

theorem ceilingPoincareScaleData_rate_eq_uniformPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    (ceilingPoincareScaleData certificate).rate =
      FixedBasePulledPositiveEdgeFloor.uniformPoincareRate certificate :=
  rfl

/-- Replacing the sum ceiling by the finite maximum can only improve the
constructed fixed-base rate. -/
theorem maximumPoincareRate_le_uniformPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    maximumPoincareRate certificate ≤
      FixedBasePulledPositiveEdgeFloor.uniformPoincareRate certificate := by
  rw [← ceilingPoincareScaleData_rate_eq_uniformPoincareRate certificate]
  exact FixedBasePulledPoincareScaleData.rate_le_of_scale_le
    (maximumPoincareScaleData certificate)
    (ceilingPoincareScaleData certificate)
    (centralPhysicalFiniteVacuumSectorPathMaximum_le_ceiling
      w hw base half)

theorem moving_abs_gap_at_maximumPoincareRate
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
      maximumPoincareRate certificate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving :=
  (maximumPoincareScaleData certificate).moving_abs_gap
    later hlater coefficient

end FixedBasePulledPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap.FixedBasePulledPositiveEdgeFloor.floor_mul_movingDiagonal_le_maximum_mul_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap.FixedBasePulledPositiveEdgeFloor.maximumPoincareScaleData
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap.FixedBasePulledPositiveEdgeFloor.maximumPoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap.FixedBasePulledPositiveEdgeFloor.maximumPoincareRate_le_uniformPoincareRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap.FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_maximumPoincareRate
