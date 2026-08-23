/-
# Compile pulled endpoint control to a BF4 Poincare scale

All BF4 path methods ultimately supply the same input: one positive scale
which bounds every pairwise centered coefficient difference by the pulled
Dirichlet energy.  This module packages that input and performs the common
weighted-pairwise-variance and mass-cancellation argument once.

The result is the existing reusable positive Poincare-scale datum.  This is a
finite algebraic compiler and does not supply an all-base uniform scale or
edge floor, a completed gap, a thermodynamic/continuum limit, or a Clay
conclusion.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler

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
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
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

private theorem endpointScale_poincare_left_identity
    (floor mass diagonal : Q') :
    floor * (mass * diagonal + mass * diagonal) ≈
      (mass + mass) * (floor * diagonal) := by
  q_ring

private theorem endpointScale_poincare_right_identity
    (mass scale diagonal matrix : Q') :
    (mass * mass) *
        (scale * ((diagonal + diagonal) + -(matrix + matrix))) ≈
      (mass + mass) *
        ((mass * scale) * (diagonal + -matrix)) := by
  q_ring

structure FixedBasePulledEndpointScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Type 1 where
  scale : Q'
  scale_pos : (0 : Q') < scale
  endpoint_bound :
    ∀ later : Nat, certificate.start ≤ later →
    ∀ coefficient : Nat → Q',
    ∀ left, left ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half →
    ∀ right, right ∈
      centralPhysicalFiniteVacuumSectorIndices w hw base half →
      certificate.floor *
          ((coefficient left + -coefficient right) *
            (coefficient left + -coefficient right)) ≤
        scale *
          finiteJointDirichletEnergy
            (centralPhysicalFiniteVacuumSectorIndices w hw base half)
            coefficient
            (centralPhysicalFinitePulledKernel w hw base later half)

namespace FixedBasePulledEndpointScaleData

theorem floor_mul_movingDiagonal_le_scale_mul_deficit
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledEndpointScaleData certificate)
    (later : Nat) (hlater : certificate.start ≤ later)
    (coefficient : Nat → Q') :
    let moving :=
      centralPhysicalFinitePulledVacuumSectorHeadCenteredCoefficient
        w hw base later half coefficient
    certificate.floor *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving ≤
      data.scale *
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
        data.scale * energy := by
    intro left hleft right hright
    exact data.endpoint_bound later hlater moving
      left hleft right hright
  have hbound : certificate.floor * pairwise ≤
      (mass * mass) * (data.scale * energy) :=
    floor_mul_finiteWeightedPairwiseVariance_le
      states weight moving certificate.floor data.scale energy
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
  have hscale0 : (0 : Q') ≤ data.scale := Q'.le_of_lt data.scale_pos
  have henergyScaled :
      (mass * mass) * (data.scale * energy) ≤
        (mass * mass) *
          (data.scale *
            ((diagonal + diagonal) + -(matrix + matrix))) := by
    apply Q'.mul_le_mul_of_nonneg_left _ _ _
      (Q'.mul_le_mul_of_nonneg_left _ _ _ henergy hscale0)
    exact Q'.mul_nonneg _ _ hmass0 hmass0
  have hleft : certificate.floor * pairwise ≈
      (mass + mass) * (certificate.floor * diagonal) :=
    Q'.eqv_trans _ _ _
      (Q'.mul_eqv_congr_left certificate.floor _ _ hpairwise)
      (endpointScale_poincare_left_identity
        certificate.floor mass diagonal)
  have hright :
      (mass * mass) *
          (data.scale *
            ((diagonal + diagonal) + -(matrix + matrix))) ≈
        (mass + mass) *
          ((mass * data.scale) * (diagonal + -matrix)) :=
    endpointScale_poincare_right_identity
      mass data.scale diagonal matrix
  have hscaled :
      (mass + mass) * (certificate.floor * diagonal) ≤
        (mass + mass) *
          ((mass * data.scale) * (diagonal + -matrix)) :=
    Q'.le_trans' _ _ _ (Q'.ge_of_eqv hleft)
      (Q'.le_trans' _ _ _ hbound
        (Q'.le_trans' _ _ _ henergyScaled (Q'.le_of_eqv hright)))
  have hmassPoincare : certificate.floor * diagonal ≤
      (mass * data.scale) * (diagonal + -matrix) :=
    Q'.le_of_mul_le_mul_left hscaled
      (Q'.pos_add_nonneg
        (fixedBasePulledMass_pos w hw base later half) hmass0)
  have hmatrixDiagonal := fixedBasePulledMovingMatrix_le_diagonal
    (w := w) (hw := hw) base later half hbaseLater coefficient
  have hdeficit0 : (0 : Q') ≤ diagonal + -matrix :=
    Q'.sub_nonneg_of_le hmatrixDiagonal
  have hmassScale : mass * data.scale ≤ data.scale :=
    Q'.le_trans' _ ((1 : Q') * data.scale) _
      (Q'.mul_le_mul_of_nonneg_right _ _ _
        (fixedBasePulledMass_le_one base later half hbaseLater)
        hscale0)
      (Q'.le_of_eqv (Q'.one_mul_eqv _))
  exact Q'.le_trans' _ _ _ hmassPoincare
    (Q'.mul_le_mul_of_nonneg_right _ _ _ hmassScale hdeficit0)

def toPoincareScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    {certificate : FixedBasePulledPositiveEdgeFloor w hw base half}
    (data : FixedBasePulledEndpointScaleData certificate) :
    FixedBasePulledPoincareScaleData certificate where
  scale := data.scale
  scale_pos := data.scale_pos
  floor_mul_diagonal_le_scale_mul_deficit :=
    data.floor_mul_movingDiagonal_le_scale_mul_deficit

end FixedBasePulledEndpointScaleData

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler.FixedBasePulledEndpointScaleData.floor_mul_movingDiagonal_le_scale_mul_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledEndpointScaleCompiler.FixedBasePulledEndpointScaleData.toPoincareScaleData
