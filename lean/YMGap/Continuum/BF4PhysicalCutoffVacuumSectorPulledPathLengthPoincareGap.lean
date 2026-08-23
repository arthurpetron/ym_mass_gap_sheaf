/-
# Quadratic path-length Poincare rate on each pulled BF4 carrier

The finite Cauchy--Schwarz path compiler replaces the old recursively doubled
path scale by the square of the canonical path length.  Taking its finite
maximum and combining it with the persistent pulled edge floor gives a new
strict rational Poincare rate on every fixed base carrier.

The new scale and rate are no larger than the former maximum-amplification
scale and rate.  They may still vary with the expanding base carrier.  No
all-base common rate, unconditional completed gap, thermodynamic/continuum
limit, or Clay conclusion is asserted.

No `Classical.*`, choice, `native_decide`, `sorry`, custom axiom, or
noncomputable declaration is used.
-/

import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthMaximum
import YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap

namespace YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap

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
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledMaximumPoincareGap
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthMaximum
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPoincareScale
open YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledUniformPoincareGap
open YMGap.Continuum.BF4PhysicalFiniteVacuumSector
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPairwiseVariance
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathCeiling
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorPathLengthMaximum
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

private theorem pathLength_poincare_left_identity
    (floor mass diagonal : Q') :
    floor * (mass * diagonal + mass * diagonal) ≈
      (mass + mass) * (floor * diagonal) := by
  q_ring

private theorem pathLength_poincare_right_identity
    (mass scale diagonal matrix : Q') :
    (mass * mass) *
        (scale * ((diagonal + diagonal) + -(matrix + matrix))) ≈
      (mass + mass) *
        ((mass * scale) * (diagonal + -matrix)) := by
  q_ring

namespace FixedBasePulledPositiveEdgeFloor

/-! ## 1. Quadratic-length mass-free Poincare inequality -/

theorem floor_mul_movingDiagonal_le_pathLengthMaximum_mul_deficit
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
      centralPhysicalFiniteVacuumSectorPathLengthMaximum w hw base half *
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
  let scale :=
    centralPhysicalFiniteVacuumSectorPathLengthMaximum w hw base half
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
      BF4PhysicalCutoffVacuumSectorPulledPathLengthMaximum.FixedBasePulledPositiveEdgeFloor.floor_mul_endpoint_sq_le_pathLengthMaximum_mul_pulledDirichlet
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
      (centralPhysicalFiniteVacuumSectorPathLengthMaximum_pos
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
      (pathLength_poincare_left_identity
        certificate.floor mass diagonal)
  have hright :
      (mass * mass) *
          (scale * ((diagonal + diagonal) + -(matrix + matrix))) ≈
        (mass + mass) *
          ((mass * scale) * (diagonal + -matrix)) :=
    pathLength_poincare_right_identity mass scale diagonal matrix
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

/-! ## 2. Constructed scale, rate, and comparison -/

def pathLengthPoincareScaleData
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    FixedBasePulledPoincareScaleData certificate where
  scale := centralPhysicalFiniteVacuumSectorPathLengthMaximum w hw base half
  scale_pos := centralPhysicalFiniteVacuumSectorPathLengthMaximum_pos
    w hw base half
  floor_mul_diagonal_le_scale_mul_deficit :=
    floor_mul_movingDiagonal_le_pathLengthMaximum_mul_deficit certificate

def pathLengthPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) : Q' :=
  (pathLengthPoincareScaleData certificate).rate

theorem pathLengthPoincareRate_nonnegative
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    (0 : Q') ≤ pathLengthPoincareRate certificate :=
  (pathLengthPoincareScaleData certificate).rate_nonnegative

theorem pathLengthPoincareRate_lt_one
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    pathLengthPoincareRate certificate < (1 : Q') :=
  (pathLengthPoincareScaleData certificate).rate_lt_one

/-- Polynomial path accounting can only improve the former maximum-path
fixed-base rate. -/
theorem pathLengthPoincareRate_le_maximumPoincareRate
    {w : Q'} {hw : (0 : Q') ≤ w} {base half : Nat}
    (certificate : FixedBasePulledPositiveEdgeFloor w hw base half) :
    pathLengthPoincareRate certificate ≤
      FixedBasePulledPositiveEdgeFloor.maximumPoincareRate certificate := by
  exact FixedBasePulledPoincareScaleData.rate_le_of_scale_le
    (pathLengthPoincareScaleData certificate)
    (FixedBasePulledPositiveEdgeFloor.maximumPoincareScaleData certificate)
    (centralPhysicalFiniteVacuumSectorPathLengthMaximum_le_pathMaximum
      w hw base half)

theorem moving_abs_gap_at_pathLengthPoincareRate
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
      pathLengthPoincareRate certificate *
        centralPhysicalFinitePulledVacuumSectorDiagonalQuadratic
          w hw base later half moving :=
  (pathLengthPoincareScaleData certificate).moving_abs_gap
    later hlater coefficient

end FixedBasePulledPositiveEdgeFloor

end YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap

/-! ## Axiom audit -/

#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap.FixedBasePulledPositiveEdgeFloor.floor_mul_movingDiagonal_le_pathLengthMaximum_mul_deficit
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap.FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate_lt_one
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap.FixedBasePulledPositiveEdgeFloor.pathLengthPoincareRate_le_maximumPoincareRate
#print axioms
  YMGap.Continuum.BF4PhysicalCutoffVacuumSectorPulledPathLengthPoincareGap.FixedBasePulledPositiveEdgeFloor.moving_abs_gap_at_pathLengthPoincareRate
