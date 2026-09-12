/-
# Uniform Poincare compiler for the inward-mate OS flow

This module discharges every algebraic step after the all-vector endpoint
coverage condition named in the preceding arbitrary-observable energy module.
If one positive rational floor, independent of the cutoff, controls every
centered physical norm by the selected inward-mate endpoint oscillation, then
the actual finite physical OS transfer obeys a single strict form rate at every
cutoff `K >= 1`.

The compiled rate is

  formScale / (formScale + coverage.floor),

where `formScale = 4 * (1 + globalInwardMateTransportCost)` up to rational
equivalence.  The rate is nonnegative and strictly below one.

No inhabitant of `GlobalInwardMateUniformEndpointCoverage` is asserted here.
Consequently this is a conditional compiler, not a proved finite-volume
spectral gap, completed gap, continuum limit, or Clay theorem.

No `Classical`, choice, `native_decide`, `sorry`, custom axiom,
noncomputable declaration, enlarged heartbeat budget, or trusted external
computation is used.
-/

import YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy

namespace YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler

set_option autoImplicit false

open YMGap.Constructive
open YMGap.Constructive.ExpNeg
open YMGap.Continuum.BF4PhysicalFiniteVacuumSectorDirichlet
open YMGap.Continuum.BF4PhysicalMarkovTransferLaws
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSObservableEnergy
open YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSParityFormGap
open YMGap.Continuum.BF4SU2FixedMagneticPhysicalMarkov
open YMGap.Continuum.BF4SU2FixedMagneticPositiveKernelConvergence
open YMGap.Continuum.BF4WeightedJointPerronPerturbation
open YMGap.Continuum.FiniteDeterministicKernelPushforward
open YMGap.Continuum.FiniteWeightedGramSOS
open YMGap.Continuum.SU2FiniteTrivalentPacketGraphFullSupportNorm
open YMGap.Continuum.SU2FundamentalPentagonFiniteGraph
open YMGap.Continuum.Z4FiniteCylinderQuadraticStability
open YMGap.Continuum.Z4HalfTimeReflectionNormalizedPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalGram
open YMGap.Continuum.Z4HalfTimeReflectionPhysicalReindex
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

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

/-! ## 1. Exact physical Dirichlet/transfer recoding -/

/-- The full half-state Dirichlet energy of any observable is twice its
physical identity-minus-transfer form. -/
theorem centralPhysicalFullDirichlet_eqv_twice_deficit
    (K : Nat) (coefficient : EdgeLabelling -> Q') :
    finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
        (centralNormalizedPhysicalReflectedKernel
          anchorCoupling (by decide) K 0) ≈
      (centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient coefficient +
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient coefficient) +
      -(centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            coefficient) +
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            coefficient)) := by
  let states := centralPositiveHalfStates anchorCoupling (by decide) K 0
  let weight := centralPhysicalRowMarginal anchorCoupling (by decide) K 0
  let joint := centralNormalizedPhysicalReflectedKernel
    anchorCoupling (by decide) K 0
  have hgeneric := finiteJointDirichletEnergy_eqv_twice_deficit
    states weight coefficient joint
    (fun state hstate => centralPhysicalJoint_row_eq_marginal hstate)
    (fun left hleft right hright =>
      centralNormalizedPhysicalReflectedKernel_symm
        ((mem_centralPositiveHalfStates_iff.mp hleft).1)
        ((mem_centralPositiveHalfStates_iff.mp hright).1))
  have hdiag := finiteWeightedSquare_physical_eqv_inner
    anchorCoupling (by decide) K 0 coefficient
  have hmatrix := centralPhysicalWeightedMarkovQuadratic_eq_joint
    anchorCoupling (by decide) K 0 coefficient
  refine Q'.eqv_trans _
    (finiteJointDirichletEnergy states coefficient joint) _ ?_ ?_
  · exact Q'.eqv_symm
      (centralPhysicalPositiveDirichlet_eqv_full
        anchorCoupling (by decide) K 0 coefficient)
  exact Q'.eqv_trans _ _ _ hgeneric
    (Q'.add_eqv_congr'
      (Q'.add_eqv_congr' hdiag hdiag)
      (Q'.neg_eqv_congr _ _
        (Q'.add_eqv_congr'
          (Q'.eqv_symm hmatrix) (Q'.eqv_symm hmatrix))))

def globalInwardMateObservableFormScale : Q' :=
  globalInwardMateObservablePathScale +
    globalInwardMateObservablePathScale

theorem globalInwardMateObservableFormScale_positive :
    (0 : Q') < globalInwardMateObservableFormScale := by
  unfold globalInwardMateObservableFormScale
  exact Q'.pos_add_nonneg globalInwardMateObservablePathScale_positive
    (Q'.le_of_lt globalInwardMateObservablePathScale_positive)

theorem centralPhysicalMarkovMatrix_le_norm
    (K : Nat) (coefficient : EdgeLabelling -> Q') :
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        coefficient
        (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
          coefficient) <=
      centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        coefficient coefficient := by
  exact Q'.le_trans' _ _ _
    (Q'.le_abs_self _)
    (centralPhysicalMarkovApply_abs_form_le_identity
      anchorCoupling (by decide) K 0 coefficient)

/-! ## 2. Coverage compiles to a cutoff-uniform Poincare inequality -/

namespace GlobalInwardMateUniformEndpointCoverage

theorem floor_mul_norm_le_formScale_mul_deficit
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q')
    (hcenter : CentralPhysicalMeanZero
      anchorCoupling (by decide) K 0 coefficient) :
    coverage.floor *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient coefficient <=
      globalInwardMateObservableFormScale *
        (centralPhysicalWeightedInner anchorCoupling (by decide) K 0
            coefficient coefficient +
          -(centralPhysicalWeightedInner anchorCoupling (by decide) K 0
            coefficient
            (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
              coefficient))) := by
  let diagonal := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    coefficient coefficient
  let matrix := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    coefficient
    (centralPhysicalMarkovApply anchorCoupling (by decide) K 0 coefficient)
  let energy := finiteJointDirichletEnergy (centralHalfStates K 0) coefficient
    (centralNormalizedPhysicalReflectedKernel
      anchorCoupling (by decide) K 0)
  have hflow := coverage.floor_mul_norm_le_scale_mul_Dirichlet
    K hK coefficient hcenter
  have henergy : energy ≈
      (diagonal + diagonal) + -(matrix + matrix) :=
    centralPhysicalFullDirichlet_eqv_twice_deficit K coefficient
  have hdoubleDeficit :
      (diagonal + diagonal) + -(matrix + matrix) ≈
        (diagonal + -matrix) + (diagonal + -matrix) := by
    refine Q'.eqv_trans _
      ((diagonal + diagonal) + (-matrix + -matrix)) _ ?_ ?_
    · exact Q'.add_eqv_congr_left _ _ _
        (Q'.neg_add_eqv matrix matrix)
    · exact Q'.add_swap_inner diagonal diagonal (-matrix) (-matrix)
  have hcollect : globalInwardMateObservablePathScale * energy ≈
      globalInwardMateObservableFormScale * (diagonal + -matrix) := by
    refine Q'.eqv_trans _
      (globalInwardMateObservablePathScale *
        ((diagonal + diagonal) + -(matrix + matrix))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ henergy
    refine Q'.eqv_trans _
      (globalInwardMateObservablePathScale *
        ((diagonal + -matrix) + (diagonal + -matrix))) _ ?_ ?_
    · exact Q'.mul_eqv_congr_left _ _ _ hdoubleDeficit
    refine Q'.eqv_trans _
      (globalInwardMateObservablePathScale * (diagonal + -matrix) +
        globalInwardMateObservablePathScale * (diagonal + -matrix)) _
      (Q'.mul_add_eqv _ _ _) ?_
    unfold globalInwardMateObservableFormScale
    exact Q'.eqv_symm
      (Q'.add_mul_eqv globalInwardMateObservablePathScale
        globalInwardMateObservablePathScale (diagonal + -matrix))
  exact Q'.le_trans' _ _ _ hflow (Q'.le_of_eqv hcollect)

def denominator
    (coverage : GlobalInwardMateUniformEndpointCoverage) : Q' :=
  globalInwardMateObservableFormScale + coverage.floor

theorem denominator_positive
    (coverage : GlobalInwardMateUniformEndpointCoverage) :
    (0 : Q') < denominator coverage := by
  unfold denominator
  exact Q'.pos_add_nonneg globalInwardMateObservableFormScale_positive
    (Q'.le_of_lt coverage.floor_positive)

def rate (coverage : GlobalInwardMateUniformEndpointCoverage) : Q' :=
  Q'.divPos globalInwardMateObservableFormScale (denominator coverage)
    (denominator_positive coverage)

theorem rate_nonnegative
    (coverage : GlobalInwardMateUniformEndpointCoverage) :
    (0 : Q') <= rate coverage := by
  exact Q'.le_of_lt
    (Q'.divPos_pos _ _ (denominator_positive coverage)
      globalInwardMateObservableFormScale_positive)

theorem rate_lt_one
    (coverage : GlobalInwardMateUniformEndpointCoverage) :
    rate coverage < (1 : Q') := by
  apply divPos_lt_one_of_lt_local
  exact lt_add_of_pos_right_local _ _ coverage.floor_positive

theorem denominator_mul_matrix_le_scale_mul_norm
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q')
    (hcenter : CentralPhysicalMeanZero
      anchorCoupling (by decide) K 0 coefficient) :
    denominator coverage *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            coefficient) <=
      globalInwardMateObservableFormScale *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient coefficient := by
  let diagonal := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    coefficient coefficient
  let matrix := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    coefficient
    (centralPhysicalMarkovApply anchorCoupling (by decide) K 0 coefficient)
  let scale := globalInwardMateObservableFormScale
  have hpoincare := floor_mul_norm_le_formScale_mul_deficit coverage
    K hK coefficient hcenter
  have hmatrixDiagonal := centralPhysicalMarkovMatrix_le_norm K coefficient
  have hfloorMatrix : coverage.floor * matrix <=
      coverage.floor * diagonal :=
    Q'.mul_le_mul_of_nonneg_left _ _ _ hmatrixDiagonal
      (Q'.le_of_lt coverage.floor_positive)
  have hfirst : (scale + coverage.floor) * matrix <=
      scale * matrix + coverage.floor * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.add_mul_eqv scale coverage.floor matrix))
      (Q'.add_le_add_left _ _ _ hfloorMatrix)
  have hadd := Q'.add_le_add_right
    (coverage.floor * diagonal)
    (scale * (diagonal + -matrix))
    (scale * matrix) hpoincare
  have hfinish : coverage.floor * diagonal + scale * matrix <=
      scale * diagonal :=
    Q'.le_trans' _ _ _ hadd
      (Q'.le_of_eqv (scale_deficit_cancel_local scale diagonal matrix))
  unfold denominator
  exact Q'.le_trans' _ _ _ hfirst
    (Q'.le_trans' _
      (coverage.floor * diagonal + scale * matrix) _
      (Q'.le_of_eqv (Q'.add_comm_eqv _ _)) hfinish)

/-- **Conditional uniform all-vector strict form bound.**  The rate does not
depend on `K` or on the centered coefficient. -/
theorem matrix_le_rate_mul_norm
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q')
    (hcenter : CentralPhysicalMeanZero
      anchorCoupling (by decide) K 0 coefficient) :
    centralPhysicalWeightedInner anchorCoupling (by decide) K 0
        coefficient
        (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
          coefficient) <=
      rate coverage *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient coefficient := by
  let diagonal := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    coefficient coefficient
  let matrix := centralPhysicalWeightedInner anchorCoupling (by decide) K 0
    coefficient
    (centralPhysicalMarkovApply anchorCoupling (by decide) K 0 coefficient)
  let scale := globalInwardMateObservableFormScale
  have hscaled := denominator_mul_matrix_le_scale_mul_norm coverage
    K hK coefficient hcenter
  have hcommuted : matrix * denominator coverage <= scale * diagonal :=
    Q'.le_trans' _ _ _
      (Q'.le_of_eqv (Q'.mul_comm_eqv matrix (denominator coverage))) hscaled
  have hdivision := Q'.le_divPos_of_mul_le
    (scale * diagonal) (denominator coverage)
    (denominator_positive coverage) hcommuted
  have hfactor : Q'.divPos (scale * diagonal) (denominator coverage)
        (denominator_positive coverage) ≈ rate coverage * diagonal := by
    unfold rate
    exact divPos_mul_right_eqv_local
      scale diagonal (denominator coverage) (denominator_positive coverage)
  exact Q'.le_trans' _ _ _ hdivision (Q'.le_of_eqv hfactor)

theorem abs_matrix_le_rate_mul_norm
    (coverage : GlobalInwardMateUniformEndpointCoverage)
    (K : Nat) (hK : 1 <= K)
    (coefficient : EdgeLabelling -> Q')
    (hcenter : CentralPhysicalMeanZero
      anchorCoupling (by decide) K 0 coefficient) :
    Q'.abs
        (centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient
          (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
            coefficient)) <=
      rate coverage *
        centralPhysicalWeightedInner anchorCoupling (by decide) K 0
          coefficient coefficient := by
  rw [abs_of_nonneg]
  · exact matrix_le_rate_mul_norm coverage K hK coefficient hcenter
  · exact centralPhysicalMarkovApply_positive
      anchorCoupling (by decide) K 0 coefficient

end GlobalInwardMateUniformEndpointCoverage

structure GlobalInwardMateUniformPoincareCertificate
    (coverage : GlobalInwardMateUniformEndpointCoverage) : Type where
  rate : Q'
  rate_eq : rate ≈ GlobalInwardMateUniformEndpointCoverage.rate coverage
  rate_nonnegative : (0 : Q') <= rate
  rate_lt_one : rate < (1 : Q')
  strict_form : forall (K : Nat) (_hK : 1 <= K)
      (coefficient : EdgeLabelling -> Q'),
    CentralPhysicalMeanZero anchorCoupling (by decide) K 0 coefficient ->
      Q'.abs
          (centralPhysicalWeightedInner anchorCoupling (by decide) K 0
            coefficient
            (centralPhysicalMarkovApply anchorCoupling (by decide) K 0
              coefficient)) <=
        rate * centralPhysicalWeightedInner
          anchorCoupling (by decide) K 0 coefficient coefficient

def globalInwardMateUniformPoincareCertificate
    (coverage : GlobalInwardMateUniformEndpointCoverage) :
    GlobalInwardMateUniformPoincareCertificate coverage :=
  { rate := GlobalInwardMateUniformEndpointCoverage.rate coverage
    rate_eq := Q'.eqv_refl _
    rate_nonnegative := GlobalInwardMateUniformEndpointCoverage.rate_nonnegative
      coverage
    rate_lt_one := GlobalInwardMateUniformEndpointCoverage.rate_lt_one coverage
    strict_form :=
      GlobalInwardMateUniformEndpointCoverage.abs_matrix_le_rate_mul_norm
        coverage }

#print axioms centralPhysicalFullDirichlet_eqv_twice_deficit
#print axioms globalInwardMateObservableFormScale_positive
#print axioms centralPhysicalMarkovMatrix_le_norm
#print axioms GlobalInwardMateUniformEndpointCoverage.floor_mul_norm_le_formScale_mul_deficit
#print axioms GlobalInwardMateUniformEndpointCoverage.rate_lt_one
#print axioms GlobalInwardMateUniformEndpointCoverage.abs_matrix_le_rate_mul_norm
#print axioms globalInwardMateUniformPoincareCertificate

end YMGap.Continuum.BF4PhysicalVacuumSectorInwardMateGlobalAllSourceOSUniformPoincareCompiler
