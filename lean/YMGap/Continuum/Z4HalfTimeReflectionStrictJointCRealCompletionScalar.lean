/-
# Rational scaling on the completed strict-cylinder OS carrier

For a rational scalar `s`, the strict OS squared distance scales by `s^2`.
The explicit input tolerance

`epsilon * invSucc ((s^2).num.toNat)`

therefore makes staged scaling uniformly continuous with Type-level data.
The generic modulus-continuous completion map descends rational scaling to the
same base-independent completed carrier.

Scalar algebra laws and homogeneity of completed time translation are proved
in the following layer.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveTimeTranslation
import YMGap.Constructive.CRealInnerRegularity
import YMGap.Continuum.RCScaleClose

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdditiveTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealDirectLimitSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealRadicalDescent
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBaseTransportBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderBilinearTimeTranslation
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderDirectLimit
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCylinderSeminorm
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointDoubledTimeMixedOSBilinear
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointOSDistanceContraction
open YMGap.Continuum.Z4StrongCouplingParametricAnchor

local infix:50 " ≈ " => Q'.eqv

private theorem neg_num_cast_local (a : Q') : (-a).num = -(a.num) := rfl

local macro "ring_qeqv" : tactic =>
  `(tactic| (show _ * (_ : Int) = _ * (_ : Int);
             simp only [Q'.add_num_cast, Q'.add_den_cast, Q'.mul_num_cast,
               Q'.mul_den_cast, Q'.neg_den, neg_num_cast_local,
               Q'.mkPos_num, Q'.mkPos_den,
               Int.add_mul, Int.mul_add, Int.neg_mul, Int.mul_neg,
               Int.neg_add, Int.neg_neg, Int.one_mul, Int.mul_one,
               Int.zero_mul, Int.mul_zero, Int.zero_add, Int.add_zero]; ac_rfl))

private theorem creal_mul_congr_right
    {scalar left right : CReal} (h : CReal.Equiv left right) :
    CReal.Equiv (CReal.mul scalar left) (CReal.mul scalar right) :=
  CReal.Equiv.trans (CRealAlg.cmul_comm scalar left)
    (CReal.Equiv.trans (CReal.mul_congr_left h)
      (CRealAlg.cmul_comm right scalar))

/-! ## 1. Fixed-base quadratic scaling -/

/-- The reflection quadratic is exactly homogeneous of degree two. -/
theorem reflectionQuadratic_smul_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (scalar : Q') (vector : StrictJointCylinderVector base) :
    CReal.Equiv
      ((vector.smul scalar).reflectionQuadratic hcoupling hle)
      (CReal.mul (CReal.ofQ' (scalar * scalar))
        (vector.reflectionQuadratic hcoupling hle)) := by
  let scaled := vector.smul scalar
  let diagonal := strictJointCylinderReflectionBilinear
    hcoupling hle vector vector
  let scalarReal := CReal.ofQ' scalar
  have hselfScaled := strictJointCylinderReflectionBilinear_self
    hcoupling hle scaled
  have hleft := strictJointCylinderReflectionBilinear_smul_left
    hcoupling hle scalar vector scaled
  have hright := strictJointCylinderReflectionBilinear_smul_right
    hcoupling hle scalar vector vector
  have hself := strictJointCylinderReflectionBilinear_self
    hcoupling hle vector
  have hfactor : CReal.Equiv
      (CReal.mul scalarReal scalarReal)
      (CReal.ofQ' (scalar * scalar)) :=
    CReal.Equiv.symm (CRealAlg.ofQ'_mul scalar scalar)
  exact CReal.Equiv.trans (CReal.Equiv.symm hselfScaled)
    (CReal.Equiv.trans hleft
      (CReal.Equiv.trans (creal_mul_congr_right hright)
        (CReal.Equiv.trans
          (CReal.Equiv.symm (CRealAlg.cmul_assoc scalarReal scalarReal diagonal))
          (CReal.Equiv.trans
            (CReal.mul_congr_left hfactor)
            (creal_mul_congr_right hself)))))

/-- Scaling both endpoints scales their presentation difference. -/
theorem strictJointCylinderDifference_smul_equivalent
    {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference
        (left.smul scalar) (right.smul scalar))
      ((strictJointCylinderDifference left right).smul scalar) := by
  intro radius support
  have houter := strictJointCylinderDifference_coefficient_code
    (left.smul scalar) (right.smul scalar) radius support
  have hdiff := strictJointCylinderDifference_coefficient_code
    left right radius support
  refine Q'.eqv_trans _ _ _ houter ?_
  change
    scalar * left.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base left.roots support) +
      (-(scalar * right.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base right.roots support))) ≈
    scalar *
      (strictJointCylinderDifference left right).coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base (strictJointCylinderDifference left right).roots support)
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.mul_eqv_congr_left scalar _ _ (Q'.eqv_symm hdiff))
  ring_qeqv

/-- Fixed-base squared distance scales by the nonnegative factor `s^2`. -/
theorem strictJointCylinderReflectionDistSq_smul_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (scalar : Q')
    (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle
        (left.smul scalar) (right.smul scalar))
      (CReal.mul (CReal.ofQ' (scalar * scalar))
        (strictJointCylinderReflectionDistSq hcoupling hle left right)) := by
  have hpresentation := StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle
    (strictJointCylinderDifference_smul_equivalent scalar left right)
  exact CReal.Equiv.trans hpresentation
    (reflectionQuadratic_smul_equiv hcoupling hle scalar
      (strictJointCylinderDifference left right))

/-! ## 2. Staged scaling and its explicit continuity modulus -/

def strictJointCylinderStageSmul
    (scalar : Q') (stage : StrictJointCylinderStage) :
    StrictJointCylinderStage :=
  ⟨stage.base, stage.vector.smul scalar⟩

private theorem boxTransportStrictJointCylinderVector_smul_of_le
    {base outer : Nat} (hbase : base <= outer)
    (scalar : Q') (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector hbase (vector.smul scalar) =
      (boxTransportStrictJointCylinderVector hbase vector).smul scalar := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  exact boxTransportStrictJointCylinderVector_smul padding scalar vector

theorem strictJointCylinderStageReflectionDistSq_smul_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (scalar : Q') (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageSmul scalar left)
        (strictJointCylinderStageSmul scalar right))
      (CReal.mul (CReal.ofQ' (scalar * scalar))
        (strictJointCylinderStageReflectionDistSq hcoupling hle left right)) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hscaled := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle (strictJointCylinderStageSmul scalar left)
      (strictJointCylinderStageSmul scalar right) hleft hright
  have horiginal := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left right hleft hright
  have hfixed := strictJointCylinderReflectionDistSq_smul_equiv
    hcoupling hle scalar
    (boxTransportStrictJointCylinderVector hleft left.vector)
    (boxTransportStrictJointCylinderVector hright right.vector)
  rw [← boxTransportStrictJointCylinderVector_smul_of_le hleft,
    ← boxTransportStrictJointCylinderVector_smul_of_le hright] at hfixed
  exact CReal.Equiv.trans (CReal.Equiv.symm hscaled)
    (CReal.Equiv.trans hfixed (creal_mul_congr_right horiginal))

/-- Rational scaling with its computable squared-distance input tolerance. -/
def strictJointCylinderStageSmulContinuous
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) (scalar : Q') :
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).ModulusContinuous where
  toFun := strictJointCylinderStageSmul scalar
  tolerance := CReal.InnerRegularity.scaleTolerance (scalar * scalar)
  tolerance_pos := fun epsilon hepsilon =>
    CReal.InnerRegularity.scaleTolerance_pos
      (scalar * scalar) epsilon hepsilon
  contraction := by
    intro epsilon hepsilon left right hdist
    have hsq : (0 : Q') <= scalar * scalar :=
      SumOfSquares.q_mul_self_nonneg scalar
    have hscaled := CReal.leEv_smul_nonneg hsq hdist
    have hconstant : CReal.leEv
        (CReal.mul (CReal.ofQ' (scalar * scalar))
          (CReal.ofQ'
            (CReal.InnerRegularity.scaleTolerance
              (scalar * scalar) epsilon)))
        (CReal.ofQ' epsilon) := by
      have hproduct := CReal.InnerRegularity.mul_scaleTolerance_le
        (scalar * scalar) epsilon hsq hepsilon
      exact CReal.leEv_trans
        (CReal.leEv_of_equiv
          (CReal.Equiv.symm (CRealAlg.ofQ'_mul (scalar * scalar)
            (CReal.InnerRegularity.scaleTolerance
              (scalar * scalar) epsilon))))
        (CReal.leEv_of_le (CReal.ofQ'_le_ofQ' hproduct))
    exact CReal.leEv_trans
      (CReal.leEv_of_equiv
        (strictJointCylinderStageReflectionDistSq_smul_equiv
          hcoupling hle scalar left right))
      (CReal.leEv_trans hscaled hconstant)

/-! ## 3. Rational scaling on the completed carrier -/

def strictJointCylinderCompletedSmul
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) (scalar : Q') :
    StrictJointCylinderOSCompletion hcoupling hle ->
      StrictJointCylinderOSCompletion hcoupling hle :=
  (strictJointCylinderStageSmulContinuous hcoupling hle scalar).completionMap

#print axioms reflectionQuadratic_smul_equiv
#print axioms strictJointCylinderDifference_smul_equivalent
#print axioms strictJointCylinderReflectionDistSq_smul_equiv
#print axioms strictJointCylinderStageReflectionDistSq_smul_equiv
#print axioms strictJointCylinderStageSmulContinuous
#print axioms strictJointCylinderCompletedSmul

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionScalar
