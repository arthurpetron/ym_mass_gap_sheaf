/-
# Zero and negation on the completed strict-cylinder OS carrier

This module continues the linearization of the same base-independent
strict-cylinder completion.  It constructs a canonical staged zero and proves
that rational scaling by `-1` is an isometry of the staged OS distance.
Consequently negation descends through Cauchy representatives and the
completion quotient.

The additive group laws and the general rational scalar action are subsequent
obligations; this file does not claim a completed vector space yet.
-/

import YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd

namespace YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg

set_option maxRecDepth 100000
set_option maxHeartbeats 5000000

open YMGap.Constructive
open YMGap.Continuum.CRealSeminormCompletion
open YMGap.Continuum.Z4CanonicalPolymerUniverse
open YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionAdd
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

/-! ## 1. Fixed-base negation is an OS isometry -/

/-- The difference of two negated presentations represents the negation of
their difference. -/
theorem strictJointCylinderDifference_neg_equivalent
    {base : Nat} (left right : StrictJointCylinderVector base) :
    StrictJointCylinderVectorEquivalent
      (strictJointCylinderDifference
        (left.smul (-1)) (right.smul (-1)))
      ((strictJointCylinderDifference left right).smul (-1)) := by
  intro radius support
  have houter := strictJointCylinderDifference_coefficient_code
    (left.smul (-1)) (right.smul (-1)) radius support
  have hdiff := strictJointCylinderDifference_coefficient_code
    left right radius support
  refine Q'.eqv_trans _ _ _ houter ?_
  change
    ((-1 : Q') * left.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base left.roots support)) +
      (-((-1 : Q') * right.coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base right.roots support))) ≈
    (-1 : Q') *
      (strictJointCylinderDifference left right).coefficient
        (Z4HalfTimeReflectionStrictJointMarkedCylinder.centralStrictLocalQueryCode
          radius base (strictJointCylinderDifference left right).roots support)
  refine Q'.eqv_trans _ _ _ ?_
    (Q'.mul_eqv_congr_left (-1) _ _ (Q'.eqv_symm hdiff))
  ring_qeqv

/-- Fixed-base negation preserves the strict squared OS distance. -/
theorem strictJointCylinderReflectionDistSq_neg_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    {base : Nat} (left right : StrictJointCylinderVector base) :
    CReal.Equiv
      (strictJointCylinderReflectionDistSq hcoupling hle
        (left.smul (-1)) (right.smul (-1)))
      (strictJointCylinderReflectionDistSq hcoupling hle left right) := by
  have hpresentation := StrictJointCylinderVector.reflectionQuadratic_equiv
    hcoupling hle (strictJointCylinderDifference_neg_equivalent left right)
  exact CReal.Equiv.trans hpresentation
    (reflectionQuadratic_smul_neg_one_equiv hcoupling hle
      (strictJointCylinderDifference left right))

/-! ## 2. Staged zero and negation -/

/-- The empty zero presentation at any fixed base. -/
def strictJointCylinderVectorZero (base : Nat) :
    StrictJointCylinderVector base where
  roots := []
  rootsCanonical := by
    intro root hroot
    cases hroot
  coefficient := fun _ => 0

/-- The empty zero presentation at base zero. -/
def strictJointCylinderStageZero : StrictJointCylinderStage where
  base := 0
  vector := strictJointCylinderVectorZero 0

/-- Negation stays in the same source base. -/
def strictJointCylinderStageNeg
    (stage : StrictJointCylinderStage) : StrictJointCylinderStage :=
  ⟨stage.base, stage.vector.smul (-1)⟩

private theorem boxTransportStrictJointCylinderVector_smul_of_le
    {base outer : Nat} (hbase : base <= outer)
    (scalar : Q') (vector : StrictJointCylinderVector base) :
    boxTransportStrictJointCylinderVector hbase (vector.smul scalar) =
      (boxTransportStrictJointCylinderVector hbase vector).smul scalar := by
  obtain ⟨padding, rfl⟩ := Nat.exists_eq_add_of_le hbase
  exact boxTransportStrictJointCylinderVector_smul padding scalar vector

/-- Negation is an isometry of the base-independent staged distance. -/
theorem strictJointCylinderStage_neg_equiv
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling)
    (left right : StrictJointCylinderStage) :
    CReal.Equiv
      (strictJointCylinderStageReflectionDistSq hcoupling hle
        (strictJointCylinderStageNeg left)
        (strictJointCylinderStageNeg right))
      (strictJointCylinderStageReflectionDistSq hcoupling hle left right) := by
  let outer := max left.base right.base
  have hleft : left.base <= outer := Nat.le_max_left _ _
  have hright : right.base <= outer := Nat.le_max_right _ _
  have hneg := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle (strictJointCylinderStageNeg left)
      (strictJointCylinderStageNeg right) hleft hright
  have horiginal := strictJointCylinderStageReflectionDistSq_at_common
    hcoupling hle left right hleft hright
  have hfixed := strictJointCylinderReflectionDistSq_neg_equiv hcoupling hle
    (boxTransportStrictJointCylinderVector hleft left.vector)
    (boxTransportStrictJointCylinderVector hright right.vector)
  rw [← boxTransportStrictJointCylinderVector_smul_of_le hleft,
    ← boxTransportStrictJointCylinderVector_smul_of_le hright] at hfixed
  exact CReal.Equiv.trans (CReal.Equiv.symm hneg)
    (CReal.Equiv.trans hfixed horiginal)

def strictJointCylinderStageNegNonexpansive
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    (strictJointCylinderStageSquaredSeminorm hcoupling hle).Nonexpansive where
  toFun := strictJointCylinderStageNeg
  contraction := fun left right =>
    CReal.leEv_of_equiv
      (strictJointCylinderStage_neg_equiv hcoupling hle left right)

/-! ## 3. Completed zero and negation -/

/-- The zero point in the completed strict OS carrier. -/
def strictJointCylinderCompletedZero
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointCylinderOSCompletion hcoupling hle :=
  (strictJointCylinderStageSquaredSeminorm hcoupling hle).embedRep
    strictJointCylinderStageZero

/-- Negation on the completed strict OS carrier. -/
def strictJointCylinderCompletedNeg
    {coupling : Q'} (hcoupling : (0 : Q') <= coupling)
    (hle : coupling <= anchorCoupling) :
    StrictJointCylinderOSCompletion hcoupling hle ->
      StrictJointCylinderOSCompletion hcoupling hle :=
  (strictJointCylinderStageNegNonexpansive hcoupling hle).completionMap

#print axioms strictJointCylinderDifference_neg_equivalent
#print axioms strictJointCylinderReflectionDistSq_neg_equiv
#print axioms strictJointCylinderVectorZero
#print axioms strictJointCylinderStageZero
#print axioms strictJointCylinderStage_neg_equiv
#print axioms strictJointCylinderStageNegNonexpansive
#print axioms strictJointCylinderCompletedZero
#print axioms strictJointCylinderCompletedNeg

end YMGap.Continuum.Z4HalfTimeReflectionStrictJointCRealCompletionZeroNeg
